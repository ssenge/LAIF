"""Static per-episode distractor for TwoRoom: a smooth colour pattern added to every frame of an episode.

The pattern is amp * sum_k c_{ck} B_k / sqrt(n) with n = 6 fixed cosine patterns B_k (the same for every episode) and
coefficients c_{ck} per channel, drawn once per episode from the uniform law with unit variance, so an episode carries
3 n = 18 static factors. It is added after the normalization of the images (ImageNet statistics, so amp is in units
of about one standard deviation of a pixel). Training episodes are seeded by their dataset index, evaluation episodes
by 10^6 plus their position in the evaluation batch, so the two sets of patterns are disjoint draws of the same law.
Switched on by the environment variable B2_DISTRACT=<amp>.
"""
import math
import os

import numpy as np
import torch

N_PAT = 6
AMP = float(os.environ.get("B2_DISTRACT", "0") or 0)
_BASIS = {}


def basis(h, w):
    if (h, w) not in _BASIS:
        r = np.random.default_rng(1234)
        yy, xx = np.mgrid[0:h, 0:w] / max(h - 1, 1)
        _BASIS[(h, w)] = torch.tensor(np.stack([
            np.cos(2 * np.pi * (fx * xx + fy * yy) + ph)
            for fx, fy, ph in zip(r.uniform(0.3, 1.5, N_PAT), r.uniform(0.3, 1.5, N_PAT), r.uniform(0, 6.28, N_PAT))
        ]), dtype=torch.float32)
    return _BASIS[(h, w)]


def pattern(seed, c, h, w):
    coef = torch.tensor(np.random.default_rng(int(seed)).uniform(-math.sqrt(3), math.sqrt(3), (c, N_PAT)), dtype=torch.float32)
    return AMP * torch.einsum("ck,khw->chw", coef, basis(h, w)) / math.sqrt(N_PAT)


class AddDistractor:
    """Training transform on a sample dict: pixels (T, C, H, W) of one window, ep_idx (T,) raw episode index."""

    def __call__(self, sample):
        px = sample["pixels"]
        sample["pixels"] = px + pattern(int(np.asarray(sample["ep_idx"]).reshape(-1)[0]), *px.shape[-3:]).to(px)
        return sample


class Identity:
    def __call__(self, sample):
        return sample


def patch_train(train_module):
    """Append the distractor to the LeWM image preprocessor (needs ep_idx in data.dataset.keys_to_load); ep_idx gets no
    z-score normalizer."""
    orig = train_module.get_img_preprocessor
    orig_norm = train_module.get_column_normalizer
    train_module.get_column_normalizer = lambda ds, src, tgt: Identity() if src == "ep_idx" else orig_norm(ds, src, tgt)

    def pre(*args, **kwargs):
        from stable_pretraining import data as dt
        return dt.transforms.Compose(orig(*args, **kwargs), AddDistractor())

    train_module.get_img_preprocessor = pre


def patch_eval():
    """Add the pattern of env e to its observations and goal after the policy's image transform."""
    import stable_worldmodel as swm
    base = swm.policy.BasePolicy
    orig = base._prepare_info

    def prep(self, info_dict):
        out = orig(self, info_dict)
        for k in ("pixels", "goal"):
            v = out.get(k)
            if v is None:
                continue
            assert torch.is_tensor(v) and v.ndim == 5, (k, type(v), getattr(v, "shape", None))   # (E, T, C, H, W)
            if not getattr(prep, "shown", False):
                print(f"distractor added in eval: {k} {tuple(v.shape)}", flush=True)
            pats = torch.stack([pattern(10**6 + e, *v.shape[-3:]) for e in range(v.shape[0])]).to(v)
            out[k] = v + pats[:, None]
        prep.shown = True
        return out

    base._prepare_info = prep
