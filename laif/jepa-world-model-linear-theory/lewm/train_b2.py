"""LeWM training with two optional extra terms; the LeWM code (a clone at $LEWM_DIR) is imported and left unchanged.

Hydra overrides (besides the usual LeWM ones):
  +b2.lam_inv=<w>  inverse dynamics: an MLP reads the action block a_t from (z_t, z_{t+1}), squared error, weight w
  +b2.mu=<m>       minus m * T, T = sum_{h=1..T-1} tr(C_h^T (Cov(z) + lam I)^{-1} C_h), C_h = Cov(z_{t+h}, a_t) pooled over the
                   batch, lam = mean latent variance (ridge whitening: with D = 192 latents and a few hundred frames per batch,
                   full whitening fits chance correlations); at Cov(z) = I this is half the term of Theorem 4
The small matrix algebra of T runs in float32 on the CPU (gradients flow back to the device).
"""
import os
import sys

LEWM = os.environ.get("LEWM_DIR", os.path.join(os.path.dirname(os.path.abspath(__file__)), "le-wm"))  # a clone of the LeWM code
sys.path.insert(0, os.path.normpath(LEWM))

import torch  # noqa: E402
from torch import nn  # noqa: E402

import distract  # noqa: E402
import jepa  # noqa: E402
import train  # noqa: E402

if distract.AMP:
    distract.patch_train(train)

_init = jepa.JEPA.__init__


def _init_b2(self, encoder, predictor, action_encoder, projector=None, pred_proj=None):
    _init(self, encoder, predictor, action_encoder, projector, pred_proj)
    d, a = action_encoder.embed[-1].out_features, action_encoder.patch_embed.in_channels
    self.inv_head = nn.Sequential(nn.Linear(2 * d, 512), nn.SiLU(), nn.Linear(512, a))


jepa.JEPA.__init__ = _init_b2
_forward = train.lejepa_forward


def act_cov(emb, act, ridge=1.0):
    """emb (B, T, D), act (B, T, A) -> sum over h of tr(C_h^T (Sz + ridge * mean variance * I)^{-1} C_h)."""
    z = emb.float().cpu(); a = act.float().cpu()
    zf = z.reshape(-1, z.shape[-1]); zf = zf - zf.mean(0)
    Sz = zf.T @ zf / zf.shape[0]
    Sz = Sz + ridge * Sz.diagonal().mean().detach() * torch.eye(z.shape[-1])
    tot = z.new_zeros(())
    for h in range(1, z.shape[1]):
        zh = z[:, h:].reshape(-1, z.shape[-1]); ah = a[:, : a.shape[1] - h].reshape(-1, a.shape[-1])
        zh = zh - zh.mean(0); ah = ah - ah.mean(0)
        C = zh.T @ ah / zh.shape[0]
        tot = tot + (C * torch.linalg.solve(Sz, C)).sum()
    return tot.to(emb.device)


def b2_forward(self, batch, stage, cfg):
    out = _forward(self, batch, stage, cfg)          # LeWM losses; batch["action"] is NaN-free afterwards
    b2 = cfg.get("b2") or {}
    lam_inv, mu = float(b2.get("lam_inv", 0.0)), float(b2.get("mu", 0.0))
    emb, act = out["emb"], batch["action"]
    logs = {}
    if lam_inv > 0:
        pa = self.model.inv_head(torch.cat([emb[:, :-1], emb[:, 1:]], -1))
        out["inv_loss"] = (pa.float() - act[:, :-1].float()).pow(2).mean()
        out["loss"] = out["loss"] + lam_inv * out["inv_loss"]; logs["inv_loss"] = out["inv_loss"]
    if mu > 0 or not self.training:
        out["actcov"] = act_cov(emb, act)
        if mu > 0:
            out["loss"] = out["loss"] - mu * out["actcov"]
        logs["actcov"] = out["actcov"]
    if self.training and self.global_step % 50 == 0:
        lr = self.optimizers().param_groups[0]["lr"]
        print(f"b2 step {self.global_step} lr {lr:.3g} pred {out['pred_loss'].item():.4f} "
              + " ".join(f"{k} {v.item():.4f}" for k, v in logs.items()), flush=True)
    if logs:
        self.log_dict({f"{stage}/{k}": v.detach() for k, v in logs.items()}, on_step=True, sync_dist=True)
    return out


train.lejepa_forward = b2_forward

if __name__ == "__main__":
    sys.argv[0] = os.path.join(os.path.normpath(LEWM), "train.py")
    train.run()
