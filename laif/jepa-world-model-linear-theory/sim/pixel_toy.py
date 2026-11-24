"""Pixel test of the action-covariance term on a small LeWM-type world model (CPU).

World: 32x32 images. A bright blob (the agent) at p in [0,1]^2 moves by p' = clip(p + step (a + sigma e)), a, e ~ N(0, I_2)
(actuator noise). The background is a sum of n_bg fixed smooth patterns with coefficients drawn once per episode
(static content). Model: CNN encoder to K latents, MLP predictor of z' from (z, a), SIGReg on the latents.
Variants: 'lewm' (prediction + SIGReg), 'inv' (+ lam_inv * inverse dynamics, an MLP reading a from (z, z')),
'cov' (- mu * sum_{h=1..H} ||Cov(z_{t+h}, a_t)||_F^2 over the batch), 'covn' (unsquared norms), 'invcov' (inv + cov),
'sup' (reference: supervised position readout).
Reported: linear-probe R^2 of the agent position and of the background coefficients from z, the action response
(variance over actions of the predicted next latent, summed over dimensions), and goal-reaching success by random-shooting
model-predictive control with the latent distance to the goal image as cost.
"""
import argparse, json, math, time
import numpy as np
import torch, torch.nn as nn, torch.nn.functional as F

p = argparse.ArgumentParser()
p.add_argument("--variant", default="lewm"); p.add_argument("--seed", type=int, default=0)
p.add_argument("--K", type=int, default=4); p.add_argument("--n_bg", type=int, default=6)
p.add_argument("--steps", type=int, default=3000); p.add_argument("--batch", type=int, default=64)
p.add_argument("--T", type=int, default=6); p.add_argument("--H", type=int, default=3)
p.add_argument("--sigma", type=float, default=0.5); p.add_argument("--step", type=float, default=0.08)
p.add_argument("--lam_sig", type=float, default=0.1); p.add_argument("--lam_inv", type=float, default=1.0)
p.add_argument("--mu", type=float, default=1.0); p.add_argument("--bg_amp", type=float, default=0.5)
p.add_argument("--bg_dist", default="uniform")   # uniform: unit-variance uniform coefficients, so a background coefficient is not exactly normal
p.add_argument("--white", type=int, default=0)
p.add_argument("--episodes", type=int, default=100); p.add_argument("--out", default="")
args = p.parse_args()
torch.manual_seed(args.seed); rng = np.random.default_rng(args.seed); torch.set_num_threads(2)
S = 32
yy, xx = np.mgrid[0:S, 0:S] / (S - 1)
prng = np.random.default_rng(1234)                      # the patterns are the same for every seed
PAT = np.stack([np.cos(2 * np.pi * (fx * xx + fy * yy) + ph) for fx, fy, ph in
                zip(prng.uniform(0.3, 1.5, args.n_bg), prng.uniform(0.3, 1.5, args.n_bg), prng.uniform(0, 6.28, args.n_bg))])


def render(pos, coef):
    """pos (..., 2), coef (..., n_bg) -> images (..., 1, S, S)."""
    blob = np.exp(-(((xx - pos[..., 0, None, None]) ** 2 + (yy - pos[..., 1, None, None]) ** 2) / (2 * 0.05**2)))
    bg = args.bg_amp * np.tensordot(coef, PAT, axes=([-1], [0])) / math.sqrt(args.n_bg)
    return torch.tensor((blob + bg)[..., None, :, :], dtype=torch.float32)


def rollout(B, T, pos0=None, actions=None):
    pos = np.empty((B, T + 1, 2)); pos[:, 0] = rng.uniform(0, 1, (B, 2)) if pos0 is None else pos0
    a = rng.standard_normal((B, T, 2)) if actions is None else actions
    for t in range(T):
        pos[:, t + 1] = np.clip(pos[:, t] + args.step * (a[:, t] + args.sigma * rng.standard_normal((B, 2))), 0, 1)
    return pos, a


def bgc(shape):
    return rng.uniform(-math.sqrt(3), math.sqrt(3), shape) if args.bg_dist == "uniform" else rng.standard_normal(shape)


class Enc(nn.Module):
    def __init__(s):
        super().__init__()
        s.c = nn.Sequential(nn.Conv2d(1, 16, 3, 2, 1), nn.ReLU(), nn.Conv2d(16, 32, 3, 2, 1), nn.ReLU(),
                            nn.Conv2d(32, 64, 3, 2, 1), nn.ReLU(), nn.Flatten(), nn.Linear(64 * 16, 128), nn.ReLU(),
                            nn.Linear(128, args.K))
    def forward(s, x): return s.c(x)


mlp = lambda i, o: nn.Sequential(nn.Linear(i, 128), nn.ReLU(), nn.Linear(128, 128), nn.ReLU(), nn.Linear(128, o))
enc, pred, inv = Enc(), mlp(args.K + 2, args.K), mlp(2 * args.K, 2); head = nn.Linear(args.K, 2)
opt = torch.optim.Adam([*enc.parameters(), *pred.parameters(), *inv.parameters(), *head.parameters()], lr=1e-3)
KN = torch.linspace(0, 3, 17); DT = 3 / 16; W = torch.full((17,), 2 * DT); W[[0, -1]] = DT
PHI = torch.exp(-KN.square() / 2); W = W * PHI


def sigreg(z):
    A = torch.randn(z.shape[-1], 64); A = A / A.norm(dim=0)
    xt = (z @ A).unsqueeze(-1) * KN
    err = (xt.cos().mean(0) - PHI).square() + xt.sin().mean(0).square()
    return ((err @ W) * z.shape[0]).mean()


def act_cov(z, a, sq=True):
    """z (B, T+1, K), a (B, T, 2): sum over h of ||Cov(z_{t+h}, a_t)||_F^2 (or ||.||_F if not sq), pooled over the batch and t."""
    tot = 0.0
    if args.white:                                      # the term on batch-whitened latents, as in the theory (Cov(z) = I)
        zz = z.reshape(-1, z.shape[-1]); C = torch.cov(zz.T) + 1e-4 * torch.eye(z.shape[-1])
        ev, V = torch.linalg.eigh(C); z = (z - zz.mean(0)) @ (V * ev.rsqrt()) @ V.T
    for h in range(1, args.H + 1):
        zf = z[:, h:].reshape(-1, z.shape[-1]); af = a[:, : a.shape[1] - h + 1].reshape(-1, 2)
        zf = zf - zf.mean(0); af = af - af.mean(0)
        c = (zf.T @ af / zf.shape[0]).square().sum()
        tot = tot + (c if sq else (c + 1e-8).sqrt())
    return tot


t0 = time.time()
for it in range(args.steps):
    pos, a = rollout(args.batch, args.T); coef = bgc((args.batch, 1, args.n_bg)).repeat(args.T + 1, 1)
    x = render(pos, coef); at = torch.tensor(a, dtype=torch.float32)
    z = enc(x.flatten(0, 1)).view(args.batch, args.T + 1, -1)
    zp = pred(torch.cat([z[:, :-1], at], -1))
    l_pred = (zp - z[:, 1:]).square().sum(-1).mean()
    loss = l_pred + args.lam_sig * sigreg(z.flatten(0, 1))
    if args.variant in ("inv", "invcov"):
        loss = loss + args.lam_inv * (inv(torch.cat([z[:, :-1], z[:, 1:]], -1)) - at).square().sum(-1).mean()
    if args.variant in ("cov", "invcov"):
        loss = loss - args.mu * act_cov(z, at)
    if args.variant == "sup":                           # reference: supervised linear readout of the agent position
        loss = loss + 10 * (head(z) - torch.tensor(pos, dtype=torch.float32)).square().sum(-1).mean()
    if args.variant == "covn":                          # unsquared norm: its gradient does not vanish at Cov = 0
        loss = loss - args.mu * act_cov(z, at, sq=False)
    opt.zero_grad(); loss.backward(); opt.step(); z_tr = z.detach()
    if it % 500 == 0: print(f"it {it} pred {l_pred.item():.4f} cov {act_cov(z, at).item():.4f} ({time.time() - t0:.0f}s)", flush=True)

enc.eval(); pred.eval()
with torch.no_grad():
    # probes
    pos, a = rollout(2000, 1); coef = bgc((2000, 1, args.n_bg)).repeat(2, 1)
    z = enc(render(pos, coef).flatten(0, 1)).view(2000, 2, -1).numpy()
    def r2(Z, Y):
        Z1 = np.hstack([Z, np.ones((len(Z), 1))]); n = len(Z) // 2
        w = np.linalg.lstsq(Z1[:n], Y[:n], rcond=None)[0]; res = Y[n:] - Z1[n:] @ w
        return 1 - res.var(0).sum() / Y[n:].var(0).sum()
    r2_pos, r2_bg = r2(z[:, 0], pos[:, 0]), r2(z[:, 0], coef[:, 0])
    zt = torch.tensor(z[:200, 0]); acts = torch.randn(64, 2)
    zz = pred(torch.cat([zt[:, None].expand(-1, 64, -1), acts[None].expand(200, -1, -1)], -1))
    response = zz.var(1).sum(-1).mean().item(); zvar = float(z[:, 0].var(0).sum())
    # planning: random-shooting MPC, horizon 5, 256 candidates
    succ = 0; dist0 = []; dist1 = []
    for ep in range(args.episodes):
        coef1 = bgc((1, args.n_bg)); p_cur = rng.uniform(0, 1, (1, 2)); goal = rng.uniform(0, 1, (1, 2))
        zg = enc(render(goal, coef1)); dist0.append(np.linalg.norm(p_cur - goal))
        for step in range(25):
            zc = enc(render(p_cur, coef1)).expand(256, -1); cand = torch.randn(256, 5, 2)
            for h in range(5): zc = pred(torch.cat([zc, cand[:, h]], -1))
            best = (zc - zg).square().sum(-1).argmin()
            p_cur = np.clip(p_cur + args.step * (cand[best, 0].numpy()[None] + args.sigma * rng.standard_normal((1, 2))), 0, 1)
        d = np.linalg.norm(p_cur - goal); dist1.append(d); succ += d < 0.1
res = dict(variant=args.variant, seed=args.seed, K=args.K, n_bg=args.n_bg, sigma=args.sigma, mu=args.mu, white=args.white, bg_dist=args.bg_dist, lam_sig=args.lam_sig, lam_inv=args.lam_inv,
           r2_pos=float(r2_pos), r2_bg=float(r2_bg), response=response, zvar=zvar, success=succ / args.episodes,
           dist_start=float(np.mean(dist0)), dist_end=float(np.mean(dist1)), pred=l_pred.item(), act_cov=act_cov(z_tr, at).item(), sec=time.time() - t0)
print(json.dumps(res))
if args.out: open(args.out, "a").write(json.dumps(res) + "\n")
