"""Asserts for the E8P lattice codebook and quip (2-bit, QuIP# form without fine-tuning). Run: python sim/test_quip.py"""
import sys, pathlib, itertools
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
import torch
from nnc import compress as C

torch.manual_seed(0)
torch.set_num_threads(1)
S = C.e8p_source()
assert S.shape == (256, 8) and len({tuple(s) for s in S.tolist()}) == 256
assert ((S * 2) % 2 == 1).all() and ((S ** 2).sum(1) <= 10).sum() == 227 and ((S ** 2).sum(1) == 12).sum() == 29

# full codebook: every source with every even-sum sign pattern (2^7 of 2^8) and both shifts = 2^16 distinct points
sg = torch.tensor(list(itertools.product((1.0, -1.0), repeat=8)))
P = (sg[:, None, :] * S[None]).reshape(-1, 8)
P = P[torch.remainder(P.sum(1), 2) == 0]
CB = torch.cat([P + 0.25, P - 0.25])
assert CB.shape == (2 ** 16, 8) and len({tuple(p) for p in CB.tolist()}) == 2 ** 16

# structured search equals brute force
Y = torch.randn(3000, 8) * 1.2
q = C.e8p_nearest(Y, S)
dq = ((Y - q) ** 2).sum(1)
db = torch.cat([torch.cdist(y, CB).pow(2).min(1).values for y in Y.split(300)])
assert torch.allclose(dq, db, atol=1e-4), (dq - db).abs().max()
assert {tuple(p) for p in q.tolist()} <= {tuple(p) for p in CB.tolist()}

# Gaussian MSE per coordinate over the step c (x / (c rms) is quantized); 2-bit scalar Lloyd-Max is 0.1175
X = torch.randn(200000, 8)
mse = {c: ((X - c * C.e8p_nearest(X / c, S)) ** 2).mean().item() for c in torch.arange(0.8, 1.3, 0.02).tolist()}
c0 = min(mse, key=mse.get)
print(f'E8P Gaussian MSE {mse[c0]:.4f} at c={c0:.2f}')
assert mse[c0] < 0.1 and abs(C.E8P_SCALE - c0) <= 0.03, (c0, mse[c0])

# a layer: lower H-weighted error than GPTQ 2-bit g128 with rotation (2.25 bpw) at 2 bpw
o, i = 64, 256
Xc = torch.randn(4000, i) @ torch.randn(i, i) * 0.3 + torch.randn(4000, i) * torch.linspace(0.1, 3, i)
H = Xc.T @ Xc / 4000
W = torch.randn(o, i) / i ** 0.5 * torch.linspace(0.2, 3, o)[:, None]
Qq, bq = C.quip(W, H)
Qg, bg = C.gptq(W, H, 2, 128, act=1, clip=1, had=1)
eq, eg = C.werr(W, Qq, H), C.werr(W, Qg, H)
print(f'quip {eq:.4f} at {bq / W.numel():.3f} bpw, gptq {eg:.4f} at {bg / W.numel():.3f} bpw')
assert bq == 2 * o * i + C.FP and eq < eg

# per-row scales, no output rotation, column rescale: bit counts and errors; a zero row gives finite output
W[3] = 0
for kw, extra in ((dict(rows=1), o * C.FP), (dict(ro=0, rows=1), o * C.FP), (dict(rescale=1), C.FP + i * C.FP)):
    Qk, bk = C.quip(W, H, **kw)
    assert bk == 2 * o * i + extra and torch.isfinite(Qk).all(), kw
    assert C.werr(W, Qk, H) < eg, kw
    if kw.get('ro') == 0:  # without the output rotation a zero row stays a row: it must decode near 0
        assert Qk[3].abs().max() < 1e-3, kw
for t in (0, 3):  # tune passes never raise the H-weighted error
    Qt, _ = C.quip(W, H, rows=1, ro=0, tune=t)
    if t == 0:
        e0 = C.werr(W, Qt, H)
    else:
        assert C.werr(W, Qt, H) <= e0 + 1e-9
print('ok')
