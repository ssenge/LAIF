"""Asserts for gmix e8=1: E8P lattice rows (quip, row scale, no output rotation) as one more option of the Fisher slope.
Run: python sim/test_gmix_e8.py"""
import sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
import torch
from nnc import compress as C, fisher

torch.manual_seed(0)
torch.set_num_threads(1)
o, i, g = 64, 256, 64
X = torch.randn(3000, i) @ torch.randn(i, i) * 0.3 + torch.randn(3000, i) * torch.linspace(0.1, 3, i)
H = X.T @ X / 3000
W = torch.randn(o, i) / i ** 0.5 * torch.linspace(0.2, 3, o)[:, None]
F = torch.rand(o, i) * torch.linspace(0.01, 5, o)[:, None]
fisher._F[fisher.key(W)] = F

for had in (1, 2):
    runs = {b: C.gptq(W, H, b, g, act=1, clip=1, had=had) for b in (2, 3, 4)}
    Qe, be = C.quip(W, H, ro=0, rows=1, ri=had)
    assert be == 2 * o * i + o * C.FP
    rs = (i // g) * 2 * C.FP
    const = runs[2][1] - o * i * 2 - o * rs + 2 * o  # group indices + 2-bit tag per row (4 options)
    # e8=0 is unchanged by the new per-row bit accounting
    for lam in (1e6, 10, 1e-6):
        Q0, b0 = C.gmix(W, H, g=g, lam=lam, had=had)
        Qr, br = C.gmix(W, H, g=g, lam=lam, had=had, e8=0)
        assert torch.equal(Q0, Qr) and b0 == br
    # a huge slope: every row takes the cheapest option, the lattice row (2 i + 16 < 2 i + rs)
    Q, bits = C.gmix(W, H, g=g, lam=1e9, had=had, e8=1)
    assert torch.equal(Q, Qe) and bits == const + o * (2 * i + C.FP), (bits, const + o * (2 * i + C.FP))
    # a tiny slope: every row takes 4 bits
    Q, bits = C.gmix(W, H, g=g, lam=1e-9, had=had, e8=1)
    assert torch.equal(Q, runs[4][0]) and bits == const + o * (4 * i + rs)
    # in between: each row is a row of one option, chosen as the Lagrangian optimum, bits counted per row
    opts = [runs[2][0], runs[3][0], runs[4][0], Qe]
    rb = torch.tensor([2 * i + rs, 3 * i + rs, 4 * i + rs, 2 * i + C.FP], dtype=torch.float64)
    D = torch.stack([((W - q).double() ** 2 * F.double()).sum(1) for q in opts], 1)
    for lam in (30.0, 3.0):
        Q, bits = C.gmix(W, H, g=g, lam=lam, had=had, e8=1)
        k = torch.tensor([[torch.equal(Q[r], q[r]) for q in opts].index(True) for r in range(o)])
        cost = D + lam * 1e-6 * rb
        assert torch.allclose(cost[torch.arange(o), k], cost.min(1).values)
        assert bits == const + int(rb[k].sum())
        print(f'had={had} lam={lam}: bpw {bits / W.numel():.3f}, rows per option {torch.bincount(k, minlength=4).tolist()}')
    # the mix never has a higher Fisher error than the scalar-only mix at no more bits
    for lam in (30.0, 3.0):
        Qs, bs_ = C.gmix(W, H, g=g, lam=lam, had=had)
        Qm, bm = C.gmix(W, H, g=g, lam=lam, had=had, e8=1)
        ferr = lambda Q: ((W - Q).double() ** 2 * F.double()).sum().item()
        assert ferr(Qm) + lam * 1e-6 * bm <= ferr(Qs) + lam * 1e-6 * bs_ + 1e-9  # Lagrangian over a superset
try:
    C.gmix(W, H, g=g, bpw=2.5, e8=1)
    raise SystemExit('e8 without lam must fail')
except AssertionError:
    pass
print('ok')
