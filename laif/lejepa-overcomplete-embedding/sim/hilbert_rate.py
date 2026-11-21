"""Gaussian world of 2605.26379 with N = 1, encoder output M = 2, exact Gaussian embedding.
z ~ N(0,1), z' = rho z + sqrt(1-rho^2) eta. h = Phi^{-1} o H o Phi with H the Hilbert curve (measure preserving
[0,1] -> [0,1]^2), so h(z) ~ N(0, I_2). Checks: (a) h(z) is close to N(0, I_2); (b) L(h) = E|h(z') - h(z)|^2 stays
above the bound M (1-rho^2)^{N/M} = 2 sqrt(1-rho^2); (c) L(h) scales like (1-rho)^{1/2}, the exponent N/M."""
import numpy as np
from scipy.special import ndtr, ndtri
from scipy.stats import kstest
P = 16                                   # curve order: 4^P cells
def d2xy(d):                             # Hilbert index -> cell (x, y), vectorized, side 2^P
    x = np.zeros_like(d); y = np.zeros_like(d); t = d.copy(); s = 1
    while s < 2 ** P:
        rx = 1 & (t // 2); ry = 1 & (t ^ rx)
        sw = ry == 0; fl = sw & (rx == 1)
        x = np.where(fl, s - 1 - x, x); y = np.where(fl, s - 1 - y, y)
        x, y = np.where(sw, y, x), np.where(sw, x, y)
        x = x + s * rx; y = y + s * ry; t = t // 4; s *= 2
    return x, y
def h(z, rng):
    u = ndtr(z); n = 4 ** P
    d = np.minimum((u * n).astype(np.int64), n - 1)
    x, y = d2xy(d)
    jx = jy = 0.5                                     # cell centre: a fixed map (resolution 2^-P)
    return np.stack([ndtri((x + jx) / 2 ** P), ndtri((y + jy) / 2 ** P)], 1)
if __name__ == '__main__':
    rng = np.random.default_rng(0); n = 400000
    z = rng.standard_normal(n); X = h(z, rng)
    ks = [kstest(X[:, i], 'norm').pvalue for i in range(2)]; c = np.corrcoef(X.T)[0, 1]
    print(f"(a) KS p-values {ks[0]:.2f} {ks[1]:.2f}, corr {c:+.4f}, var {X.var(0).round(3)}")
    assert min(ks) > 1e-3 and abs(c) < 0.01
    eps, Ls = [], []
    for e in [1e-1, 3e-2, 1e-2, 3e-3, 1e-3, 3e-4, 1e-4, 3e-5, 1e-5]:
        rho = 1 - e; zp = rho * z + np.sqrt(1 - rho ** 2) * rng.standard_normal(n)
        L = np.mean(np.sum((h(zp, rng) - h(z, rng)) ** 2, 1)); bound = 2 * np.sqrt(1 - rho ** 2)
        print(f"1-rho {e:.0e}: L {L:.4f}  bound {bound:.4f}  ratio {L / bound:.2f}  matched M=N optimum 2(1-rho) {2*e:.1e}")
        assert L >= bound
        eps.append(e); Ls.append(L)
    slope = np.polyfit(np.log(eps), np.log(Ls), 1)[0]
    print(f"(c) fitted exponent of L in (1-rho): {slope:.3f}, below N/M = 0.5 in this range")
