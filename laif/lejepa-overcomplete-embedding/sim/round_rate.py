"""Space-filling encoder for N = 1, M = 2 with round cells. s = |2 Phi(z) - 1| is uniform on [0, 1). The square
(a, b) in [0,1)^2 maps to N(0, I_2) by the polar map R = sqrt(-2 log(1 - a)), theta = 2 pi b. The a-range is cut into
bands [a_lo, a_hi): inner bands a_k = 4^-k / 2 (k >= 0, radii halving towards 0) and outer bands 1 - 2^-j (j >= 1).
A band of s is sent to the same band of a, cut into K = round(2 pi R_mid / dR) cells in b, each filled by a Hilbert
curve, so that every cell is round after the polar map. The map is measure preserving, so h(z) ~ N(0, I_2) up to the
cell resolution. Checks L >= 2 sqrt(1 - rho^2) and that L / (2 sqrt(1 - rho^2)) stays bounded as rho -> 1."""
import numpy as np
from scipy.special import ndtr
from scipy.stats import kstest
from hilbert_rate import d2xy, P
EDGES = np.unique(np.concatenate([[0.0], 0.5 * 4.0 ** -np.arange(40, -1, -1), 1 - 2.0 ** -np.arange(2, 45)]))
R = lambda a: np.sqrt(-2 * np.log1p(-a))
LO, HI = EDGES[:-1], EDGES[1:]
K = np.maximum(1, np.round(2 * np.pi * R((LO + HI) / 2) / np.maximum(R(HI) - R(LO), 1e-300))).astype(np.int64)
def h(z):
    s = np.minimum(np.abs(2 * ndtr(z) - 1), HI[-1] * (1 - 1e-16))
    k = np.searchsorted(EDGES, s, side='right') - 1
    lo, hi, kk = LO[k], HI[k], K[k]
    t = (s - lo) / (hi - lo); q = np.minimum(np.floor(t * kk), kk - 1); tp = t * kk - q
    n = 4 ** P; d = np.minimum((tp * n).astype(np.int64), n - 1)
    x, y = d2xy(d); hx = (x + 0.5) / 2 ** P; hy = (y + 0.5) / 2 ** P
    a = lo + (hi - lo) * hy; b = (q + hx) / kk
    r, th = R(a), 2 * np.pi * b
    return np.stack([r * np.cos(th), r * np.sin(th)], 1)
if __name__ == '__main__':
    rng = np.random.default_rng(0); n = 2000000
    z = rng.standard_normal(n); X = h(z)
    ks = [kstest(X[:, i], 'norm').pvalue for i in range(2)]; c = np.corrcoef(X.T)[0, 1]
    print(f"cells per band: inner {K[:3]} ... outer {K[-3:]}; KS p {ks[0]:.2f} {ks[1]:.2f}, corr {c:+.4f}")
    assert min(ks) > 1e-3 and abs(c) < 0.01
    eps, rat = [], []
    for e in [1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8, 1e-9, 1e-10]:
        rho = 1 - e; zp = rho * z + np.sqrt(1 - rho ** 2) * rng.standard_normal(n)
        D = np.sum((h(zp) - h(z)) ** 2, 1); L = D.mean(); se = D.std() / np.sqrt(n); bound = 2 * np.sqrt(1 - rho ** 2)
        print(f"1-rho {e:.0e}: L {L:.3e} +- {se:.1e}  L / bound {L / bound:.3f} +- {se / bound:.3f}"); assert L >= bound
        eps.append(e); rat.append(L / bound)
    rat = np.array(rat); print(f"ratio over 1-rho in [1e-10, 1e-5]: min {rat[3:].min():.3f} max {rat[3:].max():.3f}")
    assert rat[3:].max() < 5.5 and rat[3:].max() / rat[3:].min() < 1.06   # bounded and flat over five decades
