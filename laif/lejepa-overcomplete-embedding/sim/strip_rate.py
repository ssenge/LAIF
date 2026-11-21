"""Tail-matched space-filling map for N = 1, M = 2. s = |2 Phi(z) - 1| is uniform; s in [1-2^{1-j}, 1-2^{-j}) fills the
strip a in the same range with 2^j Hilbert squares of side 2^{-j} (boustrophedon in b), so a is close to s and the
tail of z goes to the tail of h. Then Box-Muller: R = sqrt(-2 log(1-a)), theta = 2 pi b, h = R (cos, sin) ~ N(0, I_2) up to the
cell resolution 2^-P of the curve. Checks L >= 2 sqrt(1 - rho^2) and the exponent 1/2 of L in 1 - rho."""
import numpy as np
from scipy.special import ndtr
from scipy.stats import kstest
from hilbert_rate import d2xy, P
def strip(s, rng):
    j = np.floor(-np.log2(1 - s)).astype(np.int64) + 1; j = np.minimum(j, 40)
    a0 = 1 - 2.0 ** (1 - j); w = 2.0 ** (-j)
    t = (s - a0) / w                               # in [0,1)
    nsq = 2.0 ** j; q = np.floor(t * nsq); tp = t * nsq - q
    n = 4 ** P; d = np.minimum((tp * n).astype(np.int64), n - 1)
    x, y = d2xy(d); hx = (x + 0.5) / 2 ** P; hy = (y + 0.5) / 2 ** P   # cell centre: a fixed map
    b = (q + hx) / nsq; b = np.where(j % 2 == 0, 1 - b, b)   # boustrophedon
    a = a0 + w * hy
    return a, b
def h(z, rng):
    s = np.abs(2 * ndtr(z) - 1); s = np.minimum(s, 1 - 1e-15)
    a, b = strip(s, rng); R = np.sqrt(-2 * np.log1p(-a)); th = 2 * np.pi * b
    return np.stack([R * np.cos(th), R * np.sin(th)], 1)
if __name__ == '__main__':
    rng = np.random.default_rng(0); n = 1000000
    z = rng.standard_normal(n); X = h(z, rng)
    ks = [kstest(X[:, i], 'norm').pvalue for i in range(2)]; c = np.corrcoef(X.T)[0, 1]
    print(f"(a) KS p {ks[0]:.2f} {ks[1]:.2f}, corr {c:+.4f}, var {X.var(0).round(3)}"); assert min(ks) > 1e-3 and abs(c) < 0.01
    eps, Ls = [], []
    for e in [1e-1, 3e-2, 1e-2, 3e-3, 1e-3, 3e-4, 1e-4, 3e-5, 1e-5, 3e-6, 1e-6, 1e-7, 1e-8]:
        rho = 1 - e; zp = rho * z + np.sqrt(1 - rho ** 2) * rng.standard_normal(n)
        L = np.mean(np.sum((h(zp, rng) - h(z, rng)) ** 2, 1)); bound = 2 * np.sqrt(1 - rho ** 2)
        print(f"1-rho {e:.0e}: L {L:.4f}  bound {bound:.4f}  ratio {L / bound:.2f}"); assert L >= bound
        eps.append(e); Ls.append(L)
    for lo in range(0, len(eps) - 4, 2):
        print(f"local exponent over 1-rho in [{eps[lo+4]:.0e}, {eps[lo]:.0e}]: {np.polyfit(np.log(eps[lo:lo+5]), np.log(Ls[lo:lo+5]), 1)[0]:.3f}")
    last = np.polyfit(np.log(eps[-5:]), np.log(Ls[-5:]), 1)[0]; r = np.array(Ls[-4:]) / (2 * np.sqrt(1 - (1 - np.array(eps[-4:])) ** 2))
    assert abs(last - 0.5) < 0.08 and r.max() < 12, (last, r)   # order (1-rho)^{1/2} up to a slowly growing factor
    print(f"exponent {last:.3f} (N/M = 0.5); L / bound over the last four values: {np.round(r, 2)}")
