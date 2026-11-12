"""Design of a bounded-variance quantum mean estimator from certified amplitude estimation (AE), sigma = 1.

Centering: median of k means of g classical samples, |m0 - mu| <= r except with prob delta0, so S = E[x^2] <= 1 + r^2
for x = y - m0. Bands (t_{j-1}, t_j] of |x|, t_j = b rho^(j-1), j = 1..L, for x > 0 and x < 0 separately; band
variable Z = |x| 1{band} / t_j in [0, 1] (band 1: one variable (1 + x 1{|x| <= b} / b) / 2), estimated by AE to an angle interval of width eta_j, error
t_j (sqrt(a) eta + eta^2 / 2). Worst case over the split of S between band 1, bands >= 2 and the tail |x| > T."""
import numpy as np
from scipy.stats import binom

def centering(r, delta0):
    """Fewest classical samples k*g with P(Bin(k, 1/(g r^2)) >= (k+1)/2) <= delta0, k odd."""
    best = None
    for k in range(1, 400, 2):
        for g in range(1, 4000):
            p = min(1.0, 1 / (g * r * r))
            if binom.sf((k - 1) // 2, k, p) <= delta0:
                if best is None or k * g < best[0]: best = (k * g, k, g)
                break
        if best and k > best[0]: break
    return best

def error(S, b, rho, L, eta1, eta):
    T = b * rho ** (L - 1)
    A = 2 * (L - 1) * rho * eta * eta                        # both signs, bands j >= 2
    sq = sum(b * rho ** (j - 1) * eta * eta for j in range(2, L + 1))   # 2 signs x t_j eta^2 / 2
    m1 = np.linspace(0, S, 2001)
    R = S - m1
    mb = np.clip(A * T * T / 4, 0, R)                         # maximizer of sqrt(A mb) + (R - mb) / T
    band1 = b * (1 + eta1) * eta1 + 0 * m1               # one AE on (1 + x 1{|x| <= b} / b) / 2
    best = (band1 + np.sqrt(A * mb) + (R - mb) / T).max()
    return best + sq

TAB = {0.1: 33.10, 0.05: 38.03, 0.01: 52.06, 1e-3: 72.34, 1e-4: 92.12, 1e-6: 135.91}   # calls to A x eps, eps = 1e-4
def cA(alpha):
    la = np.log10(sorted(TAB)); v = [TAB[a] for a in sorted(TAB)]
    return float(np.interp(np.log10(alpha), la, v))
def ae_cost(eta, alpha):
    e = np.sin(eta) / 2
    return cA(alpha) / e

def design(eps, delta):
    best = None
    for r in (0.25, 0.5, 1.0):
        d0 = delta / 10
        c0 = centering(r, d0)
        S = 1 + r * r
        for rho in (4, 8, 16, 32, 64):
            for b in (0.5, 1, 2, 4):
                for L in range(2, 12):
                    T = b * rho ** (L - 1)
                    if S / T > eps: continue
                    al = (delta - d0) / (2 * L - 1)
                    for f1 in (1,):
                        # scale eta to meet the error target (error is increasing in eta)
                        lo, hi = 1e-9, 0.5
                        for _ in range(50):
                            mid = (lo + hi) / 2
                            if error(S, b, rho, L, f1 * mid, mid) <= eps: lo = mid
                            else: hi = mid
                        eta = lo
                        cost = c0[0] + ae_cost(f1 * eta, al) + 2 * (L - 1) * ae_cost(eta, al)
                        if best is None or cost < best[0]: best = (cost, dict(r=r, rho=rho, b=b, L=L, f1=f1, eta=eta, n0=c0[0]))
    return best

if __name__ == "__main__":
    import sys
    for eps in map(float, sys.argv[1:]):
        c, d = design(eps, 0.05)
        print(f"eps={eps}: cost {c:.4g} = {c * eps:.1f}/eps, classical >= {3.8415 / eps**2:.4g}", d, flush=True)
