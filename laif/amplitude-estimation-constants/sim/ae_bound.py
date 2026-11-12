"""Certified worst-case number of calls of amplitude estimation without phase estimation.

Stage at width w in cell (lo, hi]: K is the largest odd K <= cap(w) that fits (so K in [kmin, cap(lo)]);
then N_K = the smallest N on a fixed grid with Wphi(N, alpha_c) / K <= lo / r, where Wphi is the largest
Clopper-Pearson width in the angle K theta over all outcomes. Cost N_K (K - 1) / 2 Q calls.
alpha_c is constant on blocks of cells and is rounded down to a geometric grid.

usage: ae_bound.py eps alpha r kappa gamma
"""
import sys
import numpy as np
from functools import lru_cache
from ae_core import cpv, kg as _kg, HALF

kg = lru_cache(None)(_kg)
NGRID = sorted({int(round(1.08 ** i)) for i in range(0, 136)})


@lru_cache(None)
def wtable(a):
    """Running minimum over the N grid of the worst Clopper-Pearson angle width at level a."""
    out, best = [], np.inf
    for N in NGRID:
        lo, hi = cpv(N, a)
        w = (np.arcsin(np.sqrt(hi)) - np.arcsin(np.sqrt(lo))).max()
        best = min(best, w); out.append(best)
    return out


def qround(a):
    return 1.1 ** np.floor(np.log(a) / np.log(1.1))   # round down: more conservative


def bound(eps, alpha_last, r, kappa, gamma, rho=1.02):
    stop = np.arcsin(2 * eps)
    g = [stop]
    while g[-1] < HALF:
        g.append(min(HALF, g[-1] * rho))
    B, F, BA = [0.0], [0.0], [0.0]
    for c in range(len(g) - 1):
        lo, hi = g[c], g[c + 1]
        a_c = qround(alpha_last * (stop / hi) ** gamma)
        tab = wtable(a_c)
        target = max(lo / r, stop * 0.999)
        kmin = kg(hi * (1 + 1e-9), max(1, int(kappa * HALF / hi)))
        cap = max(1, int(kappa * HALF / lo))
        bc = fc = ba = 0.0
        for K in range(kmin, cap + 1, 2):
            # smallest grid N with tab[N] <= target * K (tab is non-increasing); the running minimum drops
            # at this first index, so W is the worst width of NGRID[i] itself
            i = next((j for j, v in enumerate(tab) if v <= target * K), None)
            if i is None:
                return None
            N, W = NGRID[i], tab[i]
            nxt = min(hi, W / K)
            n = int(np.searchsorted(g, nxt))
            bc = max(bc, N * (K - 1) / 2 + B[n])
            fc = max(fc, a_c + F[n])
            ba = max(ba, N * K + BA[n])            # calls to A or its inverse: 2k + 1 per shot
        B.append(max(B[-1], bc)); F.append(max(F[-1], fc)); BA.append(max(BA[-1], ba))
    return B[-1], F[-1], BA[-1]


def best(eps, alpha, r, kappa, gamma):
    lo, hi = alpha * 1e-3, alpha
    for _ in range(14):
        mid = (lo * hi) ** 0.5
        res = bound(eps, mid, r, kappa, gamma)
        if res is not None and res[1] <= alpha:
            lo = mid
        else:
            hi = mid
    return lo, bound(eps, lo, r, kappa, gamma)


if __name__ == "__main__":
    eps, alpha, r, kappa, gamma = map(float, sys.argv[1:6])
    al, res = best(eps, alpha, r, kappa, gamma)
    print(f"eps={eps} alpha={alpha} r={r} kappa={kappa} gamma={gamma}: alpha_last {al:.3g}, "
          f"sum alpha {res[1]:.4f}, worst-case Q calls {res[0]:.0f} = {res[0] * eps:.2f}/eps", flush=True)
