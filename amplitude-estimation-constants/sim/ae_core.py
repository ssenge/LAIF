"""Clopper-Pearson intervals and the fit function kg, shared by the other scripts."""
import numpy as np
from scipy.stats import beta

HALF = np.pi / 2


def cp(h, N, a):
    """Exact Clopper-Pearson interval for p from h successes in N shots at level a, widened by 1e-12."""
    lo = 0.0 if h == 0 else beta.ppf(a / 2, h, N - h + 1)
    hi = 1.0 if h == N else beta.ppf(1 - a / 2, h + 1, N - h)
    return max(0.0, lo - 1e-12), min(1.0, hi + 1e-12)


def cpv(N, a):
    """cp(h, N, a) for all h = 0..N at once."""
    h = np.arange(N + 1)
    with np.errstate(all="ignore"):
        lo = np.where(h == 0, 0.0, beta.ppf(a / 2, h, N - h + 1))
        hi = np.where(h == N, 1.0, beta.ppf(1 - a / 2, h + 1, N - h))
    return np.maximum(0.0, lo - 1e-12), np.minimum(1.0, hi + 1e-12)


def kg(w, cap):
    """Smallest, over interval positions l in [0, pi/2 - w], of the largest odd K <= cap that maps
    [l, l + w] into one branch [j pi/2, (j + 1) pi/2]. Exact sweep over the positions not yet served."""
    free = [(0.0, HALF - w)]
    for K in range(cap if cap % 2 else cap - 1, 0, -2):
        step = HALF / K
        nxt = []
        for a, b in free:                          # keep only positions where K does not fit
            for j in range(max(1, int(a / step)), min(K - 1, int((b + w) / step) + 1) + 1):
                lo, hi = max(a, j * step - w), min(b, j * step)
                if lo < hi:
                    nxt.append((lo, hi))
        free = nxt
        if not free:
            return K
    return 1


if __name__ == "__main__":
    # self-check: kg against the largest fitting K at random positions, and cpv against cp
    rng = np.random.default_rng(1)

    def fit(l, w, cap):
        u = l + w
        return next(K for K in range(cap if cap % 2 else cap - 1, 0, -2)
                    if np.floor(K * l / HALF) == np.floor(K * u / HALF) or K * u / HALF == np.floor(K * u / HALF))

    for _ in range(200):
        cap = int(rng.integers(3, 400)); w = HALF / cap * rng.uniform(0.5, 1.0)
        assert min(fit(l, w, cap) for l in rng.random(2000) * (HALF - w)) >= kg(w, cap)
    for N, a in [(1, 0.01), (7, 0.003), (50, 1e-5), (400, 0.02)]:
        lo, hi = cpv(N, a)
        assert all((lo[h], hi[h]) == cp(h, N, a) for h in range(N + 1))
    print("ok")
