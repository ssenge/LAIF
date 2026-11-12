"""LocalMaxCut on d-regular trees (vertex satisfied iff at least ceil(d/2) of its d neighbours lie on the other side).
Radius-1 rule z_u = [g_u > sum_i w_i s_(i)], s_(1) <= ... <= s_(d) the sorted neighbour seeds, w symmetric
(w_i = w_{d+1-i}), so the rule commutes with flipping every seed. Gaussian seeds, sampled radius-2 trees."""
import sys, numpy as np
from scipy.optimize import minimize
def sample(d, n, rng):
    return rng.standard_normal(n), rng.standard_normal((n, d)), rng.standard_normal((n, d, d - 1))
def val(d, w, data):
    gv, gn, gc = data; k = -(-d // 2); n = len(gv)
    T = lambda s: np.sort(s, -1) @ w
    zv = gv > T(gn)
    zw = gn > T(np.concatenate([np.repeat(gv[:, None, None], d, 1), gc], -1))
    return np.count_nonzero((zw != zv[:, None]).sum(1) >= k) / n
def full(d, h):            # half vector -> symmetric weights
    h = np.asarray(h); return np.concatenate([h, h[::-1]]) if d % 2 == 0 else np.concatenate([h, h[-2::-1]])
if __name__ == "__main__":
    d = int(sys.argv[1]); nh = (d + 1) // 2
    data = sample(d, 400_000, np.random.default_rng(7))
    from math import comb
    k = -(-d // 2); p0 = sum(comb(d, j) for j in range(k, d + 1)) / 2**d
    assert abs(val(d, np.zeros(d), data) - p0) < 0.003
    best = (0, None)
    for start in [np.full(nh, 0.3 / d), np.r_[np.zeros(nh - 1), 0.5], np.linspace(0.05, 0.6, nh), np.full(nh, 1.0 / d)]:
        r = minimize(lambda h: -val(d, full(d, h), data), start, method="Nelder-Mead",
                     options={"xatol": 1e-4, "fatol": 1e-6, "maxiter": 400, "initial_simplex": None})
        if -r.fun > best[0]: best = (-r.fun, r.x)
    w = full(d, best[1])
    fresh = val(d, w, sample(d, 4_000_000, np.random.default_rng(99)))
    print(d, "train", round(best[0], 5), "fresh", round(fresh, 5), "w", np.round(w, 4).tolist(), flush=True)
