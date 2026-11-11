# Uniform accuracy of the design estimate (Lemma U) with the unbiased estimator of Lemma E:
# random action sets of K points in R^d, small-support design (G-value <= 2d) by Frank-Wolfe, M_a = ceil(c sqrt(r pi_a ln K)/eps).
# Reports the fraction of runs with sup_x |mu~(x) - mu(x)| > eps, for growing K at fixed c.
import sys
import os
import numpy as np
from scipy.linalg import qr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))   # python -I drops the script directory
from estimator import boosted, estimator


def g_design(X, iters=5000, target=2.0):
    """small-support design with max_x x^T M(w)^{-1} x <= target * d (C_G = target), started on d pivoted points"""
    K, d = X.shape
    piv = qr(X.T, pivoting=True)[2][:d]
    w = np.zeros(K); w[piv] = 1 / d
    for _ in range(iters):
        Mi = np.linalg.inv((X * w[:, None]).T @ X)
        g = np.einsum('kd,de,ke->k', X, Mi, X)
        k = g.argmax()
        if g[k] <= target * d:
            break
        step = (g[k] / d - 1) / (g[k] - 1)
        w *= 1 - step; w[k] += step
    assert g.max() <= target * d
    return w


def run(d, K, eps, c, M_lam, rng, reps):
    X = rng.normal(size=(K, d)); X /= np.linalg.norm(X, axis=1, keepdims=True) * 2   # |x| = 1/2
    th = rng.normal(size=d); th /= np.linalg.norm(th) * 1.0
    mu = 0.5 + X @ th / 2                                                            # in [1/4, 3/4]
    w = g_design(X)
    S = np.flatnonzero(w)
    Mi = np.linalg.inv((X[S] * w[S, None]).T @ X[S])
    alpha = (X[S] @ Mi @ X.T) * w[S, None]                                           # alpha_a(x), shape |S| x K
    assert np.allclose(alpha.T @ X[S], X, atol=1e-8)
    m = 12
    Ms = np.maximum(12, np.ceil(c * np.sqrt(d * w[S] * np.log(K)) / eps)).astype(int)
    lam = {Mv: M_lam(Mv, m) for Mv in set(Ms)}
    fails = 0
    for _ in range(reps):
        Y = np.array([estimator(mu[a], Mv, m, lam[Mv], rng, 1)[0] for a, Mv in zip(S, Ms)])
        err = alpha.T @ (Y - mu[S])
        fails += np.abs(err).max() > eps
    return fails / reps, int(2 * (2 * m + 1) * Ms.sum()), len(S)


if __name__ == "__main__":
    rng = np.random.default_rng(11)
    cache = {}
    def M_lam(Mv, m):
        if (Mv, m) not in cache:
            cache[(Mv, m)] = np.cos(boosted(0.0, Mv, m, rng, 100000)).mean()
        return cache[(Mv, m)]
    d, eps, c = 6, 0.05, float(sys.argv[1]) if len(sys.argv) > 1 else 3.0
    for K in [10, 100, 1000, 10000]:   # support stays O(d) while K grows
        f, q, s = run(d, K, eps, c, M_lam, rng, 200)
        assert f <= 0.05
        print(f"d={d} K={K:6d} eps={eps}: support {s}, queries/phase {q}, queries*eps/(d sqrt(ln K)) {q * eps / (d * np.sqrt(np.log(K))):.0f}, P(sup err > eps) = {f:.3f}", flush=True)
