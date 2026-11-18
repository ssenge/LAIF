"""Exact mean-variance and mean-CVaR Pareto sets of a 100-asset binary portfolio instance built as in Appendix A of
arXiv:2609.13790: constant-correlation covariance, sparsified to the interactions of k SWAP layers on a line,
assets placed by a quadratic assignment, diagonal shift to positive semidefiniteness.
Usage: python -I portfolio.py <seed> [k]"""
import os, sys, time, resource
import numpy as np
from scipy.optimize import quadratic_assignment
from scipy.stats import norm
sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from pareto_qubo import pareto_qubo, value

def swap_mask(n, k):
    """Pairs of line positions that meet on adjacent qubits before or between k alternating SWAP layers."""
    at = list(range(n)); M = np.zeros((n, n), bool); swaps = 0
    for layer in range(k + 1):
        for q in range(n - 1): M[at[q], at[q + 1]] = M[at[q + 1], at[q]] = True
        if layer == k: break
        for q in range(layer % 2, n - 1, 2): at[q], at[q + 1] = at[q + 1], at[q]; swaps += 1
    return M, swaps

def instance(seed, n=100, k=4):
    rng = np.random.default_rng(seed)
    s = rng.uniform(0.1, 0.3, n); mu = rng.uniform(0, 0.1, n)
    S = 0.3 * np.outer(s, s); np.fill_diagonal(S, s ** 2)
    M, swaps = swap_mask(n, k)
    # place assets on line positions: maximize sum_ij S[pi(i),pi(j)]^2 M_ij (FAQ, then 2-opt), as in Appendix A
    A = S ** 2; np.fill_diagonal(A, 0)
    res = quadratic_assignment(M.astype(float), A, method="faq", options={"maximize": True, "rng": seed})
    res = quadratic_assignment(M.astype(float), A, method="2opt",
                               options={"maximize": True, "rng": seed, "partial_guess": np.column_stack([np.arange(n), res.col_ind])})
    pi = res.col_ind                                   # line position q holds asset pi[q]
    mu, S = mu[pi], S[np.ix_(pi, pi)]                  # reindex assets by line position
    Ss = np.where(M | np.eye(n, dtype=bool), S, 0.0)
    delta = max(0.0, -np.linalg.eigvalsh(Ss).min() + 1e-8); Sig = Ss + delta * np.eye(n)
    kept = ((Ss - np.diag(np.diag(Ss))) ** 2).sum() / ((S - np.diag(np.diag(S))) ** 2).sum()
    return mu, Sig, dict(swaps=swaps, interactions=int(np.triu(M, 1).sum()), delta=delta, kept_sq=kept, mu_sum=mu.sum())

if __name__ == "__main__":
    M, sw = swap_mask(100, 4); assert sw == 198 and np.triu(M, 1).sum() == 297, (sw, np.triu(M, 1).sum())
    seed = int(sys.argv[1]); k = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    mu, Sig, info = instance(seed, k=k); n = len(mu)
    lin = np.stack([mu, -np.diag(Sig)], 1)
    pair = {(u, v): np.array([0.0, -2 * Sig[u, v]]) for u in range(n) for v in range(u + 1, n) if Sig[u, v] != 0}
    st = {}; t = time.process_time()
    w, P, X = pareto_qubo(n, lin, pair, coords={v: (v, 0) for v in range(n)}, stats=st, keep_x=True)
    cpu = time.process_time() - t
    for x, p in zip(X[:: max(1, len(X) // 200)], P[:: max(1, len(X) // 200)]):   # spot-check values
        assert np.isclose(x @ mu, p[0]) and np.isclose(-(x @ Sig @ x), p[1])
    np.savez(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data", f"portfolio_s{seed}_k{k}.npz"), mu=mu, Sig=Sig, P=P, X=X)
    print(f"seed={seed} k={k} {info} width={w} pareto_points={len(P)} max_labels={st['max_labels']} cpu_s={cpu:.1f} rss_mb={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/2**20:.0f}", flush=True)
