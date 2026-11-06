"""Run the k = 2 Local Vector algorithm plus flip rounds on actual random binary paint shop instances
and count paint swaps per car directly from the colour sequence.

For k = 2 the Local Vector rounding is a sign: y_v = sign(D_v - tau/sqrt(d) sum_w s_vw D_w), where
D = sum_l alpha_l B_l g is a Gaussian field built with signed non-backtracking walk matrices B_l
(B_1 = A_s, B_2 = A_s^2 - d I, B_l = A_s B_{l-1} - (d - 1) B_{l-2}). An edge (v, w) with s_vw = +1
wants different first-occurrence colours, s_vw = -1 wants equal ones.

usage: bpsp_check.py cars m tau theta1,theta2,...|- [seed]
"""
import sys
import numpy as np
import scipy.sparse as sp
from lv_baseline import alphas


def instance(n, rng):
    seq = rng.permutation(np.repeat(np.arange(n), 2))
    occ = np.zeros(2 * n, int)
    seen = np.zeros(n, bool)
    for i, c in enumerate(seq):            # 0 = first occurrence, 1 = second
        occ[i] = seen[c]; seen[c] = True
    return seq, occ


def swaps(seq, occ, x):
    col = x[seq] ^ occ
    return int((col[1:] != col[:-1]).sum())


def solve(seq, occ, n, m, tau, thetas, rng, d=4):
    a, b = seq[:-1], seq[1:]
    keep = a != b                          # a car twice in a row always costs one swap
    s = np.where(occ[:-1] ^ occ[1:], 1.0, -1.0)[keep]
    a, b = a[keep], b[keep]
    A = sp.coo_matrix((np.r_[s, s], (np.r_[a, b], np.r_[b, a])), shape=(n, n)).tocsr()
    lam, al = alphas(d, m)
    g = rng.standard_normal(n)
    prev, cur = g, A @ g                   # B_0 g, B_1 g
    D = al[0] * prev + al[1] * cur
    for l in range(2, m):
        prev, cur = cur, A @ cur - (d if l == 2 else d - 1) * prev
        D += al[l] * cur
    y = np.sign(D - tau / np.sqrt(d) * (A @ D))
    for th in thetas:                      # flip if at least th incident edges are unsatisfied
        bad = ((A.multiply(y[:, None]).multiply(y[None, :])) > 0).sum(axis=1).A1
        y = np.where(bad >= th, -y, y)
    return (y < 0).astype(int)


if __name__ == "__main__":
    n, m, tau = int(float(sys.argv[1])), int(sys.argv[2]), float(sys.argv[3])
    thetas = [int(v) for v in sys.argv[4].split(",")] if sys.argv[4] != "-" else []
    rng = np.random.default_rng(int(sys.argv[5]) if len(sys.argv) > 5 else 1)
    seq, occ = instance(n, rng)
    x = solve(seq, occ, n, m, tau, thetas, rng)
    assert all(((x[seq] ^ occ)[seq == c]).sum() == 1 for c in range(min(n, 50)))   # pairs differ
    print(f"cars={n} m={m} tau={tau} rounds={thetas}: swaps/car {swaps(seq, occ, x) / n:.4f}", flush=True)
