"""Checks for the note on the quantum lower bound for frequency sampling on a set of characters (README.md).

1. The reduction identities Z_{s0}(f) = M^{-1/2} sum g and Z_s(f) = Z_{s xor s0}(g) for f = g chi_{s0}.
2. For g uniform among functions with sum S, E Z_u(g)^2 = 1 - (S^2 - M)/(M(M - 1)) for u != 0 (exact enumeration
   for M = 8, sampling for M = 64), so E R <= K in case A, and the tail P(D > 21) <= 1/20 by sampling.
3. The repetition count r: binomial tails with per-run probabilities >= 0.0376 (case A) and <= 0.02 (case B).
4. The numbers in the proof: (sum g)^2 <= M^2/2 when K <= M/400 and c = 99.
5. The zero-query case: total variation between the targets of two inputs is at least 1/2.
"""
import itertools
import math

import numpy as np
from scipy.stats import binom

rng = np.random.default_rng(3)


def chars(m):
    pts = np.array(list(itertools.product([0, 1], repeat=m)))
    return (-1.0) ** (pts @ pts.T % 2)  # chi[s, sigma]


def Z(f, chi):
    return chi @ f / math.sqrt(len(f))


def check_identities():
    m = 5
    chi = chars(m)
    for _ in range(20):
        g = rng.choice([-1.0, 1.0], 2 ** m)
        s0 = rng.integers(2 ** m)
        f = g * chi[s0]
        zf, zg = Z(f, chi), Z(g, chi)
        assert abs(zf[s0] - g.sum() / math.sqrt(2 ** m)) < 1e-12
        assert all(abs(zf[s] - zg[s ^ s0]) < 1e-12 for s in range(2 ** m))
    print("1. reduction identities hold (m = 5, 20 random cases)")


def fixed_weight(M, S, n):
    """n uniform functions on M points with sum S."""
    neg = (M - S) // 2
    out = np.ones((n, M))
    for i in range(n):
        out[i, rng.choice(M, neg, replace=False)] = -1
    return out


def check_moments():
    m, M = 3, 8
    chi = chars(m)
    for S in [0, 2, 4, 6]:
        neg = (M - S) // 2
        vals = []
        for idx in itertools.combinations(range(M), neg):
            g = np.ones(M); g[list(idx)] = -1
            vals.append(Z(g, chi)[1:] ** 2)
        mean = np.mean(vals, axis=0)
        pred = 1 - (S * S - M) / (M * (M - 1))
        assert np.allclose(mean, pred)
    print("2. E Z_u^2 = 1 - (S^2 - M)/(M(M - 1)) exactly for M = 8, every u != 0 and S = 0, 2, 4, 6")
    m, M = 6, 64
    chi = chars(m)
    for S in [0, 16, 32]:
        G = fixed_weight(M, S, 20000)
        z2 = (G @ chi.T / math.sqrt(M)) ** 2
        pred = 1 - (S * S - M) / (M * (M - 1))
        assert np.max(np.abs(z2[:, 1:].mean(0) - pred)) < 0.08
    print("   and by sampling for M = 64, S = 0, 16, 32")
    worst = 0
    for m in [6, 8, 10]:
        M = 2 ** m
        chi = chars(m)
        G = fixed_weight(M, 0, 4000)
        z2 = (G @ chi.T / math.sqrt(M)) ** 2
        for K in [2, 4, M // 8]:
            for _ in range(5):
                U = rng.choice(np.arange(1, M), K - 1, replace=False)
                D = 1 + z2[:, U].sum(1) / K
                worst = max(worst, np.mean(D > 21))
    assert worst <= 1 / 20
    print(f"   case A: largest sampled P(D > 21) = {worst:.4f} <= 1/20 (M = 64, 256, 1024; K = 2, 4, M/8)")


def binom_tail_ge(r, p, k):
    return float(binom.sf(k - 1, r, p))


def check_repetitions():
    pa, pb = 1 / 21 - 1 / 100, 1 / 100 + 1 / 100
    r = 1500
    k = math.ceil(r * (pa + pb) / 2)
    errA = 1 - binom_tail_ge(r, pa, k)
    errB = binom_tail_ge(r, pb, k)
    assert errA <= 0.05 and errB <= 0.05
    print(f"3. r = {r} runs, accept case A iff at least {k} outcomes are the extra symbol: errors {errA:.4f}, {errB:.4f}")


def check_numbers():
    c = 99
    for m in range(9, 40):
        M = 2 ** m
        for K in sorted({1, 2, 3, max(1, M // 1000), M // 400}):
            if K < 1 or K > M // 400:
                continue
            S = 2 * math.ceil(math.sqrt(c * K * M) / 2)
            assert S * S >= c * K * M and S * S <= M * M / 2 and S <= M
    print("4. (sum g)^2 in [cKM, M^2/2] for K <= M/400, c = 99, 2^9 <= M <= 2^39")


def check_trivial():
    # K >= 2: f = chi_s and f' = chi_t for s != t in S; targets put M/(K + M) >= 1/2 on s and on t
    for M, K in [(16, 2), (16, 16), (1024, 3), (1024, 1024)]:
        assert M / (K + M) >= 0.5
    # K = 1: f = chi_s0 gives the extra symbol probability 1/(1 + M), a balanced f gives 1
    print("5. zero queries: two inputs whose targets are at total variation >= 1/2")


if __name__ == "__main__":
    check_identities()
    check_moments()
    check_repetitions()
    check_numbers()
    check_trivial()
    print("all checks passed")
