"""Checks for the note on the quantum lower bound for frequency sampling on a set of characters (README.md).

1. The reduction identities Z_{s0}(f) = M^{-1/2} sum g and Z_s(f) = Z_{s xor s0}(g) for f = g chi_{s0}.
2. For g uniform among functions with sum S, E Z_u(g)^2 = 1 - (S^2 - M)/(M(M - 1)) for u != 0 (exact enumeration
   for M = 8, sampling for M = 64); for sum g = Sigma*, p_f(s0) >= 99/120 with probability >= 19/20 (sampled).
3. The numbers in the proof: c K M <= Sigma*^2 <= M^2/2 when K <= M/400 and c = 99.
4. The zero-query case: total variation between the targets of two inputs is at least 1/2.
"""
import itertools
import math

import numpy as np

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
    c, worst = 99, 0.0
    for m in [9, 10, 11]:
        M = 2 ** m
        chi = chars(m)
        for K in [1, 2, 4, M // 400]:
            Sig = 2 * math.ceil(math.sqrt(c * K * M) / 2)
            G = fixed_weight(M, Sig, 1000)
            z2 = (G @ chi.T / math.sqrt(M)) ** 2  # chi[0] is the constant character: z2[:, 0] = Sig^2 / M
            for _ in range(3):
                U = rng.choice(np.arange(1, M), K - 1, replace=False)
                p = z2[:, 0] / (K + z2[:, 0] + z2[:, U].sum(1))
                worst = max(worst, np.mean(p < 99 / 120))
    assert worst <= 1 / 20
    print(f"   sum g = Sigma*: largest sampled P(p_f(s0) < 99/120) = {worst:.4f} <= 1/20 (M = 512, 1024, 2048)")


def check_numbers():
    c = 99
    for m in range(9, 40):
        M = 2 ** m
        for K in sorted({1, 2, 3, max(1, M // 1000), M // 400}):
            if K < 1 or K > M // 400:
                continue
            S = 2 * math.ceil(math.sqrt(c * K * M) / 2)
            assert S * S >= c * K * M and S * S <= M * M / 2 and S <= M
    print("3. (sum g)^2 in [cKM, M^2/2] for K <= M/400, c = 99, 2^9 <= M <= 2^39")


def target(f, chi, S):
    z2 = (chi[S] @ f / math.sqrt(len(f))) ** 2
    D = 1 + z2.sum() / len(S)
    return np.concatenate([z2 / (len(S) * D), [1 / D]])


def check_trivial():
    m = 6
    chi = chars(m)
    for S in [[5], [3, 9], list(range(40)), list(range(64))]:
        s, t = S[0], (S[1] if len(S) > 1 else S[0] ^ 1)
        tv = 0.5 * np.abs(target(chi[s], chi, S) - target(chi[t], chi, S)).sum()
        assert tv >= 0.5
    print("4. zero queries: the targets of chi_s and chi_t are at total variation >= 1/2 (K = 1, 2, 40, 64)")


if __name__ == "__main__":
    check_identities()
    check_moments()
    check_numbers()
    check_trivial()
    print("all checks passed")
