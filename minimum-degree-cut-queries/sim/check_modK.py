"""Checks for Section 12 of the README: simple graphs with answers mod K, and restricted query sets.

Run: python check_modK.py

Tests, by assertion:
1. The product formula for kappa in Theorem 10, against the direct average over all upper triangular U, at D = 3.
2. For random pairs of histories with kappa != 0, every independent set A of the graph on S satisfies
   2^|A| <= K^R, with R the number of terms, and every nonzero upper entry has norm at least 1/K.
3. Theorem 12 on a tiny algorithm: Grover on the singletons {v_l}, with a = 0. It has B = 1/2 in the labels used,
   and the sum over j of ||psi - psi_j|| stays below 2 pi T sqrt(L) B.
4. For every K >= 3 up to 200, some z has |cos(pi 2z/K)| <= 1/2, as Proposition 11 uses.

Limits: small D, random histories, one algorithm in test 3. None of this tests the approximate degree of AND
or the sum over S.
"""
import itertools

import numpy as np

rng = np.random.default_rng(11)


def e(t):
    return np.exp(2j * np.pi * t)


def norm(t):
    return abs(t - np.round(t))


def W_matrix(D, K, R):
    """W = sum_s theta_s y_s q_s^T with theta_s = +-2z/K, and y_s, q_s with entries in {0, +-1}."""
    W = np.zeros((D, D))
    for _ in range(R):
        W += 2 * rng.integers(1, K) / K * rng.choice([-1, 1]) * np.outer(rng.integers(-1, 2, D), rng.integers(-1, 2, D))
    return W


def kappa_formula(W):
    D = len(W)
    out = 1.0 + 0j
    for l in range(D):
        out *= (1 - e(W[l, l])) / 2
        for m in range(l + 1, D):
            out *= (1 + e(W[l, m])) / 2
    return out


def kappa_direct(W):
    D = len(W)
    idx = [(l, m) for l in range(D) for m in range(l, D)]
    total = 0j
    for bits in itertools.product([0, 1], repeat=len(idx)):
        chi = (-1) ** sum(b for b, (l, m) in zip(bits, idx) if l == m)
        total += chi * e(sum(b * W[l, m] for b, (l, m) in zip(bits, idx)))
    return total / 2 ** len(idx)


for K in (3, 5, 6):
    for _ in range(20):
        W = W_matrix(3, K, 2)
        assert abs(kappa_formula(W) - kappa_direct(W)) < 1e-9

tested = 0
for K in (3, 5, 7):
    for R in (2, 4):
        for _ in range(4000):
            D = 7
            W = W_matrix(D, K, R)
            if min(norm(W[l, l]) for l in range(D)) < 1e-9:
                continue
            tested += 1
            for l in range(D):
                for m in range(l + 1, D):
                    assert norm(W[l, m]) < 1e-9 or norm(W[l, m]) >= 1 / K - 1e-9
            for size in range(1, D + 1):
                for A in itertools.combinations(range(D), size):
                    if all(norm(W[l, m]) < 1e-9 for l, m in itertools.combinations(A, 2)):
                        assert 2 ** size <= K ** R
assert tested > 0


def grover_states(L, marked, T):
    """Grover on L items, with phase -1 on the marked ones."""
    psi = np.ones(L, complex) / np.sqrt(L)
    for _ in range(T):
        psi = psi * np.array([-1 if i in marked else 1 for i in range(L)])
        psi = 2 * psi.mean() - psi
    return psi


L, T = 64, 6
base = grover_states(L, set(), T)
total = sum(np.linalg.norm(base - grover_states(L, {j}, T)) for j in range(L))
assert total <= 2 * np.pi * T * np.sqrt(L) * 0.5

for K in range(3, 201):
    assert min(abs(np.cos(2 * np.pi * z / K)) for z in range(K)) <= 0.5 + 1e-12

print(f"ok: {tested} histories with nonzero diagonal; hybrid sum {total:.1f} against {2 * np.pi * T * np.sqrt(L) * 0.5:.1f}")
