#!/usr/bin/env python3
"""Small-case check for the lower bound sketched for Theorem 1 of ../README.md.

Circuit: input |s>|+>, s in {0,1}^T, then for each i a rotation Rz(theta_i) on the last qubit controlled by bit i of s.
Measuring X gives f_s(theta) = cos(<s, theta>). That is T trainable two-qubit gates, each used once.
Question: how many inputs s can be shattered at margin gamma, as a function of T?

Note: random sampling plus hill climbing, so each m printed is a lower bound on the shattering number.
"""
import sys
import numpy as np

GAMMA = 0.25


def count(s, th):
    v = np.cos(th @ s.T)
    ok = (np.abs(v) >= GAMMA).all(axis=1)
    return np.unique((v[ok] > 0) @ (1 << np.arange(s.shape[0]))).size


def largest(T, rng, n, tries, th=None):
    th = rng.uniform(0, 2 * np.pi, size=(n, T)) if th is None else th
    pool = np.array([[(x >> i) & 1 for i in range(T)] for x in range(1, 2 ** T)], float)
    s = pool[:1]
    while s.shape[0] < min(pool.shape[0], 21):
        m = s.shape[0] + 1
        best, bs = -1, None
        cur = np.vstack([s, pool[rng.integers(len(pool))]])
        for _ in range(tries):
            d = cur.copy()
            d[rng.integers(m)] = pool[rng.integers(len(pool))]
            if len({tuple(r) for r in d}) < m:
                continue
            c = count(d, th)
            if c >= best:
                best, bs, cur = c, d, d
            if best == 2 ** m:
                break
        if best < 2 ** m:
            break
        s = bs
    return s


def main():
    rng = np.random.default_rng(1)
    # the witness is exact: cos(theta_1), cos(theta_2), cos(theta_1 + theta_2) take all 8 sign patterns
    assert count(np.array([[1, 0], [0, 1], [1, 1.0]]), rng.uniform(0, 2 * np.pi, (100000, 2))) == 8
    for T in range(2, int(sys.argv[1]) + 1):
        s = largest(T, rng, int(sys.argv[2]), int(sys.argv[3]))
        print(f"T={T}: shattered {s.shape[0]} inputs at margin {GAMMA}, ratio {s.shape[0] / T:.2f}", flush=True)


if __name__ == "__main__":
    main()
