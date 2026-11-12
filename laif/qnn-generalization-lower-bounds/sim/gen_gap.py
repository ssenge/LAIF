#!/usr/bin/env python3
"""Checks Theorem 2 of ../README.md on a small instance: E[gen of ERM] >= (gamma/4) sqrt(m/N) for pure noise labels.

Takes a shattered set of the family f_s(theta) = cos<s, theta>, uniform inputs, labels fair coins independent of the
input, and the loss (1 - y f)/2, so the true risk of every theta is exactly 1/2. ERM is approximated by the best of many
sampled theta, which can only understate the gap of true ERM.
"""
import numpy as np
from cos_family import GAMMA, count, largest


def main():
    rng = np.random.default_rng(3)
    T = 5
    th = rng.uniform(0, 2 * np.pi, (1500000, T))
    s = largest(T, rng, 1500000, 150, th)
    m = s.shape[0]
    assert count(s, th) == 2 ** m, "not shattered on this sample"
    vals = np.cos(th @ s.T)
    print(f"T={T}, shattered m={m}, margin {GAMMA}")
    for N in [m, 2 * m, 10 * m, 100 * m, 1000 * m]:
        gaps = []
        for _ in range(60):
            idx = rng.integers(m, size=N)
            y = rng.choice([-1.0, 1.0], size=N)
            yj = np.bincount(idx, weights=y, minlength=m)
            emp = 0.5 * (1 - vals @ yj / N)
            gaps.append(0.5 - emp.min())
        gap = float(np.mean(gaps))
        bound = GAMMA / 4 * np.sqrt(m / N)
        print(f"  N={N:6d}  mean gap of sampled ERM {gap:.4f}  lower bound {bound:.4f}")
        assert gap >= bound


if __name__ == "__main__":
    main()
