"""Checks for the distance amplification of local-minimum hardness (README.md).

1. The dichotomy of the base instance on small graphs: projected descent on [0,1]^n for
   q(x) = x^T ((k - 1/2)(A + I) - J) x ends at 0 when alpha(G) < k and at a point with a
   coordinate 1 when alpha(G) >= k (or at the stationary point 0, which is then not a minimiser).
2. The decoder of Theorem 1: with r copies and delta^p <= (pi/2)^p r/2, the count of coordinates in
   (pi/2, 3pi/2) separates the two cases, also for adversarial points that spend the whole budget.
"""
import itertools
import math

import numpy as np

rng = np.random.default_rng(5)


def alpha(n, edges):
    for size in range(n, 0, -1):
        for S in itertools.combinations(range(n), size):
            if all(not (a in S and b in S) for a, b in edges):
                return size, S
    return 0, ()


def descend(M, x, steps=4000, lr=0.02):
    for _ in range(steps):
        x = np.clip(x - lr * 2 * M @ x, 0, 1)
    return x


def check_dichotomy():
    cases = stalled = 0
    for _ in range(60):
        n = int(rng.integers(3, 8))
        edges = [(a, b) for a in range(n) for b in range(a + 1, n) if rng.random() < 0.4]
        A = np.zeros((n, n))
        for a, b in edges:
            A[a, b] = A[b, a] = 1
        al, S = alpha(n, edges)
        for k in range(1, n + 1):
            M = (k - 0.5) * (A + np.eye(n)) - np.ones((n, n))
            for _ in range(5):
                x = descend(M, rng.random(n))
                if al < k:
                    assert np.max(x) < 1e-6
                elif np.max(x) < 1e-6:
                    # descent can stop at the stationary point 0; it is not a local minimiser,
                    # since q < 0 along the indicator of a maximum stable set
                    e = np.zeros(n)
                    e[list(S)] = 1
                    assert e @ M @ e < 0
                    stalled += 1
                else:
                    assert np.max(x) > 1 - 1e-9
            cases += 1
    print(f"1. dichotomy holds at all descent end points ({cases} graph/threshold pairs; {stalled} runs stopped at 0, not a minimiser)")


def classify(theta, r):
    return np.sum((theta > np.pi / 2) & (theta < 3 * np.pi / 2)) > r / 2


def check_decoder():
    worst = 0
    for p in (1, 1.5, 2, 3):
        for r in (1, 2, 5, 16, 64):
            n = 4
            N = r * n
            delta = (np.pi / 2) * (r / 2) ** (1 / p) * (1 - 1e-9)
            for case in ("no", "yes"):
                for _ in range(300):
                    v = np.where(rng.random(N) < 0.5, 0.0, 2 * np.pi)
                    if case == "yes":  # one coordinate at pi in each copy, others anywhere allowed
                        for s in range(r):
                            v[s * n + rng.integers(n)] = np.pi
                        v[rng.random(N) < 0.2] = np.pi
                    # adversary: push as many coordinates as the budget allows just across pi/2
                    theta = v.copy()
                    budget = delta ** p
                    order = rng.permutation(N)
                    for i in order:
                        step = np.pi / 2 + 1e-12
                        if step ** p > budget:
                            break
                        budget -= step ** p
                        if v[i] == 0:
                            theta[i] = step
                        elif v[i] == 2 * np.pi:
                            theta[i] = 2 * np.pi - step
                        else:
                            theta[i] = np.pi - step
                    assert np.sum(np.abs(theta - v) ** p) < delta ** p
                    assert classify(theta, r) == (case == "yes")
                    worst += 1
    print(f"2. decoder correct on {worst} adversarial points, p in {{1, 1.5, 2, 3}}, r up to 64")


if __name__ == "__main__":
    check_dichotomy()
    check_decoder()
    print("all checks passed")
