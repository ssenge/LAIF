"""Checks for the distance amplification of local-minimum hardness (README.md).

1. The dichotomy of the base instance on small graphs: projected descent on [0,1]^n for
   q(x) = x^T ((k - 1/2)(A + I) - J) x ends at 0 when alpha(G) < k and at a point with a
   coordinate 1 when alpha(G) >= k (or at the stationary point 0, which is then not a minimiser).
2. The decoder of Theorem 1: with r copies, the distance to the corners {0, 2pi}^N separates the two
   cases for every point within (1 - 1/N)(pi/2) r^(1/p) of a local minimiser.
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


def corner_distance(theta, p):
    return np.sum(np.minimum(theta, 2 * np.pi - theta) ** p) ** (1 / p)


def check_decoder():
    count = 0
    for p in (1, 1.5, 2, 3):
        for r in (1, 2, 5, 16, 64):
            n = 4
            N = r * n
            rho = (np.pi / 2) * r ** (1 / p)
            radius = (1 - 1 / N) * rho
            for case in ("no", "yes"):
                for trial in range(300):
                    v = np.where(rng.random(N) < 0.5, 0.0, 2 * np.pi)
                    if case == "yes":  # at least one coordinate at pi in each copy
                        for s in range(r):
                            v[s * n + rng.integers(n)] = np.pi
                    budget = radius ** p * (1 - 1e-12)
                    theta = v.copy()
                    if trial % 3 == 0:  # worst case: spread the budget evenly over the moved coordinates
                        idx = np.flatnonzero(v == np.pi) if case == "yes" else rng.permutation(N)[: max(1, r)]
                        step = (budget / len(idx)) ** (1 / p)
                    else:
                        idx = rng.permutation(N)[: int(rng.integers(1, N + 1))]
                        step = (budget / len(idx)) ** (1 / p) * rng.random()
                    for i in idx:  # move towards the other case
                        if v[i] == np.pi:
                            theta[i] = np.pi - min(step, np.pi)
                        elif v[i] == 0:
                            theta[i] = min(step, np.pi)
                        else:
                            theta[i] = 2 * np.pi - min(step, np.pi)
                    assert np.sum(np.abs(theta - v) ** p) < radius ** p
                    D = corner_distance(theta, p)
                    assert (D > (1 + 1 / N) * rho * (1 - 1e-9)) if case == "yes" else (D < (1 - 1 / N) * rho)
                    count += 1
            # the radius rho is best possible from the dichotomy alone
            v_yes = np.zeros(N)
            v_yes[:r] = np.pi
            mid = np.zeros(N)
            mid[:r] = np.pi / 2
            assert abs(np.sum(np.abs(mid - v_yes) ** p) ** (1 / p) - rho) < 1e-9
            assert abs(np.sum(np.abs(mid) ** p) ** (1 / p) - rho) < 1e-9
    print(f"2. corner-distance decoder correct on {count} points, p in {{1, 1.5, 2, 3}}, r up to 64;"
          " the midpoint example is at distance exactly rho from both cases")


if __name__ == "__main__":
    check_dichotomy()
    check_decoder()
    print("all checks passed")
