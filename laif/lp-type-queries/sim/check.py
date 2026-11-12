"""Against the exact solver on all the points, and how the queries grow. Run with python check.py (numpy; qiskit and qiskit-aer for the circuits)
Limits: the exact solver is a Welzl implementation written here; it is checked against brute force on tiny inputs, in floating point.
"""
import itertools
import sys
import numpy as np
from lptype import *


def brute(P):
    """Smallest ball among those defined by at most d + 1 points that contains all points."""
    d = P.shape[1]
    best = None
    for k in range(1, d + 2):
        for R in itertools.combinations(range(len(P)), k):
            c, r2 = ball_of(P[list(R)], d)
            if not violates(P, c, r2).any() and (best is None or r2 < best):
                best = r2
    return best


def families(n, d, seed):
    r = np.random.default_rng(seed)
    yield "gaussian", r.normal(size=(n, d))
    u = r.normal(size=(n, d))
    yield "sphere", u / np.linalg.norm(u, axis=1, keepdims=True)
    P = r.normal(size=(n, d)) * 0.1
    P[r.integers(n)] += 10.0
    yield "one outlier", P
    yield "lattice", r.integers(0, 8, size=(n, d)).astype(float)
    yield "same point", np.ones((n, d))


def main():
    rng = np.random.default_rng(2)
    cnt = 0
    for d in (1, 2, 3):
        for n in (1, 2, 3, 5, 8, 11):
            for seed in range(25):
                for name, P in families(n, d, seed):
                    b = brute(P)
                    assert abs(solve(P)[1] - b) <= 1e-6 * max(1, b), (name, n, d, seed)
                    cnt += 1
    print("the classical solver agreed with brute force on", cnt, "small inputs")
    cnt = unfinished = 0
    rounds = {}
    for d in (1, 2, 3, 5):
        for n in (40, 200, 1000, 5000):
            for seed in range(8):
                for name, P in families(n, d, seed):
                    q = Q(P, rng, 32)
                    ball, t, big = clarkson(q)
                    unfinished += ball is None
                    if ball is not None:
                        want = solve(P)[1]
                        assert abs(ball[1] - want) <= 1e-5 * max(1, want), (name, n, d, seed)
                        rounds[d] = max(rounds.get(d, 0), t)
                    cnt += 1
    print(f"clarkson agreed with the solver on {cnt - unfinished} of {cnt} runs, {unfinished} ran out of rounds")
    print("largest number of rounds by dimension:", rounds)

    wrong = most = 0
    print("\nqueries / sqrt(n), budget 16, mean of 5; last column: fitted exponent")
    sizes = [2 ** k for k in range(10, 21, 2)]
    print(f"{'family':14}{'d':>3}" + "".join(f"{n:>9}" for n in sizes) + "   exponent")
    for d in (2, 3, 5):
        for name in ("gaussian", "sphere", "one outlier"):
            row = []
            for n in sizes:
                qs = []
                for seed in range(5):
                    P = dict(families(n, d, seed))[name]
                    q = Q(P, np.random.default_rng(seed), 16)
                    ball, t, _ = clarkson(q)
                    wrong += ball is None or violates(P, *ball).any()  # optimal on a subset and containing all
                    most = max(most, t)
                    qs.append(q.spent)
                row.append(np.mean(qs))
            e = np.polyfit(np.log(sizes), np.log(row), 1)[0]
            print(f"{name:14}{d:3}" + "".join(f"{x / n ** 0.5:9.0f}" for x, n in zip(row, sizes)) + f"{e:11.3f}", flush=True)
    print(f"wrong answers in those runs: {wrong}; most rounds: {most}")
    print("ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
