"""Oracle applications under exact Grover statistics, and failure rates with a per-call budget.

Part 1 runs each search until no good element remains, the quantity bounded in expectation by
O(sqrt(d*N)) in Durr et al., Corollary 5. It reports the measured constant.
Part 2 stops each call after budget*sqrt(d*N) applications and counts wrong final answers, checked against
the exact back end. Limits: statistical simulation, small n, hand-built families.
"""
import sys
import numpy as np
from arb import solve
import instances as I


def part1(ns, seeds):
    print(f"{'family':11} {'n':>4} {'applications':>13} {'/n^1.5':>8} {'/cost':>7} {'classical n^2':>13}")
    for name in ("random", "chain", "blocks8", "bidirected"):
        for n in ns:
            W = I.FAMILIES[name](n)
            a, c = [], []
            for s in range(seeds):
                r, out = solve(W, mode="bbht", seed=s)
                r.verify(*out)
                a.append(r.stats.applications)
                c.append(r.stats.cost)
            a, c = np.mean(a), np.mean(c)
            print(f"{name:11} {n:4} {a:13.0f} {a / n ** 1.5:8.2f} {a / c:7.2f} {n * n:13}", flush=True)


def part2(n, seeds):
    print(f"\nn = {n}, wrong final answers per {seeds} runs, by budget per call")
    budgets = (2, 4, 8, 16, 32, 64)
    print(f"{'family':11} " + " ".join(f"{b:>8}" for b in budgets))
    for name in ("random", "chain", "blocks8", "bidirected"):
        W = I.FAMILIES[name](n)
        _, (_, truth) = solve(W)
        row = []
        for b in budgets:
            wrong = 0
            for s in range(seeds):
                try:
                    _, out = solve(W, mode="bbht", seed=s, budget=b)
                    wrong += out is None or out[1] != truth
                except (KeyError, AssertionError):
                    wrong += 1
            row.append(wrong)
        print(f"{name:11} " + " ".join(f"{w:8}" for w in row), flush=True)


if __name__ == "__main__":
    top = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    part1([2 ** k for k in range(4, top + 1)], 3)
    part2(64, 40)
