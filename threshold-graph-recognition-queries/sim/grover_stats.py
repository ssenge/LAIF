"""How small can the search budget be, and how many queries does the whole recognizer spend?

Every search follows the exact Grover law and stops after budget * sqrt(N), so a too-small budget shows up as wrong
answers. "yes" inputs are threshold graphs; "no" inputs are the same with one flip that leaves threshold.
Limits: statistical, these families only, finite sizes.
"""
import math
import numpy as np
from threshold import *


def yes(n, s):
    r = np.random.default_rng(s)
    return from_sequence(r.integers(0, 2, n), r.permutation(n))


def no(n, s):
    r = np.random.default_rng(s)
    A = from_sequence([i % 2 for i in range(n)])
    pairs = [(i, j) for i in range(0, n, 2) for j in range(1, n, 2) if j >= i + 3]
    i, j = pairs[r.integers(len(pairs))]
    A[i, j] = A[j, i] = 0
    p = r.permutation(n)
    return A[np.ix_(p, p)]


def main():
    print(f"{'budget':>6} {'n':>5} {'yes wrong':>10} {'no wrong':>9} {'queries yes':>12} {'n(n-1)/2':>9}")
    for budget in (2, 4, 8, 16, 32):
        for n in (64, 256, 1024):
            runs = 30 if n < 1024 else 10
            wy = wn = 0
            qs = []
            for s in range(runs):
                rng = np.random.default_rng(1000 * n + s)
                ans, q = recognize_threshold(yes(n, s), rng, budget)
                wy += not ans
                qs.append(q.total())
                wn += recognize_threshold(no(n, s), rng, budget)[0]
            print(f"{budget:6} {n:5} {wy:6}/{runs:<3} {wn:5}/{runs:<3} {np.mean(qs):12.0f} {n * (n - 1) // 2:9}", flush=True)
    print("\nlarger samples at budget 16, yes inputs only")
    for n, runs in ((1024, 300), (2048, 80)):
        wy = sum(not recognize_threshold(yes(n, s), np.random.default_rng(7000 * n + s), 16)[0] for s in range(runs))
        print(f"n = {n}: {wy}/{runs} wrong", flush=True)


if __name__ == "__main__":
    main()
