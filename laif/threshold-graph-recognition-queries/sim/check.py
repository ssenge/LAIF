"""Correctness and query counts for threshold.py. Exits nonzero on any mismatch.

Limits: finite sizes and these families. Answers are compared with a classical decision on the true input, which is
itself compared with the alternating 4-cycle test, on all graphs up to n = 6 and at random. Budget 32 per search.
"""
import itertools
import math
import sys
import numpy as np
from threshold import *


def alternating(A):
    n = len(A)
    return any(A[a, b] and A[c, d] and not A[a, c] and not A[b, d] for a, b, c, d in itertools.permutations(range(n), 4))


def is_chain(A):
    n = len(A)
    color = {}
    for s in range(n):
        if s in color:
            continue
        color[s], stack = 0, [s]
        while stack:
            u = stack.pop()
            for v in np.flatnonzero(A[u]):
                if int(v) not in color:
                    color[int(v)] = 1 - color[u]
                    stack.append(int(v))
                elif color[int(v)] == color[u]:
                    return False
    X = [v for v in range(n) if color[v] == 0 and A[v].any()]
    Y = [v for v in range(n) if color[v] == 1 and A[v].any()]
    if not X or not Y:
        return not A.any()
    return is_nested(A[np.ix_(X, Y)])


def exhaustive():
    rng = np.random.default_rng(0)
    bad = count = 0
    for n in range(1, 7):
        pairs = list(itertools.combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            A = np.zeros((n, n), dtype=np.int8)
            for k, (u, v) in enumerate(pairs):
                if mask >> k & 1:
                    A[u, v] = A[v, u] = 1
            assert is_threshold(A) == (not alternating(A)), A
            bad += recognize_threshold(A, rng, 32)[0] != is_threshold(A)
            bad += recognize_chain(A, rng, 32)[0] != is_chain(A)
            count += 2
    print(f"all graphs up to n = 6: {count} decisions, {bad} wrong")
    assert bad == 0


TOKENS = {
    "alternating": lambda n: "rc" * (n // 2),
    "rare": lambda n: ("c" * 9 + "r") * (n // 20) + ("r" * 9 + "c") * (n // 20),
    "blocks": lambda n: ("r" * max(1, int(n ** 0.5)) + "c" * max(1, int(n ** 0.5))) * (n // (2 * max(1, int(n ** 0.5)))),
    "corner": lambda n: "r" * (n // 2) + "rc" * max(1, int(n ** 0.5)) + "c" * (n // 2),
    "zero": lambda n: "r" * (n // 2) + "c" * (n // 2),
    "one edge": lambda n: "r" * (n // 2 - 1) + "c" + "r" + "c" * (n // 2 - 1),
}


def graphs(n, seed):
    rng = np.random.default_rng(seed)
    p = rng.permutation(n)
    yield "alternating", from_sequence([i % 2 for i in range(n)], p)
    yield "random", from_sequence(rng.integers(0, 2, n), p)
    yield "one edge", from_sequence([0, 1] + [0] * (n - 2), p)
    yield "star", from_sequence([0] * (n // 2) + [1] + [0] * (n - n // 2 - 1), p)
    yield "blocks", from_sequence([(i // max(1, int(n ** 0.5))) % 2 for i in range(n)], p)
    yield "complete", from_sequence([1] * n, p)
    yield "empty", from_sequence([0] * n, p)


def random_checks():
    rng = np.random.default_rng(1)
    count = 0
    for n in (7, 8, 12, 20, 40, 80, 150):
        for s in range(12):
            for name, A in graphs(n, s):
                assert recognize_threshold(A, rng, 32)[0], (name, n, s)
                count += 1
            for name, f in TOKENS.items():
                M = nested_from_tokens(f(n), s)
                if M.size:
                    assert recognize_nested(M, rng, 32)[0], (name, n, s)
                    count += 1
            A = from_sequence([i % 2 for i in range(n)])
            evens, odds = range(0, n, 2), range(1, n, 2)
            pairs = [(i, j) for i in evens for j in odds if j >= i + 3]
            i, j = pairs[rng.integers(len(pairs))]
            A[i, j] = A[j, i] = 0
            assert not is_threshold(A) and not recognize_threshold(A, rng, 32)[0], (n, i, j)
            count += 1
    print("families and single flips:", count, "agreed")


def scaling(top):
    ns = [2 ** k for k in range(6, top + 1)]
    print("\nthreshold graphs: queries / (n log2 n), learning plus one final search, budget 16, mean of 3; last column: fitted exponent")
    print(f"{'family':12} " + " ".join(f"{n:>8}" for n in ns) + "   exponent")
    for name in [x for x, _ in graphs(8, 0)]:
        ys = []
        for n in ns:
            qs = []
            for s in range(3):
                ans, q = recognize_threshold(dict(graphs(n, s))[name], np.random.default_rng(s), 16)
                assert ans, (name, n, s)
                qs.append(q.total())
            ys.append(float(np.mean(qs)))
        print(f"{name:12} " + " ".join(f"{y / (n * math.log2(n)):8.1f}" for y, n in zip(ys, ns)) + f"   {np.polyfit(np.log(ns[-3:]), np.log(ys[-3:]), 1)[0]:.3f}", flush=True)
    print("\nnested matrices: the same")
    print(f"{'family':12} " + " ".join(f"{n:>8}" for n in ns) + "   exponent")
    for name, f in TOKENS.items():
        ys = []
        for n in ns:
            qs = []
            for s in range(3):
                ans, q = recognize_nested(nested_from_tokens(f(n), s), np.random.default_rng(s), 16)
                assert ans, (name, n, s)
                qs.append(q.total())
            ys.append(float(np.mean(qs)))
        print(f"{name:12} " + " ".join(f"{y / (n * math.log2(n)):8.1f}" for y, n in zip(ys, ns)) + f"   {np.polyfit(np.log(ns[-3:]), np.log(ys[-3:]), 1)[0]:.3f}", flush=True)
    print("\nreading all pairs is n(n-1)/2, exponent 2, against the classical lower bound of Theorem 3")


if __name__ == "__main__":
    exhaustive()
    random_checks()
    scaling(int(sys.argv[1]) if len(sys.argv) > 1 else 11)
    print("ok")
