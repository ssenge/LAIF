"""Correctness and scaling for monge.py. Run from this folder. Fails loudly on any mismatch.

Checks: answers against brute force for all families and depths; the hard family stays inverse Monge for
random h with maximum OR(h); polygon distance chains are totally monotone; polygon diameter against brute force and
rotating calipers. Then fitted exponents. Limits: finite sizes, these families only, and the exact checks of total
monotonicity stop at n = 24.
"""
import math
import sys
import numpy as np
from monge import *


def checks():
    rng = np.random.default_rng(0)
    cnt = 0
    for n in (2, 3, 5, 8, 13, 24, 40, 64, 100, 257):
        for s in range(6):
            cases = [random_monge(n, s), random_monge(n, s, max(1, n // 2)), warped(n, s), hard(n, rng.integers(0, 2, n)), hard(n, np.zeros(n, dtype=np.int64))]
            for M in cases:
                if n <= 24:
                    assert is_totally_monotone(M)
                for d in (0, 1, 2, 3, 5):
                    v, _ = solve(M, d)
                    assert v == M.max(), (n, s, d)
                    cnt += 1
    print("global maximum agreed with brute force on", cnt, "runs")
    for n in (2, 5, 17, 60):
        for s in range(40):
            h = rng.integers(0, 2, n)
            M = hard(n, h)
            assert is_inverse_monge(M) and M.max() == h.max()
    print("hard family: inverse Monge, maximum = OR(h)")
    cnt = 0
    for n in (4, 6, 10, 16, 30, 64, 128, 300):
        for s in range(6):
            P = convex_polygon(n, s)
            m = len(P) // 2
            if n <= 16:
                assert is_totally_monotone(dist2(P[:m], P[m:]))
            brute = int(dist2(P, P).max())
            assert calipers(P) == brute
            for d in (1, 2, 3):
                assert diameter(P, d)[0] == brute
                cnt += 1
    print("polygon diameter agreed with brute force and calipers on", cnt, "runs")


def fit(ns, ys):
    return float(np.polyfit(np.log(ns), np.log(ys), 1)[0])


def scaling(top):
    ns = [2 ** k for k in range(6, top + 1)]
    print(f"\ncost at C=1 (exact evaluation of the recursion); predicted exponent 1/2 + 1/(2d+2)")
    print(f"{'family':8} {'d':>2} {'pred':>6} {'fit':>6}   " + " ".join(f"{n:>10}" for n in ns))
    for name, f in (("monge", lambda n: random_monge(n, 1)), ("hard", lambda n: hard(n, np.zeros(n, dtype=np.int64)))):
        for d in (0, 1, 2, 3, 4, 6):
            cs = []
            for n in ns:
                M = f(n)
                v, c = solve(M, d)
                assert v == M.max()
                cs.append(c)
            print(f"{name:8} {d:2} {0.5 + 1 / (2 * d + 2):6.3f} {fit(ns[-4:], cs[-4:]):6.3f}   " + " ".join(f"{c:10.0f}" for c in cs), flush=True)
    print("\nwitness recursion of Theorem 3 on single inputs (b0 = 1): value / (sqrt(n) log2 n), then fit")
    for name, f in (("monge", lambda n: random_monge(n, 1)), ("hard", lambda n: hard(n, np.zeros(n, dtype=np.int64)))):
        w = [witness(f(n), 0, n - 1, 0, n - 1) for n in ns]
        print(f"{name:8} " + " ".join(f"{x / (n ** 0.5 * math.log2(n)):6.3f}" for x, n in zip(w, ns)) + f"   exponent fit {fit(ns[-4:], w[-4:]):.3f}")
    print("\nbest explicit depth at C = 4: cost / sqrt(n)")
    print(f"{'n':>7} {'best d':>6} {'cost/sqrt n':>12} {'n^(1/4) (flat)':>15}")
    for n in ns:
        M = f(n)
        best = min((solve(M, d, 4.0)[1], d) for d in range(0, 7))
        print(f"{n:7} {best[1]:6} {best[0] / n ** 0.5:12.1f} {n ** 0.25:15.1f}", flush=True)
    print("\npolygon diameter at d = 3, C = 1")
    ms = [2 ** k for k in range(6, min(top, 11) + 1)]
    cs = []
    for n in ms:
        P = convex_polygon(n, 2)
        v, c = diameter(P, 3)
        assert v == calipers(P)
        cs.append(c)
    print("  n:    " + " ".join(f"{n:>8}" for n in ms))
    print("  cost: " + " ".join(f"{c:8.0f}" for c in cs) + f"   fit {fit(ms[-4:], cs[-4:]):.3f}, classical reads n")


if __name__ == "__main__":
    checks()
    scaling(int(sys.argv[1]) if len(sys.argv) > 1 else 12)
    print("ok")
