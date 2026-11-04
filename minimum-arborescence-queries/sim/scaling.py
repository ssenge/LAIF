"""Measured cost against n on the instance families. Usage: scaling.py [max_log2_n] > scaling.log

cost  = sum over build calls of sqrt(K * N), the bound the theorem sums, in the exact back end.
naive = cost if each selection ran plain minimum finding over the whole contracted node.
Each answer is verified by its dual certificate up to n = 1024.
Limits: exponents are fitted on hand-built families and are not worst-case statements.
"""
import math
import sys
import time
import numpy as np
from arb import solve
import instances as I


def fit(ns, ys):
    return float(np.polyfit(np.log(ns), np.log(ys), 1)[0])


def main(top):
    ns = [2 ** k for k in range(6, top + 1)]
    print(f"{'family':11} {'n':>5} {'cost':>12} {'cost/n^1.5':>10} {'/log2^2':>8} {'naive':>12} {'naive/n^1.5':>11} {'calls':>7} {'rebuilds':>8} {'sumK/n':>7} {'sumN/m':>7} {'sec':>6}")
    summary = []
    for name, f in I.FAMILIES.items():
        cs, nv = [], []
        for n in ns:
            W = f(n)
            t = time.time()
            r, out = solve(W)
            s = r.stats
            assert out is not None
            if n <= 1024:
                r.verify(*out)
            m = int(r.degin.sum())
            cs.append(s.cost)
            nv.append(s.naive)
            print(f"{name:11} {n:5} {s.cost:12.0f} {s.cost / n ** 1.5:10.2f} {s.cost / n ** 1.5 / math.log2(n) ** 2:8.3f} {s.naive:12.0f} {s.naive / n ** 1.5:11.2f} {s.calls:7} {s.rebuilds:8} {s.sum_K / n:7.2f} {s.sum_N / m:7.2f} {time.time() - t:6.1f}", flush=True)
        summary.append((name, fit(ns[-4:], cs[-4:]), fit(ns[-4:], nv[-4:])))
    print("\nfitted exponent over the last 4 sizes (the theorem gives 1.5 up to logs; classical is 2)")
    for name, a, b in summary:
        print(f"  {name:11} ours {a:.3f}   naive minimum finding {b:.3f}")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 11)
