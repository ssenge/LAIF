"""Hill climbing over weight matrices to maximize the grouped extraction cost (search for costly inputs).

Starts from the chain family and random matrices; moves: re-draw one entry, swap two entries of a
column, or move a whole row up or down by a constant. Prints the best cost / n^{1.5} per n; a
fast-growing ratio would point at a family that defeats the binomial grouping.
"""
import math, random, sys, time
from grouped_cost import grouped
from contraction_cost import chain_family, random_family
from hard_families import block_chain

def climb(n, seconds, rng):
    best_W, best = None, -1
    for W0 in (chain_family(n, rng), block_chain(n, 2, rng), random_family(n, rng)):
        c = grouped(W0)[1]
        if c > best: best, best_W = c, [row[:] for row in W0]
    W = [row[:] for row in best_W]; cur = best
    t0 = time.time()
    while time.time() - t0 < seconds:
        X = [row[:] for row in W]
        m = rng.randrange(3)
        if m == 0:
            u, v = rng.randrange(1, n), rng.randrange(1, n)
            if u != v: X[u][v] = rng.uniform(0.0, 4.0)
        elif m == 1:
            v = rng.randrange(1, n); a, b = rng.randrange(1, n), rng.randrange(1, n)
            if v not in (a, b): X[a][v], X[b][v] = X[b][v], X[a][v]
        else:
            u = rng.randrange(1, n); d = rng.uniform(-0.3, 0.3)
            for v in range(n):
                if v != u: X[u][v] += d
        c = grouped(X)[1]
        if c >= cur: W, cur = X, c
        if c > best: best = c
    return best

if __name__ == "__main__":
    rng = random.Random(3); secs = float(sys.argv[1]) if len(sys.argv) > 1 else 60
    for n in (24, 48, 96):
        b = climb(n, secs, rng); L = 1 + math.log2(n)
        print(f"n={n}: best cost/n^1.5={b / n ** 1.5:7.2f}  /(n^1.5 L^2)={b / (n ** 1.5 * L * L):6.3f}", flush=True)
