"""The flat algorithm (depth 1, no nesting) with oracle applications counted under exact Grover statistics.

Durr-Hoyer minimum finding with BBHT, each search sampled from its exact outcome law, stopping after a fixed budget
as a device would. This is depth 1 only, the n^(3/4) algorithm, because deeper levels nest bounded-error searches
and are not simulated at this level of detail. Limits: statistical, not circuits; these families only.
"""
import math
import sys
import numpy as np
from monge import random_monge, hard, warped


def dh_max(vals, rng, budget, counter):
    """Index of a maximum of vals, or a wrong index if the budget runs out."""
    N = len(vals)
    cur = int(rng.integers(N))
    limit = budget * math.sqrt(N)
    spent = 1
    while spent <= limit:
        better = np.flatnonzero(vals > vals[cur])
        t = len(better)
        theta = math.asin(math.sqrt(t / N))
        m, found = 1.0, False
        while not found and spent <= limit:
            j = int(rng.integers(0, int(m)))
            spent += 2 * j + 1
            found = t > 0 and rng.random() < math.sin((2 * j + 1) * theta) ** 2
            m = min(m * 8 / 7, math.sqrt(N) + 1)
        if found:
            cur = int(better[rng.integers(t)])
    counter[0] += spent
    return cur


def flat(M, rng, budget):
    n, c = M.shape
    k = max(1, round(math.sqrt(n)))
    counter = [0]
    segs, best = [], -np.inf

    def rec(a, b, l, u, k):
        nonlocal best
        if a > b:
            return
        if k <= 0:
            segs.append((a, b, l, u))
            return
        i = (a + b) // 2
        p = l + dh_max(M[i, l:u + 1], rng, budget, counter)
        best = max(best, M[i, p])
        rec(a, i - 1, l, p, (k - 1) // 2)
        rec(i + 1, b, p, u, k - 1 - (k - 1) // 2)

    rec(0, n - 1, 0, c - 1, k)
    if segs:
        cells = np.concatenate([M[a:b + 1, l:u + 1].ravel() for a, b, l, u in segs])
        best = max(best, cells[dh_max(cells, rng, budget, counter)])
    return best, counter[0]


def main(top):
    rng = np.random.default_rng(7)
    ns = [2 ** k for k in range(4, top + 1)]
    for budget in (8, 16, 32):
        print(f"budget {budget}*sqrt(N) per search")
        print(f"{'family':8} {'n':>5} {'applications':>13} {'/n^0.75':>8} {'wrong':>6}")
        for name, f in (("monge", lambda n, s: random_monge(n, s)), ("warped", warped), ("hard1", lambda n, s: hard(n, (np.arange(n) == s % n).astype(np.int64)))):
            xs, ys = [], []
            for n in ns:
                apps, wrong, runs = [], 0, 30 if n <= 256 else 10
                for s in range(runs):
                    M = f(n, s)
                    v, a = flat(M, rng, budget)
                    wrong += v != M.max()
                    apps.append(a)
                a = float(np.mean(apps))
                xs.append(n)
                ys.append(a)
                print(f"{name:8} {n:5} {a:13.0f} {a / n ** 0.75:8.1f} {wrong:3}/{runs}", flush=True)
            print(f"  fitted exponent over the last 4 sizes: {np.polyfit(np.log(xs[-4:]), np.log(ys[-4:]), 1)[0]:.3f}")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 11)
