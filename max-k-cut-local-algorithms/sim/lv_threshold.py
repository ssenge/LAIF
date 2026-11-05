"""Local Vector algorithm (parameter m) plus one round of a threshold rule, for large degree d:
a vertex whose own label is used by c_own neighbours moves to a least-used label (ties at random)
if c_own - c_min >= t. Girth 2m+4. Search over (tau, t) on one sample, report on a fresh one.

usage: lv_threshold.py k d m [samples]
"""
import sys
import numpy as np
from lv_plus_rule import labels


def move(lab, adj, x, t, k, ru):
    own = lab[x]; n = len(own)
    cnt = np.zeros((n, k), int)
    for y in adj[x]:
        cnt[np.arange(n), lab[y]] += 1
    mine = cnt[np.arange(n), own]
    oth = np.where(np.eye(k, dtype=bool)[own], 10**6, cnt)
    cmin = oth.min(axis=1)
    pick = (ru * (oth == cmin[:, None])).argmax(axis=1)
    return np.where(mine - cmin >= t, pick, own)


def value(lab, adj, t, k, ru):
    h = (move(lab, adj, 0, t, k, ru[0]) != move(lab, adj, 1, t, k, ru[1])).astype(float)
    return h.mean(), h.std() / np.sqrt(len(h))


if __name__ == "__main__":
    k, d, m = map(int, sys.argv[1:4])
    n = int(float(sys.argv[4])) if len(sys.argv) > 4 else 40_000
    rng = np.random.default_rng(11)
    best = (0, None, None)
    taus = [float(v) for v in sys.argv[5].split(",")] if len(sys.argv) > 5 else [0.0, 1.0, 2.0, 3.0]
    for tau in taus:
        lab, adj = labels(k, d, m, tau, n, rng)
        ru = rng.random((2, n, k))
        for t in range(1, d + 1):
            v = value(lab, adj, t, k, ru)[0]
            if v > best[0]:
                best = (v, tau, t)
    v, tau, t = best
    lab, adj = labels(k, d, m, tau, 3 * n, rng)
    fresh = value(lab, adj, t, k, rng.random((2, 3 * n, k)))
    print(f"k={k} d={d} LV m={m} + threshold round (girth {2*m+4}): tau={tau} t={t} "
          f"search {v:.5f} fresh {fresh[0]:.5f} +- {fresh[1]:.5f}", flush=True)
