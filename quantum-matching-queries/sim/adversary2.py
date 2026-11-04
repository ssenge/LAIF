"""Hill-climb for instances hard for every method at once.

Objective: min(cost_d, cost_pass, pure) from copies.evaluate. Passes are not guaranteed
to behave like shortest-path phases, so this is hardness against what we can run.
Usage: adversary2.py s1 s2 ... [--secs N]   writes adversary2_best.json
"""
import json
import random
import sys
import time

import networkx as nx

from adversary import mutate
from copies import evaluate


def score(G):
    if G.number_of_edges() == 0:
        return 0, (0, 0, 0)
    t = evaluate(G)
    return min(t), t


def climb(s, secs, seed):
    rng = random.Random(seed)
    G = nx.gnp_random_graph(s, 3 / s, seed=rng.randrange(10**9))
    best, trip = score(G)
    top, topT, topG = best, trip, G
    end = time.time() + secs
    while time.time() < end:
        H = mutate(G, rng)
        v, t = score(H)
        if v >= best:
            G, best = H, v
            if v > top:
                top, topT, topG = v, t, H.copy()
    return top, topT, topG


if __name__ == "__main__":
    args = sys.argv[1:]
    secs = 60
    if "--secs" in args:
        i = args.index("--secs")
        secs = int(args[i + 1])
        del args[i:i + 2]
    out = {}
    for s in [int(a) for a in args] or [12, 20, 30, 45, 70]:
        rec = (-1, None, None)
        for seed in range(2):
            t = climb(s, secs, seed)
            if t[0] > rec[0]:
                rec = t
        out[s] = {"score": rec[0], "triple": rec[1], "edges": list(map(list, rec[2].edges))}
        print(f"s={s:3d} sqrt={s**.5:4.1f} worst min-cost={rec[0]:3d} (cost_d, cost_pass, pure)={rec[1]} m={rec[2].number_of_edges()}", flush=True)
        with open("adversary2_best.json", "w") as f:
            json.dump(out, f)
