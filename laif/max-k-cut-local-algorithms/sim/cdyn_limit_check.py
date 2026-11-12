"""Check of the infinite-degree limit: tree value at degree d with gamma = G / sqrt(d), printed as (cut - (k-1)/k) sqrt(d).
usage: cdyn_limit_check.py k p params.jsonl(G form) samples d1 d2 ..."""
import sys, json, math
import numpy as np
from cdyn_tree import evaluate
k, p = int(sys.argv[1]), int(sys.argv[2]); n = int(float(sys.argv[4]))
prm = np.array([json.loads(l) for l in open(sys.argv[3]) if json.loads(l)["p"] == p][-1]["params"])
for d in map(int, sys.argv[5:]):
    q = prm.copy(); q[1:p + 1] /= math.sqrt(d)
    mean, se, _, m = evaluate(k, d, p, q, n, B=max(8, 4096 // d))
    print(d, round((mean - (k - 1) / k) * math.sqrt(d), 4), "+-", round(se * math.sqrt(d), 4), flush=True)
