"""Grover QAOA chain p = 1..pmax with INTERP warm starts plus random restarts; then each rich family
from the embedded Grover optimum with perturbations of several sizes.
usage: chain.py k d pmax tries families...   (family = mixer,phase,start)"""
import sys, json, time, numpy as np
from optimize import objective, run, embed, interp
from treeqaoa import nparams
k, d, pmax, tries = map(int, sys.argv[1:5]); fams = [tuple(s.split(",")) for s in sys.argv[5:]]
rng = np.random.default_rng(0); xg = None
for p in range(1, pmax + 1):
    t0 = time.time(); vg = objective(k, d, p, ("grover", "potts", "plus"))
    starts = ([interp(xg, p)] if xg is not None else []) + [rng.uniform(0, 1.2, 2 * p) for _ in range(tries)]
    fg, xg = min((run(vg, s) for s in starts), key=lambda r: r[0])
    np.save(f"grover_{k}_{d}_{p}.npy", xg)
    row = {"p": p, "grover": round(1 - fg, 7)}
    for fam in fams:
        vf = objective(k, d, p, fam); x0 = embed_any = None
        mixer = fam[0]
        if mixer.startswith("anc"):          # no embedding helper; random starts only
            n = nparams(k, p, *fam); cands = [run(vf, rng.normal(0, 1, n)) for _ in range(tries)]
        else:
            x0 = embed(xg, k, p, fam)
            cands = [run(vf, x0 + rng.normal(0, s, len(x0))) for s in (0.1, 0.3, 1.0) for _ in range(max(1, tries // 3))]
        row[",".join(fam)] = round(1 - min(c[0] for c in cands), 7)
    row["sec"] = round(time.time() - t0)
    print(json.dumps(row), flush=True)
