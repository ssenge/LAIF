"""Gamma point: compare the variants at matched truncation error. For each variant, take the largest second-factorization
cutoff on a grid whose ERI truncation error (Frobenius, of that variant's own two-body tensor) is at most the baseline's at 1e-3.
Usage: matched.py data.npz rotL.npy"""
import sys, json, numpy as np
import dflam, stack, trunc_err
from openfermion.resource_estimates.pbc.df.compute_df_resources import compute_cost
d = np.load(sys.argv[1], allow_pickle=True)
L, hc = d["L"], d["hcore"]; ne = int(d["nelec"]); mesh = list(d["mesh"]); mkq = np.zeros((1, 1), int)
Lr = np.load(sys.argv[2], allow_pickle=True)
var = {"gdf": (hc, L)}
var["gdf+shift"] = stack.shift_opt(L, hc, ne)
var["gauge"] = (hc, Lr)
var["gauge+shift"] = stack.shift_opt(Lr, hc, ne)
target = trunc_err.err(L[0, 0].real, 1e-3)
grid = [1e-3, 9e-4, 8e-4, 7e-4, 6e-4, 5e-4, 4e-4, 3e-4, 2e-4, 1e-4]
rows = []
for name, (h, LL) in var.items():
    X = LL[0, 0].real
    th = next(t for t in grid if trunc_err.err(X, t) <= target * (1 + 1e-12))
    lt, l1, l2, neig = dflam.lam(h, LL, mkq, th, True)
    c = compute_cost(2 * h.shape[1], lt, 2 * LL[0, 0].shape[0], neig, mesh)
    rows.append({"variant": name, "cutoff": th, "err": trunc_err.err(X, th), "lambda": lt, "num_eig": neig, "toffoli": int(c.total_toffolis)})
    print(json.dumps(rows[-1]), flush=True)
print("target err", target)
with open("matched.jsonl", "a") as fh:
    for r in rows:
        fh.write(json.dumps(dict(r, file=sys.argv[1])) + "\n")
