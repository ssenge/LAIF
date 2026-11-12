"""Certified worst-case Q and A counts over a grid of (eps, alpha), parameters r = 2, kappa = 1, gamma = 1."""
import json, sys
from ae_bound import best
eps = float(sys.argv[1])
out = []
for alpha in (0.1, 0.05, 0.01, 1e-3, 1e-4, 1e-6):
    al, res = best(eps, alpha, 2.0, 1.0, 1.0)
    if res is None:
        print(json.dumps({"eps": eps, "alpha": alpha, "infeasible": True}), flush=True); continue
    q, f, qa = res
    out.append({"eps": eps, "alpha": alpha, "alpha_last": al, "sum_alpha": f, "q_calls": q, "c": q * eps, "a_calls": qa, "cA": qa * eps})
    print(json.dumps(out[-1]), flush=True)
