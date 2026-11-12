"""Sioux Falls, CTM at dt = 1 min: strategies planned for the planned day (x F of the TNTP demand), on that day and on a
day that differs: 'incident' (link 22 -> 15 at half capacity in its middle cell, minutes 15 to 45), 'demand+20' /
'demand-20' (every OD flow x1.2 / x0.8), 'noise' (every OD flow x a lognormal factor, mean 1, sigma 0.3, unseen seed).
Ratios to the scenario day's DSO bound (BOUND; recompute with --bound, which solves dnl.dso, 10 min to 1 h).
Usage: python scenarios.py 0.4 incident [--bound]"""
import sys

import numpy as np

import common
import dnl
import static as S

BOUND = {(0.4, "planned"): 9.1068, (0.4, "incident"): 9.131, (0.4, "demand+20"): 9.347, (0.4, "demand-20"): 8.946,
         (0.4, "noise"): 9.054, (0.5, "planned"): 9.4286, (0.5, "incident"): 9.527, (0.5, "demand+20"): 10.82,
         (0.5, "demand-20"): 9.1068, (0.5, "noise"): 9.408}  # mean trip (min); x0.5 +-20% = the x0.6 / x0.4 days
INC = (66, 15.0, 45.0, 0.5)

f, kind = float(sys.argv[1]), sys.argv[2]
G, Q, c_ue, a_ue, a_ff = dnl.setup("SiouxFalls", f)
noisy = lambda n: Q * np.exp(0.3 * np.random.default_rng(n).standard_normal(Q.shape) - 0.045)
mk = lambda q, inc=(): dnl.Ctm(G, q, 1.0, factor=f, horizon=600, inc=inc)
plan = mk(Q)
real = mk({"demand+20": 1.2 * Q, "demand-20": 0.8 * Q, "noise": noisy(10 ** 6)}.get(kind, Q), [INC] if kind == "incident" else ())
sf = common.soft(G, Q, "SiouxFalls")
X = S.cfw(G, f * Q, S.Cost(G.g, True), tol=1e-5, per_dest=True)[0]
a_so, a_cap = dnl.ue_alpha(G, X, S.Cost(G.g, True)(X.sum(0))), dnl.cap_alpha(G, f * Q)
A_due = dnl.due(plan, a_ue, 40)[2]
pols = {"UE routes (static)": lambda: (lambda s, k: a_ue), "SO routes (static BPR)": lambda: (lambda s, k: a_so),
        "DUE (central, planned day)": lambda: (lambda s, k: A_due[k // s.B]),
        "price-based APDV, cold start": common.cold(a_ff, G, sf, 1),
        "price-based APDV, learned on the planned day": common.learned(plan, a_ff, G, sf, 1)}
if a_cap is not None:
    pols["capacity plan (static LP)"] = lambda: (lambda s, k: a_cap)
rows, clear = {}, []
for lab, pol in pols.items():
    a, b = plan.run(pol()), real.run(pol())
    rows[lab], clear = (a["vh"] * 60 / plan.total, b["vh"] * 60 / real.total), clear + [b["clear"]]
lb = BOUND[(f, kind)]
if "--bound" in sys.argv:
    lb = dnl.dso(real, min(real.K, int(1.1 * min(clear))), a_ue)[0] * 60 / real.total
print(f"Sioux Falls x{f}, {kind}: DSO bound planned day {BOUND[(f, 'planned')]}, scenario day {lb:.4g} min")
for lab, (a, b) in rows.items():
    print(f"  {lab}: planned {a:.2f} min = {a / BOUND[(f, 'planned')]:.3f}, scenario {b:.2f} min = {b / lb:.3f}", flush=True)
