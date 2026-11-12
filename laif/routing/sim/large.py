"""Anaheim and Chicago Sketch, CTM (dt 0.05 / 0.25 min): strategies against the free-flow lower bound (mean
free-flow trip on the same cells). Usage: python large.py Anaheim 0.8 1.0 1.2"""
import sys
import time

import common
import dnl
import static as S

name = sys.argv[1]
for f in map(float, sys.argv[2:]):
    G, Q, c_ue, a_ue, a_ff = dnl.setup(name, f)
    _, hor, B, it = dnl.GRID[name]
    sim, sf = dnl.Ctm(G, Q, dnl.DT[name], factor=f, horizon=hor, B=B), common.soft(G, Q, name)
    dist = G.shortest(sim.ncell.astype(float), G.dest)[0]
    ff = (Q * dist[:, G.orig].T).sum() / Q.sum() * sim.dt
    U = max(1, round(1 / sim.dt))
    X = S.cfw(G, f * Q, S.Cost(G.g, True), tol=1e-5, per_dest=True)[0]
    a_so, a_cap = dnl.ue_alpha(G, X, S.Cost(G.g, True)(X.sum(0))), dnl.cap_alpha(G, f * Q)
    pols = {"UE routes (static)": lambda: (lambda s, k: a_ue), "SO routes (static BPR)": lambda: (lambda s, k: a_so),
            "APDV on travel times": lambda: dnl.Reactive(None, a_ue, "exit", U=U)}
    if a_cap is not None:
        pols["capacity plan (static LP)"] = lambda: (lambda s, k: a_cap)
    pols["price-based APDV, learned"] = common.learned(sim, a_ff, G, sf, U)
    print(f"{name} x{f}: free-flow lower bound {ff:.2f} min, capacity plan {'feasible' if a_cap is not None else 'infeasible'}", flush=True)
    for lab, mk in pols.items():
        r = sim.run(mk())
        t = r["vh"] * 60 / sim.total
        print(f"  {lab}: {t:.2f} min = {t / ff:.3f} x free flow, left {abs(r['left']):.1e}", flush=True)
    t0 = time.perf_counter()
    r, gaps, _ = dnl.due(sim, a_ue, it)
    t = r["vh"] * 60 / sim.total
    print(f"  DUE (central, predictive): {t:.2f} min = {t / ff:.3f} x free flow, gap {gaps[-1]:.1e}", flush=True)
