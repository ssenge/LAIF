"""Sioux Falls, CTM at dt = 1 min: the baselines of the first table (static UE routes, APDV on travel times, DUE with
perfect foresight) against the DSO lower bound (dnl.DSO_SF). Usage: python baselines.py 0.3 0.4 0.5 0.6"""
import sys

import dnl

for f in map(float, sys.argv[1:]):
    G, Q, c_ue, a_ue, a_ff = dnl.setup("SiouxFalls", f)
    _, hor, B, it = dnl.GRID["SiouxFalls"]
    sim, lb = dnl.Ctm(G, Q, 1.0, factor=f, horizon=hor, B=B), dnl.DSO_SF[f]
    rows = {"UE routes (static)": sim.run(lambda s, k: a_ue), "APDV on travel times": sim.run(dnl.Reactive(None, a_ue, "exit"))}
    r, gaps, _ = dnl.due(sim, a_ue, it)
    rows[f"DUE (central, predictive, gap {gaps[-1]:.1e})"] = r
    for lab, r in rows.items():
        t = r["vh"] * 60 / sim.total
        print(f"x{f} {lab}: {t:.2f} min = {t / lb:.3f} x DSO bound {lb}, left {abs(r['left']):.1e}", flush=True)
