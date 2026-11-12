"""Sioux Falls, CTM at dt = 1 min with the strict FIFO node model of [5]: static plans and the FIFO-aware price-based
APDV against the DSO lower bound (the LP relaxes FIFO, so it bounds FIFO runs too); the same rule in the non-FIFO
model, and its sensitivity to the pruning threshold. Usage: python fifo.py 0.3 0.4 0.5 0.6 0.7"""
import sys

import common
import dnl
import static as S

for f in map(float, sys.argv[1:]):
    G, Q, c_ue, a_ue, a_ff = dnl.setup("SiouxFalls", f)
    sf, lb = common.soft(G, Q, "SiouxFalls"), dnl.DSO_SF[f]
    X = S.cfw(G, f * Q, S.Cost(G.g, True), tol=1e-5, per_dest=True)[0]
    pols = {"UE routes (static)": a_ue, "SO routes (static BPR)": dnl.ue_alpha(G, X, S.Cost(G.g, True)(X.sum(0))),
            "capacity plan (static LP)": dnl.cap_alpha(G, f * Q)}
    for fifo in (True, False):
        sim = dnl.Ctm(G, Q, 1.0, factor=f, horizon=600, fifo=fifo)
        out = lambda lab, r: print(f"x{f} {'FIFO' if fifo else 'non-FIFO'} {lab}: {r['vh'] * 60 / sim.total:.2f} min = "
                                   f"{r['vh'] * 60 / sim.total / lb:.3f} x DSO bound {lb}, left {abs(r['left']):.3f}", flush=True)
        for lab, a in pols.items():
            if fifo and a is not None:
                out(lab, sim.run(lambda s, k: a))
        for tmin in (0.02, 0.05, 0.1, 0.2) if fifo else (0.05,):
            out(f"price-based APDV, FIFO-aware, tmin {tmin}", sim.run(common.fifo_aware(sim, a_ff, G, sf, 1, tmin)()))
