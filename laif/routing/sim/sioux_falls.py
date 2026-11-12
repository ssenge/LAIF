"""Sioux Falls, CTM at dt = 1 min: price-based APDV (cold start; learned with origin holding) against the DSO lower
bound. Usage: python sioux_falls.py 0.3 0.4 0.5 0.6 0.7"""
import sys

import common
import dnl

for f in map(float, sys.argv[1:]):
    G, Q, c_ue, a_ue, a_ff = dnl.setup("SiouxFalls", f)
    sim, sf = dnl.Ctm(G, Q, 1.0, factor=f, horizon=600), common.soft(G, Q, "SiouxFalls")
    lb = dnl.DSO_SF[f]
    for lab, mk in (("cold start", common.cold(a_ff, G, sf, 1)), ("learned", common.learned(sim, a_ff, G, sf, 1))):
        r = sim.run(mk())
        t = r["vh"] * 60 / sim.total
        print(f"x{f} price-based APDV, {lab}: {t:.2f} min = {t / lb:.3f} x DSO bound {lb}, left {abs(r['left']):.1e}", flush=True)
