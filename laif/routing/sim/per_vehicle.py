"""Sioux Falls: the same policies in the per-vehicle simulator (vehicles.Ux, FIFO lanes) and in the CTM (non-FIFO
and FIFO node model, dt 1 min). Mean trip of completed trips (min); price-based APDV cold start (common.py; origin
holding is not mapped to the per-vehicle simulator). Usage: python per_vehicle.py 0.3 0.4 0.5 0.6"""
import sys

import common
import dnl
import vehicles

for f in map(float, sys.argv[1:]):
    G, Q, c_ue, a_ue, a_ff = dnl.setup("SiouxFalls", f)
    sf = common.soft(G, Q, "SiouxFalls")
    pols = {"free-flow SP": lambda: (lambda s, k: a_ff), "static UE": lambda: (lambda s, k: a_ue),
            "price-based APDV, cold start": common.cold(a_ff, G, sf, 1)}
    ux = vehicles.Ux(G, Q, f, horizon=400)
    print(f"x{f} (CTM DSO bound {dnl.DSO_SF[f]} min)", flush=True)
    for name, mk in list(pols.items()) + [("UXsim DUO", None)]:
        r = ux.run(mk()) if mk else ux.run(None, duo=True)
        row = f"  {name}: per vehicle {r['mean']:.2f} min (left {r['left']:.3f})"
        if mk:
            for fifo in (False, True):
                c = dnl.Ctm(G, Q, 1.0, factor=f, horizon=600, fifo=fifo)
                rc = c.run(mk())
                row += f", CTM{' FIFO' if fifo else ''} {rc['vh'] * 60 / c.total:.2f} (left {abs(rc['left']):.3f})"
        print(row, flush=True)
