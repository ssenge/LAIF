"""Sioux Falls, CTM at dt = 1 min: the learned price schemes over 60 days of learning, as mean trip / DSO bound on
days 1, 10, 20 and 30 and the range over days 31 to 60 (the tables report day 31, the run with the profile after 30
days). Learned (non-FIFO model) and FIFO-aware (strict FIFO model). Usage: python drift.py 0.5 0.6 0.7"""
import sys

import common
import dnl

for f in map(float, sys.argv[1:]):
    G, Q, c_ue, a_ue, a_ff = dnl.setup("SiouxFalls", f)
    sf, lb = common.soft(G, Q, "SiouxFalls"), dnl.DSO_SF[f]
    for lab, fifo, h, tmin in (("learned, non-FIFO", False, 0.5, None), ("FIFO-aware, FIFO", True, 1.0, 0.05)):
        sim = dnl.Ctm(G, Q, 1.0, factor=f, horizon=600, fifo=fifo)
        tr = dnl.learn(sim, lambda P: common.price(a_ff, G, sf, 1, 0.3, P, h, tmin=tmin), 60, 1.0, common.RHO)[0] / lb
        print(f"x{f} {lab}: days 1, 10, 20, 30: {tr[0]:.3f} {tr[9]:.3f} {tr[19]:.3f} {tr[29]:.3f}; "
              f"days 31 to 60: {tr[30:].min():.3f} to {tr[30:].max():.3f}", flush=True)
