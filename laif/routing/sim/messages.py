"""Message cost of price-based APDV (learned, common.py) with triggered updates: the profile is learned with exact
advertisement, then the next day is run with threshold eps (min). Per period (1 min): links re-advertised and
distance-vector messages, against periodic re-advertisement of every destination (at most |D| x m per period) and
triggered link-state flooding (about m messages per re-advertised link). Usage: python messages.py SiouxFalls 0.4 0.5 0.6"""
import sys

import numpy as np

import common
import dnl

name, EPS = sys.argv[1], (0.0, 0.01, 0.05, 0.2, 0.5)
for f in map(float, sys.argv[2:]):
    G, Q, c_ue, a_ue, a_ff = dnl.setup(name, f)
    dt = 1.0 if name == "SiouxFalls" else dnl.DT[name]
    sim = dnl.Ctm(G, Q, dt, factor=f, horizon=600 if name == "SiouxFalls" else dnl.GRID[name][1])
    d = G.shortest(sim.ncell.astype(float), G.dest)[0]
    ref = dnl.DSO_SF[f] if name == "SiouxFalls" else (Q * d[:, G.orig].T).sum() / Q.sum() * sim.dt
    U, sf = max(1, round(1 / sim.dt)), common.soft(G, Q, name)
    prof = dnl.learn(sim, lambda P: common.price(a_ff, G, sf, U, 0.3, P, 0.5), common.DAYS, 1.0, common.RHO)[1]
    D, m = len(G.dest), G.m
    print(f"{name} x{f}: |D| {D}, m {m}, periodic {D * m} msg/period", flush=True)
    for e in EPS:
        p = common.price(a_ff, G, sf, U, 0.3, prof, 0.5, e)
        r = sim.run(p)["vh"] * 60 / sim.total / ref
        msg = np.array(p.msg[1:], float)
        print(f"  eps {e}: trip/ref {r:.3f}, links re-adv/period {msg[:, 0].mean():.1f}, DV msg/period mean"
              f" {msg[:, 1].mean():.0f} max {msg[:, 1].max():.0f} ({msg[:, 1].mean() / (D * m):.3f} of periodic),"
              f" link-state ~{msg[:, 0].mean() * m:.0f}", flush=True)
