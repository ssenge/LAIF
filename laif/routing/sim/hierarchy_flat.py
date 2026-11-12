"""Flat against two-level price-based APDV from a cold start: python hierarchy_flat.py ChicagoSketch 1.0 30 1 (cell size,
zone radius); also checks that no vehicle is lost (dnl.Ctm.run asserts it)."""
import sys, time
import numpy as np

import dnl
import logit
name, f, size, hops = sys.argv[1], float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
G, Q, c_ue, a_ue, a_ff = dnl.setup(name, f)
th = 1.0 if name == "SiouxFalls" else 3.0
sf = logit.Soft(G, Q, th, G.g.fft.copy())
dt = 1.0 if name == "SiouxFalls" else dnl.DT[name]
hor = 600 if name == "SiouxFalls" else dnl.GRID[name][1]
sim = dnl.Ctm(G, Q, dt, factor=f, horizon=hor)
U = max(1, round(1 / dt))
H = dnl.Hier(G, sf, size, hops)
print("cells", H.K, "sizes", np.bincount(H.lab).min(), np.bincount(H.lab).max(), "messages hier/flat", H.messages())
for lab, h in (("flat", None), ("hier", H)):
    t = time.time()
    r = sim.run(dnl.Price(a_ff, "exit", 3.0, 0.95, 1.0, U=U, soft=sf, dyn=True, lmax=5 * G.g.fft, hier=h))
    print(lab, "cold mean", round(r["vh"] * 60 / sim.total, 3), "left", r["left"], f"{time.time() - t:.0f}s", flush=True)
