"""Chicago Sketch, CTM: two-level price-based APDV (dnl.Hier) from a cold start for cell sizes s and zone radii h,
with the messages per period as a share of flat APDV and the routing table entries per node.
Usage: python hierarchy.py ChicagoSketch 1.0 15 30 60 120"""
import sys
import dnl
import logit
name, f = sys.argv[1], float(sys.argv[2])
G, Q, c_ue, a_ue, a_ff = dnl.setup(name, f)
sf = logit.Soft(G, Q, 3.0, G.g.fft.copy())
sim = dnl.Ctm(G, Q, dnl.DT[name], factor=f, horizon=dnl.GRID[name][1])
U = max(1, round(1 / sim.dt))
dist = G.shortest(sim.ncell.astype(float), G.dest)[0]
ff = (Q * dist[:, G.orig].T).sum() / Q.sum() * sim.dt
for size in map(int, sys.argv[3:]):
    for hops in (1, 2):
        H = dnl.Hier(G, sf, size, hops)
        r = sim.run(dnl.Price(a_ff, "exit", 3.0, 0.95, 1.0, U=U, soft=sf, dyn=True, lmax=5 * G.g.fft, hier=H))
        hm, fm = H.messages()
        print(f"{name} x{f} size {size} hops {hops}: cells {H.K}, cold {r['vh'] * 60 / sim.total / ff:.3f} x ff, "
              f"msgs {hm / fm:.3f} of flat, state per node mean {H.state.mean():.0f} max {H.state.max()} (flat {len(G.dest)})", flush=True)
