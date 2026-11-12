"""The dnl policies in a per-vehicle simulator, UXsim ([8]: simplified kinematic wave per link, vehicles in
platoons of deltan, FIFO links, incremental node model).

Ux has the interface of dnl.Ctm that dnl.Price and dnl.learn use (dt = 1 min, cumulative counts Hup, Hdn, Hdm per
minute, one 'cell' per link), so the same policy objects run unchanged. Every minute the policy's split rates
alpha[d, link] become UXsim's per-destination link preferences: a vehicle picks its next link at each node with
probability proportional to them (destination-based next-hop routing, as in the CTM).

Link mapping: free-flow speed u (any; only fft matters), length u x fft, lanes ceil(cap / 1800 veh/h), outflow and
inflow capacity = cap, merge priority = cap (capacity-proportional merge, as in the CTM), jam storage = KAPPA x cap x
fft (the CTM's storage). Offered inflow of a link = vehicles that entered it + vehicles waiting at upstream link
ends with it as next link + origin-queue vehicles split by the current preferences."""
import sys

import numpy as np
import uxsim

import dnl

U_SPEED = 20.0  # m/s


class Ux:
    def __init__(self, G, Q, factor=1.0, t_load=60.0, horizon=300, deltan=5, seed=0):
        self.G, self.Q, self.factor, self.t_load, self.deltan, self.seed = G, Q, factor, t_load, deltan, seed
        g = G.g
        self.dt, self.K, self.T_load = 1.0, int(horizon), int(t_load)
        self.total = factor * Q.sum() * t_load / 60
        self.first, self.ncell = np.arange(G.m), np.maximum(1, np.rint(g.fft)).astype(np.int64)
        self.cq = self.cqk = g.cap / 60
        self.lanes = np.maximum(1, np.ceil(g.cap / 1800)).astype(int)

    def world(self, duo):
        G, g = self.G, self.G.g
        W = uxsim.World(deltan=self.deltan, reaction_time=1, tmax=self.K * 60, duo_update_time=600 if duo else 1e9,
                        print_mode=0, save_mode=0, show_mode=0, random_seed=self.seed, show_progress=0,
                        vehicle_logging_timestep_interval=-1, reduce_memory_delete_vehicle_route_pref=True)
        for v in range(G.N):
            W.addNode(str(v), 0, 0)
        for a in range(G.m):
            L = int(self.lanes[a])
            W.addLink(str(a), str(G.tail[a]), str(g.head[a]), length=U_SPEED * 60 * g.fft[a], free_flow_speed=U_SPEED,
                      jam_density_per_lane=dnl.KAPPA * g.cap[a] / 3600 / U_SPEED / L, number_of_lanes=L,
                      merge_priority=g.cap[a], capacity_out=g.cap[a] / 3600, capacity_in=g.cap[a] / 3600)
        for i, o in enumerate(G.orig):
            for j, d in enumerate(G.dest):
                if self.Q[i, j] > 0 and o != d:
                    W.adddemand(str(o), str(d), 0, self.t_load * 60, self.factor * self.Q[i, j] / 3600)
        return W

    def counts(self, W):
        """Cumulative inflow, outflow and offered inflow (veh) per link now."""
        m = self.G.m
        up = np.array([l.cum_arrival[-1] if l.cum_arrival else 0.0 for l in W.LINKS])
        dn = np.array([l.cum_departure[-1] if l.cum_departure else 0.0 for l in W.LINKS])
        wait = np.zeros(m)
        for l in W.LINKS:
            for veh in l.vehicles:
                if veh.x == l.length and getattr(veh, "route_next_link", None) is not None:
                    wait[veh.route_next_link.id] += W.DELTAN
        pref = W.ROUTECHOICE.route_pref
        for nd in W.NODES:
            out = [l.id for l in nd.outlinks.values()]
            for veh in nd.generation_queue:
                p = pref[veh.dest.id, out]
                wait[out] += W.DELTAN * (p / p.sum() if p.sum() > 0 else 1.0 / len(out))
        return up, dn, up + wait

    def run(self, policy=None, duo=False):
        """policy(sim, k) -> alpha[d, link] each minute k, or None with duo: UXsim's own reactive DUO (update every
        10 min, weight 0.5). Returns veh h (completed trips, incl. origin
        waiting; UXsim drops each OD pair's last partial platoon), unfinished share, clearance (min)."""
        assert getattr(policy, "meter", None) is None, "origin metering not mapped"
        G, m = self.G, self.G.m
        self.Hup, self.Hdn, self.Hdm = (np.zeros((self.K + 1, m)) for _ in range(3))
        W = self.world(duo)
        state = dict(k=0, done=self.K)

        def step(W):
            if W.TIME % 60:
                return
            k = int(W.TIME // 60)
            if k > self.K:
                return
            self.Hup[k], self.Hdn[k], self.Hdm[k] = self.counts(W)
            if policy is not None and k < self.K:
                A = policy(self, k)
                W.ROUTECHOICE.route_pref[np.asarray(G.dest)] = A  # in place: vehicles hold views of these rows
            state["k"] = k
            if k >= self.T_load and len(W.VEHICLES_LIVING) == 0 and state["done"] == self.K:
                state["done"] = k

        W.user_function = step
        self.W = W
        W.exec_simulation()
        k = state["k"]
        self.Hup[k + 1:], self.Hdn[k + 1:], self.Hdm[k + 1:] = self.Hup[k], self.Hdn[k], self.Hdm[k]
        W.analyzer.basic_analysis()
        a = W.analyzer
        self.total = a.trip_all  # generated vehicles, so that vh x 60 / total is their mean trip (as dnl.learn uses)
        return dict(vh=a.total_travel_time / 3600, left=1 - a.trip_completed / a.trip_all, clear=state["done"],
                    mean=a.average_travel_time / 60)


def check():
    """Light load, free-flow routes: per-vehicle mean trip = mean free-flow time (UXsim steps of 5 s)."""
    G, Q, c_ue, a_ue, a_ff = dnl.setup("SiouxFalls", 0.05)
    sim = Ux(G, Q, 0.05, t_load=30, horizon=120)
    r = sim.run(lambda s, k: a_ff)
    d = G.shortest(G.g.fft, G.dest)[0]
    ff = np.mean([d[int(v.dest.name), int(v.orig.name)] for v in sim.W.VEHICLES.values()])  # over generated platoons
    assert r["left"] == 0 and abs(r["mean"] - ff) < 0.01 * ff, (r, ff)
    assert np.allclose(sim.Hdm[-1], sim.Hup[-1]) and np.allclose(sim.Hup[-1], sim.Hdn[-1])  # all served, no queue left
    print(f"vehicles check ok: light-load mean trip {r['mean']:.3f} min vs free-flow {ff:.3f} min")


if __name__ == "__main__":
    check()
