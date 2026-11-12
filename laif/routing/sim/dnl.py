"""Destination-based cell transmission model ([2] in README.md; flows, not vehicles) with queues and spillback.

Links are cut into cells of one time step dt (round(fft/dt), at least one). Triangular fundamental diagram with
jam density = KAPPA x critical density, so per cell: capacity Q = cap dt, jam occupancy KAPPA Q, backward wave speed
vf / (KAPPA - 1). Cells hold per-destination occupancies; a cell's outflow has its composition.
Nodes, default non-FIFO per turn: each out-link's supply is shared in proportion to the turn demands; vehicles
facing a blocked turn wait in the in-link's last cell and take its capacity (a partial-FIFO coupling). fifo=True:
the generic node model of [5], capacity priorities, strict FIFO per in-link.
Vertical origin queues, sinks. Routing = destination-based split rates alpha[d, link] (share of d-flow at tail(link) sent on link):
  - static: from per-destination static UE flows on the UE shortest-path DAG, or free-flow shortest paths;
  - APDV on travel times (Reactive): every U steps, shortest paths on the current link times;
  - price-based APDV (Price): see its docstring;
  - DUE (central, predictive, perfect foresight): time-dependent split rates by averaging on time-dependent
    shortest paths over the experienced (FIFO) link times; relative gap reported.
Lower bound: dso, the CTM system optimum as an LP ([3]). Times min, flows veh (rates veh/h).
"""
import sys
import time

import numpy as np
from numba import njit, prange

import net
import logit
import static as S

KAPPA = 4.0  # jam / critical density
BIG = 1e30  # finite 'unreachable' (inf would give 0 * inf in the interpolation)
DT = {"SiouxFalls": 0.5, "Anaheim": 0.05, "ChicagoSketch": 0.25}  # min. Barcelona, Winnipeg: capacities rescaled to 1


@njit(cache=True)
def _gnm(Sd, c, beta, R):
    """Generic node model ([5]): in-link flows q_i, FIFO (q_ij = q_i beta_ij), capacity priorities c."""
    ni, no = beta.shape
    q, act, Rt = np.zeros(ni), Sd > 0, R.copy()
    while act.any():
        amin, jm = np.inf, -1
        for j in range(no):
            den = 0.0
            for i in range(ni):
                if act[i]:
                    den += c[i] * beta[i, j]
            if den > 0 and Rt[j] / den < amin:
                amin, jm = Rt[j] / den, j
        if jm < 0 or amin == np.inf:  # the rest only face unconstrained out-links (sinks)
            for i in range(ni):
                if act[i]:
                    q[i] = Sd[i]
            break
        dc = False
        for i in range(ni):  # demand-constrained in-links competing for jm get their demand
            if act[i] and beta[i, jm] > 0 and Sd[i] <= amin * c[i]:
                dc, q[i], act[i] = True, Sd[i], False
                for j in range(no):
                    Rt[j] = max(Rt[j] - Sd[i] * beta[i, j], 0.0)
        if not dc:  # else all of them are supply-constrained by jm
            for i in range(ni):
                if act[i] and beta[i, jm] > 0:
                    q[i], act[i] = amin * c[i], False
                    for j in range(no):
                        Rt[j] = max(Rt[j] - q[i] * beta[i, j], 0.0)
    return q


@njit(cache=True)
def _turn_ratio(Sd, beta, R):
    """Non-FIFO: share r_j of each turn demand toward out-link j that gets through (demand-proportional)."""
    r = np.ones(R.shape[0])
    for j in range(R.shape[0]):
        Dj = (Sd * beta[:, j]).sum()
        if Dj > R[j]:
            r[j] = R[j] / Dj
    return r


@njit(cache=True)
def _step(n, ntot, first, ncell, cq, cj, in_ptr, in_lnk, out_ptr, out_lnk, didx, oidx, oq, alpha, inbuf, cu, cd,
          arr, kap, fifo, dm):
    """One step; cu, cd, dm accumulate per link: inflow, outflow, offered inflow (turn demands toward the link; an
    origin queue offers at most what its out-links can take per step)."""
    C, D = n.shape
    Sc = np.minimum(ntot, cq)
    Rc = np.maximum(np.minimum(cq, (cj - ntot) / (kap - 1)), 0.0)
    inbuf[:] = 0.0
    for v in range(in_ptr.shape[0] - 1):
        i0, nl = in_ptr[v], in_ptr[v + 1] - in_ptr[v]
        o0, nj = out_ptr[v], out_ptr[v + 1] - out_ptr[v]
        src, dv = oidx[v], didx[v]
        ni = nl + (1 if src >= 0 else 0)
        Sd, ci, beta, Rj = np.zeros(ni), np.zeros(ni), np.zeros((ni, nj + 1)), np.empty(nj + 1)
        for j in range(nj):
            Rj[j] = Rc[first[out_lnk[o0 + j]]]
        Rj[nj] = np.inf  # sink
        for i in range(ni):
            if i < nl:
                a = in_lnk[i0 + i]
                c = first[a] + ncell[a] - 1
                row, tot, Sd[i], ci[i] = n[c], ntot[c], Sc[c], cq[c]
            else:
                row = oq[src]
                tot = row.sum()
                Sd[i], ci[i] = tot, tot  # origin queue, priority = its demand
            if Sd[i] <= 0:
                continue
            for d in range(D):
                if row[d] > 0:
                    w = row[d] / tot
                    if d == dv:
                        beta[i, nj] += w
                    else:
                        for j in range(nj):
                            beta[i, j] += w * alpha[d, out_lnk[o0 + j]]
        oc = 0.0
        for j in range(nj):
            oc += cq[first[out_lnk[o0 + j]]]
        for i in range(ni):
            so = Sd[i] if i < nl else min(Sd[i], oc)
            for j in range(nj):
                dm[out_lnk[o0 + j]] += so * beta[i, j]
        # flow of d from i to j = Sd_i * share_i(d) * g_i * alpha[d, j] * r_j (FIFO: r = 1; non-FIFO: g = 1)
        if fifo:
            g, r = _gnm(Sd, ci, beta, Rj) / np.maximum(Sd, 1e-300), np.ones(nj + 1)
        else:
            g, r = np.ones(ni), _turn_ratio(Sd, beta, Rj)
        for i in range(ni):
            if Sd[i] <= 0 or g[i] <= 0:
                continue
            if i < nl:
                a = in_lnk[i0 + i]
                c = first[a] + ncell[a] - 1
                row, tot = n[c], ntot[c]
            else:
                row = oq[src]
                tot = row.sum()
            f, out = Sd[i] * g[i] / tot, 0.0
            for d in range(D):
                x = row[d] * f
                if x == 0:
                    continue
                if d == dv:
                    arr[d] += x
                    row[d] -= x
                    out += x
                else:
                    for j in range(nj):
                        w = alpha[d, out_lnk[o0 + j]] * r[j]
                        if w > 0:
                            inbuf[out_lnk[o0 + j], d] += x * w
                            row[d] -= x * w
                            out += x * w
            if i < nl:
                ntot[c] -= out
                cd[a] += out
    for a in range(first.shape[0]):  # within links, downstream first, so a cell gives before it receives
        for c in range(first[a] + ncell[a] - 2, first[a] - 1, -1):
            y = min(Sc[c], Rc[c + 1])
            if y <= 0:
                continue
            f = y / ntot[c]
            for d in range(D):
                x = n[c, d] * f
                n[c, d] -= x
                n[c + 1, d] += x
            ntot[c] -= y
            ntot[c + 1] += y
    for a in range(first.shape[0]):
        s = inbuf[a].sum()
        if s > 0:
            n[first[a]] += inbuf[a]
            ntot[first[a]] += s
            cu[a] += s


@njit(cache=True)
def _front_age(Hup, k, cd, ncell):
    """Age (steps) of the vehicle now at each link's exit, i.e. its travel time so far; free-flow if empty."""
    m = cd.shape[0]
    out = np.empty(m)
    for a in range(m):
        N = cd[a]
        if Hup[k, a] - N <= 1e-6:
            out[a] = ncell[a]
            continue
        lo, hi = 0, k  # first s with Hup[s, a] >= N
        while lo < hi:
            mid = (lo + hi) // 2
            if Hup[mid, a] >= N:
                hi = mid
            else:
                lo = mid + 1
        s = lo - 1 + (N - Hup[lo - 1, a]) / (Hup[lo, a] - Hup[lo - 1, a]) if lo > 0 else 0.0
        out[a] = max(ncell[a], k - s)
    return out


@njit(cache=True)
def _link_times(Hup, Hdn, ncell):
    """tau[s, a] (steps): FIFO travel time of a vehicle entering link a at time s, from the cumulative counts;
    at least free-flow; for vehicles still on the link at the horizon K a lower bound."""
    K = Hup.shape[0] - 1
    m = Hup.shape[1]
    tau = np.empty((K, m))
    for a in range(m):
        u = 0
        for s in range(K):
            N = Hup[s, a] - 1e-6
            while u <= K and Hdn[u, a] < N:
                u += 1
            if u > K:
                t = K + ncell[a] - s
            elif u == 0:
                t = 0.0
            else:
                t = u - 1 + (N - Hdn[u - 1, a]) / (Hdn[u, a] - Hdn[u - 1, a]) - s
            tau[s, a] = max(ncell[a], t)
    return tau


@njit(parallel=True, cache=True)
def _tdsp(tau, out_ptr, out_lnk, head, dests, c_end, alpha, B, rate, orig, T_load, aon):
    """Per destination, backward in time (tau >= 1 step): minimum cost-to-go C[s, v] and the expected one E under
    alpha[s // B]. Adds the time-dependent shortest-path next hops (averaged per bucket) to aon. Returns the
    demand-weighted sums of E and C over departures s < T_load (cost in steps)."""
    K = tau.shape[0]
    N = out_ptr.shape[0] - 1
    nd = dests.shape[0]
    se, sc = np.zeros(nd), np.zeros(nd)
    for b in prange(nd):
        d = dests[b]
        C, E = np.empty((K + 1, N)), np.empty((K + 1, N))
        C[K], E[K] = c_end[b], c_end[b]
        for s in range(K - 1, -1, -1):
            kb = s // B
            for v in range(N):
                if v == d:
                    C[s, v], E[s, v] = 0.0, 0.0
                    continue
                best, arg, ex = BIG, -1, 0.0
                for e in range(out_ptr[v], out_ptr[v + 1]):
                    a = out_lnk[e]
                    u, t = head[a], tau[s, a]
                    x = s + t
                    if x >= K:
                        cu, eu = C[K, u], E[K, u]
                    else:
                        i = int(x)
                        f = x - i
                        cu, eu = (1 - f) * C[i, u] + f * C[i + 1, u], (1 - f) * E[i, u] + f * E[i + 1, u]
                    if cu < BIG and t + cu < best:
                        best, arg = t + cu, a
                    ex += alpha[kb, b, a] * (t + eu)
                C[s, v], E[s, v] = best, ex if ex > 0 else best
                if arg >= 0:
                    aon[kb, b, arg] += 1.0 / B
        for s in range(T_load):
            for o in range(orig.shape[0]):
                if rate[o, b] > 0:
                    se[b] += rate[o, b] * E[s, orig[o]]
                    sc[b] += rate[o, b] * C[s, orig[o]]
    return se.sum(), sc.sum()


@njit(cache=True)
def _soft_alpha(indptr, head, lid, order, dff, t, theta, alpha):
    """Logit split rates over the downhill successors (as logit._dial, without the loading)."""
    N = indptr.shape[0] - 1
    V = np.empty(N)
    for b in range(order.shape[0]):
        df = dff[b]
        V[:] = np.inf
        for r in range(N):
            v = order[b, r]
            if v < 0:
                break
            if r == 0:
                V[v] = 0.0
                continue
            m = np.inf
            for e in range(indptr[v], indptr[v + 1]):
                u = head[e]
                if df[u] < df[v] and V[u] < np.inf:
                    m = min(m, t[lid[e]] + V[u])
            if m == np.inf:
                continue
            s = 0.0
            for e in range(indptr[v], indptr[v + 1]):
                u = head[e]
                if df[u] < df[v] and V[u] < np.inf:
                    s += np.exp(-theta * (t[lid[e]] + V[u] - m))
            V[v] = m - np.log(s) / theta
            for e in range(indptr[v], indptr[v + 1]):
                u = head[e]
                if df[u] < df[v] and V[u] < np.inf:
                    alpha[b, lid[e]] = np.exp(-theta * (t[lid[e]] + V[u] - V[v]))


def sp_alpha(G, c):
    """Split rates of the shortest-path next hops at link costs c."""
    nh = G.shortest(c, G.dest)[1]
    A = np.zeros((len(G.dest), G.m))
    b, v = np.nonzero(nh >= 0)
    A[b, G.links(v, nh[b, v])] = 1.0
    return A


def ue_alpha(G, X, c_ue):
    """Split rates of the per-destination UE flows X[d, link], restricted to the UE shortest-path DAG (drops the
    residual flow of the 1e-5 gap, which could close split-rate cycles); nodes without d-flow: UE next hop."""
    dist = G.shortest(c_ue, G.dest)[0]
    X = np.where(dist[:, G.g.head] < dist[:, G.tail], X, 0.0)
    out = np.stack([np.bincount(G.tail, X[b], G.N) for b in range(len(G.dest))])[:, G.tail]
    return np.where(out > 1e-9 * X.max(), X / np.maximum(out, 1e-300), sp_alpha(G, c_ue))


def cap_alpha(G, q, prices=False):
    """Static capacity-feasible plan: per-destination flows minimising total free-flow time subject to link flow <=
    capacity (multi-commodity LP), as split rates on the shortest-path DAG of fft + capacity prices (prices: also
    return the prices, min); None if no such routing exists."""
    from scipy.optimize import linprog
    import scipy.sparse as sp
    g, D, m, N = G.g, len(G.dest), G.m, G.N
    inc = sp.csr_matrix((np.r_[np.ones(m), -np.ones(m)], (np.r_[G.tail, g.head], np.r_[np.arange(m), np.arange(m)])), (N, m))
    b = np.zeros((D, N))
    for j, d in enumerate(G.dest):
        np.add.at(b[j], G.orig, q[:, j])
        b[j, d] -= q[:, j].sum()
    r = linprog(np.tile(g.fft, D), A_ub=sp.hstack([sp.identity(m)] * D), b_ub=g.cap, A_eq=sp.block_diag([inc] * D),
                b_eq=b.ravel(), method="highs")
    if r.status == 2:  # infeasible: demand above the network's concurrent-flow capacity, queues are unavoidable
        return None
    assert r.status == 0, r.message
    c = g.fft - r.ineqlin.marginals  # marginals <= 0 for binding capacities
    a = ue_alpha(G, r.x.reshape(D, m), c)
    return (a, -r.ineqlin.marginals) if prices else a


class Ctm:
    def __init__(self, G, Q, dt, factor=1.0, t_load=60.0, horizon=360.0, B=1, kappa=KAPPA, fifo=False, inc=()):
        """inc: incidents (link, t0, t1, factor): from t0 to t1 (min) the link's middle cell has factor x capacity
        (jam occupancy unchanged)."""
        g = G.g
        self.G, self.dt, self.kappa, self.B, self.fifo = G, dt, kappa, B, fifo
        self.ncell = np.maximum(1, np.rint(g.fft / dt)).astype(np.int64)
        self.first = np.r_[0, np.cumsum(self.ncell)[:-1]].astype(np.int64)
        self.cq = np.repeat(g.cap * dt / 60, self.ncell)
        self.head = g.head.astype(np.int64)
        o = np.argsort(self.head, kind="stable")
        self.in_ptr, self.in_lnk = np.searchsorted(self.head[o], np.arange(G.N + 1)), o
        o = np.argsort(G.tail, kind="stable")
        self.out_ptr, self.out_lnk = np.searchsorted(G.tail[o], np.arange(G.N + 1)), o
        z = len(G.dest)
        self.didx, self.oidx = np.full(G.N, -1), np.full(G.N, -1)
        self.didx[G.dest], self.oidx[G.orig] = np.arange(z), np.arange(z)
        self.rate, self.T_load = factor * Q * dt / 60, int(round(t_load / dt))
        self.K = int(np.ceil(horizon / dt / B)) * B
        self.total = self.rate.sum() * self.T_load
        self.inc = [(self.first[a] + self.ncell[a] // 2, round(t0 / dt), round(t1 / dt), f) for a, t0, t1, f in inc]

    def cq_at(self, k):
        """Cell capacities (veh per step) at step k."""
        cq = self.cq.copy()
        for c, k0, k1, f in self.inc:
            if k0 <= k < k1:
                cq[c] *= f
        return cq

    def run(self, policy, meter=None):
        """Load the network with policy(sim, k) -> alpha. meter(sim, k) -> veh per origin and destination released
        this step from a hold queue in front of the origin queue (holding at the origin blocks nobody); default:
        no hold. Returns veh h, unfinished share, clearance time (min)."""
        G, m, D = self.G, self.G.m, len(self.G.dest)
        meter = meter or getattr(policy, "meter", None)
        n, self.ntot = np.zeros((self.ncell.sum(), D)), np.zeros(self.ncell.sum())
        self.hold = np.zeros((D, D))
        oq, inbuf, cu, cd, dm, arr = np.zeros((D, D)), np.zeros((m, D)), np.zeros(m), np.zeros(m), np.zeros(m), np.zeros(D)
        self.Hup, self.Hdn, self.Hdm = np.zeros((self.K + 1, m)), np.zeros((self.K + 1, m)), np.zeros((self.K + 1, m))
        vh, peak = 0.0, 0.0
        for k in range(self.K):
            if k < self.T_load:
                (self.hold if meter else oq)[:] += self.rate
            if meter:
                r = np.minimum(meter(self, k), self.hold)
                self.hold -= r
                oq += r
            self.cqk = self.cq_at(k)
            _step(n, self.ntot, self.first, self.ncell, self.cqk, self.kappa * self.cq, self.in_ptr, self.in_lnk,
                  self.out_ptr, self.out_lnk, self.didx, self.oidx, oq, policy(self, k), inbuf, cu, cd, arr,
                  self.kappa, self.fifo, dm)
            self.Hup[k + 1], self.Hdn[k + 1], self.Hdm[k + 1] = cu, cd, dm
            left = self.ntot.sum() + oq.sum() + self.hold.sum()
            vh, peak = vh + left * self.dt / 60, max(peak, left)
            if k >= self.T_load and left < 1e-6 * self.total:
                self.Hup[k + 2:], self.Hdn[k + 2:], self.Hdm[k + 2:] = cu, cd, dm
                break
        assert abs(arr.sum() + left - self.total) < 1e-6 * self.total, "vehicles lost (incomplete split rates?)"
        return dict(vh=vh, left=left / self.total, clear=(k + 1) * self.dt, peak=peak)


class Reactive:
    """APDV on the current link times (see module doc)."""

    def __init__(self, sim, a_static, est="exit", soft=None, p=1.0, beta=1.0, U=1):
        self.a_static, self.est, self.soft, self.p, self.beta, self.U = a_static, est, soft, p, beta, U
        self.c, self.ar, self.alpha, self.change = None, None, a_static, []

    def __call__(self, sim, k):
        if k % self.U:
            return self.alpha
        if self.est == "exit":
            est = sim.dt * _front_age(sim.Hup, k, sim.Hdn[k], sim.ncell)
        else:
            est = sim.dt * np.add.reduceat(np.maximum(1.0, sim.ntot / sim.cq), sim.first)
        self.c = est if self.c is None else (1 - self.beta) * self.c + self.beta * est
        if self.soft is None:
            ar = sp_alpha(sim.G, self.c)
        else:
            sf, ar = self.soft, np.zeros_like(self.a_static)
            _soft_alpha(sf.indptr, sf.head, sf.lid, sf.order, sf.dist, self.c, sf.theta, ar)
        if self.ar is not None:  # share of the routed flow that changes link per update (per destination and node)
            self.change.append(np.abs(ar - self.ar).sum() / 2 / ar.sum())
        self.ar = ar
        self.alpha = (1 - self.p) * self.a_static + self.p * ar
        return self.alpha


class Price:
    """Price-based APDV. Every U steps each link feeds its offered inflow (sig 'dem': turn demands at its tail
    node) or measured inflow (sig 'in') into a virtual queue served at rho x capacity ([4]); price = g x the virtual queue's
    delay (min). APDV distances on base + price (base 'fft' or 'exit' times); every node
    moves a share p of its split rates to the current next hop, or with soft (a logit.Soft) to the logit split
    over its downhill successors (dyn: downhill w.r.t. the current distances, else soft's fixed ones). lam0: initial prices (warm start), else 0.
    prof[k, a]: a learned price profile (min, per step of the day) added to the within-day price; down: the
    within-day term may also be negative, down to -prof (the virtual queue is projected on price >= 0, not on >= prof).
    hold (origin holding): a second virtual queue per link, served at full capacity, estimates the real
    queue; a vehicle waits at its origin until it has waited hold x the delay those queues add to its shortest path
    (APDV can carry both distances). lmax: price cap (min), applied to the virtual queue too (anti-windup). eps (min): triggered updates; a link re-advertises its base
    time, price and queue delay only when one moved by more than eps since its last advertisement, and routing uses
    the advertised values. Then self.msg holds per period (links re-advertised, distance-vector messages: every node
    whose distance to a destination changed relays it to each predecessor). tmin: split shares below tmin are dropped
    and the rest renormalised (strict FIFO node model: any share toward a full link blocks the whole in-link)."""

    def __init__(self, a0, base="fft", g=1.0, rho=0.95, p=0.1, U=1, lam0=None, soft=None, sig="dem", dyn=False,
                 prof=None, down=False, hold=None, lmax=None, eps=None, tmin=None):
        self.a0, self.base, self.g, self.rho, self.p, self.U, self.lam0, self.lmax = a0, base, g, rho, p, U, lam0, lmax
        self.eps, self.msg, self.tmin = eps, [], tmin
        self.soft, self.sig, self.dyn, self.prof, self.down, self.hold = soft, sig, dyn, prof, down, hold
        self.meter = self.release if hold is not None else None

    def release(self, sim, k):
        """Release everyone who arrived at least P ago (FIFO per origin and destination)."""
        if k == 0:
            self.P, self.R = 0.0, np.zeros_like(sim.rate)
        r = np.maximum(sim.rate * np.clip(k + 1 - self.P / sim.dt, 0, sim.T_load) - self.R, 0.0)
        self.R += r
        return r

    def __call__(self, sim, k):
        q = self.rho * np.minimum.reduceat(sim.cqk, sim.first)  # virtual service per step (veh); a link knows its capacity
        if k == 0:
            self.v = np.zeros(sim.G.m) if self.lam0 is None else self.lam0 * q / (self.g * sim.dt)
            self.alpha = self.a0.copy()
        if k % self.U:
            return self.alpha
        if k == 0:
            self.v1 = np.zeros(sim.G.m)
        if k:
            H = sim.Hdm if self.sig == "dem" else sim.Hup
            lo = -self.prof[k] * q / (self.g * sim.dt) if self.down else 0.0
            self.v = np.maximum(self.v + H[k] - H[k - self.U] - self.U * q, lo)
            if self.lmax is not None and self.g > 0:  # anti-windup: above the queue-free limit a cut stays overloaded
                self.v = np.minimum(self.v, self.lmax * q / (self.g * sim.dt))
            self.v1 = np.maximum(self.v1 + sim.Hdm[k] - sim.Hdm[k - self.U] - self.U * q / self.rho, 0.0)
        c = sim.dt * (sim.ncell if self.base == "fft" else _front_age(sim.Hup, k, sim.Hdn[k], sim.ncell))
        self.lam = self.g * sim.dt * self.v / q + (0 if self.prof is None else self.prof[k])
        if self.lmax is not None:
            self.lam = np.minimum(self.lam, self.lmax)
        lam, d1 = self.lam, sim.dt * self.v1 * self.rho / q
        if self.eps is not None:
            if k == 0:
                self.adv, self.dists, self.indeg = [c, lam, d1], None, np.bincount(sim.G.g.head, minlength=sim.G.N)
            nl = 0
            for i, x in enumerate((c, lam, d1)):
                up = np.abs(x - self.adv[i]) > self.eps
                self.adv[i] = np.where(up, x, self.adv[i])
                nl = nl | up
            c, lam, d1 = self.adv
            nl = int(np.sum(nl)) if k else sim.G.m
        if self.soft is None:  # with p < 1, averaging successive SP trees can close cycles (flow circulates, isn't lost)
            ar = sp_alpha(sim.G, c + lam)
        else:
            sf, ar = self.soft, np.zeros_like(self.alpha)
            dist, order = sf.dag(c + lam) if self.dyn else (sf.dist, sf.order)
            _soft_alpha(sf.indptr, sf.head, sf.lid, order, dist, c + lam, sf.theta, ar)
        if self.tmin:  # strict FIFO: a small share toward a full link blocks the whole in-link, so drop shares < tmin
            ar = np.where(ar < self.tmin, 0.0, ar)
            tot = np.zeros((ar.shape[0], sim.G.N))
            np.add.at(tot, (slice(None), sim.G.tail), ar)
            tot = tot[:, sim.G.tail]
            ar = ar / np.where(tot > 0, tot, 1.0)
        self.alpha = (1 - self.p) * self.alpha + self.p * ar
        if self.hold is not None:
            G = sim.G
            d0, dq = G.shortest(c, G.dest)[0], G.shortest(c + d1, G.dest)[0]
            with np.errstate(invalid="ignore"):  # unreachable pairs: inf - inf, masked
                self.P = self.hold * np.where(np.isfinite(d0), dq - d0, 0.0)[:, G.orig].T
        if self.eps is not None:  # one ADV carries all distances of (node, destination)
            assert self.soft is not None and self.dyn, "counting needs the APDV distances"
            ds = [dist] + ([d0, dq] if self.hold is not None else [])
            ch = np.ones(dist.shape, bool) if self.dists is None else np.any([a != b for a, b in zip(ds, self.dists)], axis=0)
            self.dists = ds
            self.msg.append((nl, int((ch * self.indeg[None, :]).sum())))
        return self.alpha


def due(sim, a0, iters, log=None, b0=10.0, up=2.0, down=0.5):
    """Destination-based DUE on time-dependent split rates (buckets of sim.B steps), self-regulated averaging
    ([7]): step 1/b, b += up if the gap grew, else b += down; b0 > 1 since a0 (static UE) is a good
    start and plain MSA's first step (1/2) gridlocks. Returns the run's result, the gap history, the split rates."""
    G, B = sim.G, sim.B
    A = np.repeat(a0[None].astype(np.float32), sim.K // B, 0)
    c_end = np.where(np.isfinite(d := G.shortest(sim.ncell.astype(float), G.dest)[0]), d, BIG)
    gaps, b = [], b0
    for it in range(1, iters + 1):
        r = sim.run(lambda s, k: A[k // B])
        tau = _link_times(sim.Hup, sim.Hdn, sim.ncell)
        aon = np.zeros_like(A)
        se, sc = _tdsp(tau, sim.out_ptr, sim.out_lnk, sim.head, G.dest, c_end, A, B, sim.rate, G.orig, sim.T_load, aon)
        gaps.append((se - sc) / sc)
        if log:
            print(f"    DUE it {it}: veh h {r['vh']:.0f} gap {gaps[-1]:.2e}", file=log)
        b += up if len(gaps) > 1 and gaps[-1] > gaps[-2] else (down if len(gaps) > 1 else 0.0)
        A += (aon - A) / b
    return sim.run(lambda s, k: A[k // B]), gaps, A


def dso(sim, H, a_fb, log=True):
    """Lower bound on every routing strategy's veh h: the CTM system optimum ([3]) as an LP,
    multi-destination, on sim's cells, demand and steps, horizon H steps. Holding allowed, no FIFO, no terminal
    condition. Any run of sim, truncated at H, is feasible with the same veh h up to H: per destination, outflow <=
    occupancy; per cell, outflow <= Q and inflow <= min(Q, (N - n) / (kappa - 1)) at the step start; turn flows
    free; origin queue outflow <= queue. Returns veh h, unfinished share at H, the LP's time-dependent split
    rates A[k, d, link] (a_fb where a node sends no d-flow) and its origin departures R[k, origin, d] (veh per step)."""
    import highspy
    import scipy.sparse as sp
    G, D, K, kap = sim.G, len(sim.G.dest), H, sim.kappa
    C, m, Z = int(sim.ncell.sum()), G.m, sim.rate.shape[0]
    first, last = sim.first, sim.first + sim.ncell - 1
    yc = np.setdiff1d(np.arange(C), last)  # within-link moves c -> c + 1
    ins = [sim.in_lnk[sim.in_ptr[v]:sim.in_ptr[v + 1]] for v in range(G.N)]
    outs = [sim.out_lnk[sim.out_ptr[v]:sim.out_ptr[v + 1]] for v in range(G.N)]
    ta = np.concatenate([np.repeat(i, len(o)) for i, o in zip(ins, outs)])  # turns ta -> tb
    tb = np.concatenate([np.tile(o, len(i)) for i, o in zip(ins, outs)])
    sb = np.flatnonzero(sim.oidx[G.tail] >= 0)  # origin queue -> out-link
    ea = np.flatnonzero(sim.didx[sim.head] >= 0)  # in-link -> sink of its head's destination
    so, de = sim.oidx[G.tail[sb]], sim.didx[sim.head[ea]]
    W, T, Sn, En = len(yc), len(ta), len(sb), len(ea)
    nper = dict(st=C * D, y=W * D, z=T * D, s=Sn * D, e=En, q=Z * D)  # variables per step; st = stays in its cell
    voff = dict(zip(nper, np.r_[0, np.cumsum([K * n for n in nper.values()])[:-1]]))
    rper = dict(bal=C * D, org=Z * D, out=C, inn=C, jam=C)  # rows per step
    roff = dict(zip(rper, np.r_[0, np.cumsum([K * n for n in rper.values()])[:-1]]))
    dd = np.arange(D)
    pd = lambda r, v: ((r[:, None] * D + dd).ravel(), (v[:, None] * D + dd).ravel())  # per destination
    ag = lambda r, v: (np.repeat(r, D), (v[:, None] * D + dd).ravel())  # summed over destinations
    aW, aT, aS, aC, aZ = np.arange(W), np.arange(T), np.arange(Sn), np.arange(C), np.arange(Z)
    w = 1 / (kap - 1)
    E = [  # (row type, (row, var), var type, coef, lag); n(c, k) = st(c, k-1) + inflow(c, k-1)
        # balance: outflow(k) + st(k) = st(k-1) + inflow(k-1)
        ("bal", pd(yc, aW), "y", 1, 0), ("bal", pd(last[ta], aT), "z", 1, 0), ("bal", (last[ea] * D + de, np.arange(En)), "e", 1, 0),
        ("bal", pd(aC, aC), "st", 1, 0), ("bal", pd(aC, aC), "st", -1, 1),
        ("bal", pd(yc + 1, aW), "y", -1, 1), ("bal", pd(first[tb], aT), "z", -1, 1), ("bal", pd(first[sb], aS), "s", -1, 1),
        # origin queues: q(k) = q(k-1) + rate - departures(k)
        ("org", pd(aZ, aZ), "q", 1, 0), ("org", pd(aZ, aZ), "q", -1, 1), ("org", pd(so, aS), "s", 1, 0),
        ("out", ag(yc, aW), "y", 1, 0), ("out", ag(last[ta], aT), "z", 1, 0), ("out", (last[ea], np.arange(En)), "e", 1, 0),
        ("inn", ag(yc + 1, aW), "y", 1, 0), ("inn", ag(first[tb], aT), "z", 1, 0), ("inn", ag(first[sb], aS), "s", 1, 0),
        ("jam", ag(yc + 1, aW), "y", 1, 0), ("jam", ag(first[tb], aT), "z", 1, 0), ("jam", ag(first[sb], aS), "s", 1, 0),
        ("jam", ag(yc + 1, aW), "y", w, 1), ("jam", ag(first[tb], aT), "z", w, 1), ("jam", ag(first[sb], aS), "s", w, 1),
        ("jam", ag(aC, aC), "st", w, 1),
    ]
    rows, cols, vals = [], [], []
    for rt, (rl, vl), vt, coef, lag in E:
        ks = np.arange(lag, K)[:, None]
        rows.append((roff[rt] + ks * rper[rt] + rl).ravel())
        cols.append((voff[vt] + (ks - lag) * nper[vt] + vl).ravel())
        vals.append(np.full(rows[-1].size, float(coef)))
    nv, nr = voff["q"] + K * nper["q"], roff["jam"] + K * C
    A = sp.csc_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))), shape=(nr, nv))
    del rows, cols, vals
    inf, ks = highspy.kHighsInf, np.arange(K)[:, None]
    org = np.where(ks < sim.T_load, sim.rate.ravel(), 0.0).ravel()
    rlo = np.r_[np.zeros(K * C * D), org, np.full(3 * K * C, -inf)]
    cqk = np.concatenate([sim.cq_at(k) for k in range(K)])
    rhi = np.r_[np.zeros(K * C * D), org, cqk, cqk, np.tile(kap * sim.cq * w, K)]
    ub = np.full(nv, inf)
    t = np.flatnonzero(sim.didx[sim.head[ta]] >= 0)  # d-flow at node d leaves to the sink only
    ub[(voff["z"] + ks * nper["z"] + t * D + sim.didx[sim.head[ta[t]]]).ravel()] = 0.0
    cost = np.full(nv, sim.dt / 60)
    cost[voff["e"]:voff["e"] + K * En] = 0.0
    lp = highspy.HighsLp()
    lp.num_col_, lp.num_row_ = nv, nr
    lp.col_cost_, lp.col_lower_, lp.col_upper_, lp.row_lower_, lp.row_upper_ = cost, np.zeros(nv), ub, rlo, rhi
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    lp.a_matrix_.num_col_, lp.a_matrix_.num_row_ = nv, nr
    lp.a_matrix_.start_, lp.a_matrix_.index_, lp.a_matrix_.value_ = A.indptr, A.indices, A.data
    del A
    h = highspy.Highs()
    h.setOptionValue("output_flag", log)
    h.passModel(lp)
    h.setOptionValue("solver", "pdlp")  # first-order LP solver of HiGHS ([10]); IPX for tighter gaps
    h.setOptionValue("threads", 1)
    h.run()
    assert h.getModelStatus() == highspy.HighsModelStatus.kOptimal, h.modelStatusToString(h.getModelStatus())
    x = np.asarray(h.getSolution().col_value)
    blk = lambda vt: x[voff[vt]:voff[vt] + K * nper[vt]].reshape(K, -1)
    left = blk("st")[-1].sum() + blk("y")[-1].sum() + blk("z")[-1].sum() + blk("s")[-1].sum() + blk("q")[-1].sum()
    F = np.zeros((K, m, D))  # d-flow entering each link per step
    np.add.at(F, (slice(None), tb), blk("z").reshape(K, T, D))
    np.add.at(F, (slice(None), sb), blk("s").reshape(K, Sn, D))
    tot = np.zeros((K, G.N, D))
    np.add.at(tot, (slice(None), G.tail), F)
    tot = tot[:, G.tail]
    Asp = np.where(tot > 1e-9, F / np.maximum(tot, 1e-300), a_fb.T[None]).transpose(0, 2, 1)
    R = np.zeros((K, Z, D))
    np.add.at(R, (slice(None), so), blk("s").reshape(K, Sn, D))
    return h.getInfo().objective_function_value, left / sim.total, Asp, R


def check_dso():
    """Light load: the DSO bound equals the free-flow run exactly (same cells, steps and veh h accounting)."""
    g = net.load("SiouxFalls")
    G, Q = S.Graph(g, g.ftn), S.load_trips(g)
    sim = Ctm(G, Q, 1.0, factor=0.02, t_load=3, horizon=40)
    a = sp_alpha(G, sim.ncell.astype(float))
    r, (lb, left, _, _) = sim.run(lambda s, k: a), dso(sim, sim.K, a, log=False)
    assert left < 1e-6 and abs(lb - r["vh"]) < 1e-6 * r["vh"], (lb, r["vh"], left)
    inc = Ctm(G, Q, 1.0, factor=0.02, t_load=3, horizon=40,
              inc=[(int(np.argmax(sim.Hup[-1])), 0, 10, 0.05)])  # capacity factor 0.05 keeps the LP well conditioned
    ri, lbi = inc.run(lambda s, k: a)["vh"], dso(inc, inc.K, a, log=False)[0]
    assert lb < lbi <= ri * (1 + 1e-6), (lb, lbi, ri)  # the incident binds in the sim and in the LP
    print(f"check ok: light-load DSO bound {lb:.4f} = free-flow run {r['vh']:.4f} veh h; "
          f"incident: bound {lbi:.4f} <= run {ri:.4f}")


def check():
    q = _gnm(np.array([10.0, 10.0]), np.array([20.0, 10.0]), np.array([[1.0], [1.0]]), np.array([6.0]))
    assert np.allclose(q, [4, 2]), q  # merge: capacity-proportional
    q = _gnm(np.array([10.0]), np.array([10.0]), np.array([[0.5, 0.5]]), np.array([2.0, 10.0]))
    assert np.allclose(q, [4]), q  # diverge: FIFO, the blocked turn holds the whole link
    q = _gnm(np.array([10.0, 1.0]), np.array([10.0, 10.0]), np.array([[1.0], [1.0]]), np.array([6.0]))
    assert np.allclose(q, [5, 1]), q  # demand-constrained in-link gets its demand, the rest the remaining supply
    r = _turn_ratio(np.array([10.0]), np.array([[0.5, 0.5]]), np.array([2.0, 10.0]))
    assert np.allclose(r, [0.4, 1]), r  # non-FIFO diverge: only the blocked turn is held
    g = net.load("Anaheim")  # light load, free-flow routes: mean trip time = mean free-flow distance (in cells)
    G, Q = S.Graph(g, g.zones), S.load_trips(g)
    sim = Ctm(G, Q, DT["Anaheim"], factor=0.05, t_load=20, horizon=60)
    r = sim.run(lambda s, k, A=sp_alpha(G, sim.ncell.astype(float)): A)
    dist = G.shortest(sim.ncell.astype(float), G.dest)[0]
    ff = (Q * dist[:, G.orig].T).sum() / Q.sum() * sim.dt
    mean = r["vh"] * 60 / sim.total
    assert abs(mean - ff) < 2 * sim.dt, (mean, ff)
    assert np.allclose(sim.Hdm, sim.Hup)  # nothing blocked: offered inflow = inflow
    pol = Price(sp_alpha(G, sim.ncell.astype(float)), g=3.0, rho=1.0, p=1.0)
    assert np.isclose(sim.run(pol)["vh"], r["vh"], rtol=1e-12) and pol.lam.max() == 0  # below capacity: no price, free-flow routes (ties may break differently)
    tr, prof = learn(sim, lambda P: Price(pol.a0, g=0.0, rho=1.0, p=1.0, prof=P), 2, 1.0, 1.0)
    assert prof.max() == 0 and np.allclose(tr, r["vh"] * 60 / sim.total, rtol=1e-12)  # nor a learned one
    sf, mk = logit.Soft(G, Q, 3.0, G.g.fft.copy()), lambda e: Price(pol.a0, "exit", 3.0, 0.95, 1.0, U=20, soft=sf, dyn=True, eps=e)
    a, p0, pb = sim.run(Price(pol.a0, "exit", 3.0, 0.95, 1.0, U=20, soft=sf, dyn=True))["vh"], mk(0.0), mk(1e9)
    assert sim.run(p0)["vh"] == a and p0.msg[0] == (G.m, len(G.dest) * G.m)  # eps 0: exact; period 0 advertises all
    sim.run(pb)
    assert all(x == (0, 0) for x in pb.msg[1:])  # nothing re-advertised, nothing relayed
    pt = Price(pol.a0, "exit", 3.0, 0.95, 1.0, soft=logit.Soft(G, Q, 0.3, G.g.fft.copy()), dyn=True, tmin=0.1)
    sim.run(pt)
    tot = np.zeros((len(G.dest), G.N))
    np.add.at(tot, (slice(None), G.tail), pt.alpha)
    assert np.all((pt.alpha == 0) | (pt.alpha >= 0.1)) and np.allclose(tot[tot > 0], 1)  # pruned, renormalised
    assert np.any((pt.alpha > 0) & (pt.alpha < 1))  # some node still splits
    print(f"check ok: node model; light-load mean trip {mean:.3f} min vs free-flow {ff:.3f} min; no price; triggered updates; pruning")


def setup(name, factor):
    """Graph, demand, and the static UE at the scaled demand: link costs, split rates; free-flow SP split rates."""
    g = net.load(name)
    G, Q = S.Graph(g, g.zones if g.zones < g.n else g.ftn), S.load_trips(g)
    X = S.cfw(G, factor * Q, S.Cost(g, False), tol=1e-5, per_dest=True)[0]
    c_ue = g.bpr(X.sum(0))
    return G, Q, c_ue, ue_alpha(G, X, c_ue), sp_alpha(G, g.fft.copy())



def dso_compare(name, factor, dt, horizon, due_iters, ps=(0.1, 0.2, 0.3, 0.5), log=sys.stderr):
    """The strategies and DUE at step dt against the DSO lower bound on the same cells; the LP horizon is 1.1x the
    fastest clearance. Returns the bound (veh h, unfinished share at H), rows {strategy: run}, total veh."""
    G, Q, c_ue, a_ue, a_ff = setup(name, factor)
    sim, soft = Ctm(G, Q, dt, factor=factor, horizon=horizon), logit.Soft(G, Q, 1.0, c_ue)
    pols = {"UE routes (static)": lambda s, k: a_ue, "APDV: exact, exit times": Reactive(None, a_ue, "exit"),
            "exact, occupancy times": Reactive(None, a_ue, "occ"), "soft th=1": Reactive(None, a_ue, "exit", soft=soft)}
    pols |= {f"exact, p={p}": Reactive(None, a_ue, "exit", p=p) for p in ps}
    X = S.cfw(G, factor * Q, S.Cost(G.g, True), tol=1e-5, per_dest=True)[0]
    a_so, a_cap = ue_alpha(G, X, S.Cost(G.g, True)(X.sum(0))), cap_alpha(G, factor * Q)
    pols["SO routes (static BPR, marginal costs)"] = lambda s, k: a_so
    if a_cap is not None:
        pols["capacity-feasible routes (static LP)"] = lambda s, k: a_cap
    rows = {}
    for lab, pol in pols.items():
        rows[lab] = sim.run(pol)
        print(f"  {name} x{factor} dt={dt} {lab}: {rows[lab]['vh'] * 60 / sim.total:.2f} min", file=log, flush=True)
    rows["DUE (central, predictive)"] = due(sim, a_ue, due_iters, log)[0]
    H = min(sim.K, int(1.1 * min(r["clear"] for r in rows.values()) / dt))
    t0 = time.perf_counter()
    lb, left, A, _ = dso(sim, H, a_ue)
    print(f"  {name} x{factor} DSO bound {lb * 60 / sim.total:.2f} min, left {left:.1e}, H {H} "
          f"({time.perf_counter() - t0:.0f}s)", file=log, flush=True)
    rows["DSO split rates replayed (no holding)"] = sim.run(lambda s, k: A[min(k, H - 1)])
    return (lb, left, H), rows, sim.total


def learn(sim, make, days, gd, rho, log=None, avg_from=None):
    """Day-to-day price learning: day n runs make(prof) (a Price using the profile); then per link and step of the
    day prof <- [prof + gd (offered / (rho cap) - 1)]+, the static price map per time bucket with one day as the
    period (gd in min per day). sim: a Ctm, or day n -> Ctm (demand varying by day, same steps). Returns the mean
    trip per day and the last profile, or with avg_from the mean of the profiles after days avg_from..days."""
    day = sim if callable(sim) else (lambda n: sim)
    s0 = day(0)
    q, prof, trips, acc = rho * s0.G.g.cap * s0.dt / 60, np.zeros((s0.K, s0.G.m)), [], []
    for n in range(days):
        sim = day(n)
        trips.append(sim.run(make(prof))["vh"] * 60 / sim.total)
        prof = np.maximum(prof + gd * (np.diff(sim.Hdm, axis=0) / q - 1), 0)
        if avg_from is not None and n + 1 >= avg_from:
            acc.append(prof)
        if log:
            print(f"    day {n + 1}: {trips[-1]:.2f} min, max price {prof.max():.1f}", file=log, flush=True)
    return np.array(trips), np.mean(acc, axis=0) if acc else prof


DSO_SF = {0.3: 8.9193, 0.4: 9.1068, 0.5: 9.4286, 0.6: 10.82, 0.7: 13.438}  # DSO bounds at dt = 1 (mean trip, min; python dnl.py dso SiouxFalls 1 F)



GRID = {  # net -> demand factors, horizon (min), DUE bucket (steps), DUE iterations
    "SiouxFalls": ((0.3, 0.4, 0.5, 0.6), 600, 2, 40),
    "Anaheim": ((0.8, 1.0, 1.2), 400, 20, 30),
    "ChicagoSketch": ((0.75, 1.0), 360, 20, 20),
}



if __name__ == "__main__":
    if sys.argv[1:2] == ["dso"]:  # dso NAME DT FACTOR...: strategies vs the DSO lower bound
        check_dso()
        name, dt, fs = sys.argv[2], float(sys.argv[3]), [float(f) for f in sys.argv[4:]]
        _, hor, _, it = GRID[name]
        print(f"\n**{name} at dt = {dt} min: mean trip (min) and / DSO lower bound**\n")
        print("| strategy | " + " | ".join(f"x{f}" for f in fs) + " |")
        print("|" + "---|" * (len(fs) + 1))
        res = [dso_compare(name, f, dt, hor, it) for f in fs]
        trip = lambda r, tot: r["vh"] * 60 / tot
        print("| **DSO lower bound** (unfinished at H) | " + " | ".join(
            f"{b[0] * 60 / tot:.2f} ({b[1]:.0e})" for b, _, tot in res) + " |")
        for lab in dict.fromkeys(k for _, rw, _ in res for k in rw):
            print(f"| {lab} | " + " | ".join(f"{trip(rw[lab], tot):.2f} / {rw[lab]['vh'] / b[0]:.2f}"
                                             + ("*" if rw[lab]["left"] > 1e-3 else "") if lab in rw else "-"
                                             for b, rw, tot in res) + " |")
        sys.exit()
    check()
