"""Static assignment on TNTP networks with BPR costs: UE and SO by conjugate Frank-Wolfe ([6] in README.md).
Flows veh/h, times min.
"""
import re
import sys
import time

import numpy as np
import scipy.sparse as sp
import scipy.sparse.csgraph as csg

import net

W_EPS = 1e-9  # csgraph: keep zero-time connectors as (tiny) edges

def load_trips(g):
    text = (net.DATA / net.NETS[g.name].replace("_net", "_trips")).read_text()
    Q = np.zeros((g.zones, g.zones))
    for blk in text.split("Origin")[1:]:
        m = re.match(r"\s*(\d+)", blk)
        for d, v in re.findall(r"(\d+)\s*:\s*([0-9.eE+-]+)", blk[m.end():]):
            Q[int(m.group(1)) - 1, int(d) - 1] += float(v)
    np.fill_diagonal(Q, 0)
    return Q



class Cost:
    """BPR travel time (UE) or marginal cost (SO): cost, its derivative, and the objective it is the gradient of."""

    def __init__(self, g, so):
        self.f, self.b, self.c, self.p, self.k = g.fft, g.b, g.cap, g.power, (g.power + 1 if so else 1)
        self.so = so

    def __call__(self, x):
        return self.f * (1 + self.k * self.b * (x / self.c) ** self.p)

    def d(self, x):
        p = self.p
        return np.where(p > 0, self.k * self.f * self.b * p * (x / self.c) ** np.maximum(p - 1, 0) / self.c, 0.0)

    def obj(self, x):
        t = self.f * (1 + self.b * (x / self.c) ** self.p)
        return x @ t if self.so else (self.f * x * (1 + self.b * (x / self.c) ** self.p / (self.p + 1))).sum()


class Graph:
    """Routing graph with centroids split (in-copy = destination, out-copy n+c = origin), link ids kept."""

    def __init__(self, g, ftn):
        assert len(np.unique(g.tail * g.n + g.head)) == g.m, "parallel links"
        self.g, self.m = g, g.m
        self.tail = np.where(g.tail < ftn, g.n + g.tail, g.tail)
        self.N = N = g.n + ftn
        z = np.arange(g.zones)
        self.orig, self.dest = np.where(z < ftn, g.n + z, z), z
        T = sp.csr_matrix((np.arange(1, g.m + 1, dtype=float), (self.tail, g.head)), shape=(N, N))
        self.lid = T.data.astype(np.int64) - 1  # csr order -> link id
        self.key = self.tail[self.lid] * N + g.head[self.lid]  # sorted (csr order)
        Tt = T.T.tocsr()
        self.Tt, self.lidT = Tt, Tt.data.astype(np.int64) - 1

    def reverse(self, c):
        Wt = self.Tt.copy()
        Wt.data = np.maximum(c[self.lidT], W_EPS)
        return Wt

    def links(self, v, u):
        return self.lid[np.searchsorted(self.key, v * self.N + u)]

    def demand(self, Q, ds):
        D = np.zeros((len(ds), self.N))
        D[:, self.orig] = Q[:, ds].T
        return D

    def load(self, nh, D, ds, c=None, per_dest=False):
        """Push demand D[b, v] (v -> ds[b]) along next hops nh[b, v] (< 0: none). Returns link flows and, if c is
        given, the cost-to-go along nh. Asserts that every node with demand reaches its destination (no loops)."""
        B, N = nh.shape
        rows = np.arange(B)[:, None]
        has = nh >= 0
        lk = np.where(has, self.links(np.arange(N)[None, :], np.where(has, nh, 0)), -1)
        anc, dep = np.where(has, nh, np.arange(N)), has.astype(np.int64)
        cost = np.where(has, c[np.maximum(lk, 0)], 0.0) if c is not None else None
        for _ in range(int(np.ceil(np.log2(N))) + 1):  # pointer doubling: hop depth (and cost-to-go)
            if c is not None:
                cost = cost + cost[rows, anc]
            dep, anc = dep + dep[rows, anc], anc[rows, anc]
        assert (anc[D > 0] == np.broadcast_to(ds[:, None], D.shape)[D > 0]).all(), "demand does not reach d"
        s = D.copy()
        for L in range(dep.max(), 0, -1):
            b, v = np.nonzero(dep == L)
            np.add.at(s, (b, nh[b, v]), s[b, v])
        b, v = np.nonzero(has & (s > 0))
        if per_dest:
            X = np.zeros((B, self.m))
            np.add.at(X, (b, lk[b, v]), s[b, v])
            return X, cost
        return np.bincount(lk[b, v], weights=s[b, v], minlength=self.m), cost

    def shortest(self, c, ds):
        dist, pred = csg.dijkstra(self.reverse(c), indices=ds, return_predecessors=True)
        return dist, np.where(pred >= 0, pred, -1)

    def assign(self, Q, c, rule=None, batch=128, with_cost=False, per_dest=False):
        """All-or-nothing loading for routing rule (None = shortest paths). Returns flows (per destination: [d, link]),
        sum q*dist (SP), sum q*cost."""
        x, spq, ruleq = np.zeros((len(self.dest), self.m) if per_dest else self.m), 0.0, 0.0
        for i in range(0, len(self.dest), batch):
            ds = self.dest[i:i + batch]
            dist, nh = self.shortest(c, ds)
            D = self.demand(Q, ds)
            spq += (D * np.where(D > 0, dist, 0)).sum()
            if rule is not None:
                nh = rule(self, c, ds, nh, dist)
            y, cg = self.load(nh, D, ds, c if with_cost else None, per_dest)
            if per_dest:
                x[i:i + batch] = y
            else:
                x += y
            if with_cost:
                ruleq += (D * cg).sum()
        return x, spq, ruleq


def line_search(cost, x, d, it=40):
    lo, hi = 0.0, 1.0
    if cost(x + d) @ d <= 0:
        return 1.0
    for _ in range(it):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if cost(x + mid * d) @ d < 0 else (lo, mid)
    return (lo + hi) / 2


def cfw(G, Q, cost, tol=1e-5, iters=3000, delta=0.01, per_dest=False):
    """Conjugate Frank-Wolfe. Returns flows (per destination: [d, link]), relative gap, iterations."""
    agg = (lambda X: X.sum(0)) if per_dest else (lambda X: X)
    X = G.assign(Q, cost(np.zeros(G.m)), per_dest=per_dest)[0]
    Xbar = None
    for k in range(1, iters + 1):
        x = agg(X)
        c = cost(x)
        Y, spq, _ = G.assign(Q, c, per_dest=per_dest)
        y = agg(Y)
        gap = (c @ x - spq) / (c @ x)
        if gap < tol:
            break
        S_ = Y
        if Xbar is not None:
            xbar = agg(Xbar)
            H, db = cost.d(x), xbar - x
            num, den = db @ (H * (y - x)), db @ (H * (y - xbar))
            a = num / den if den != 0 else 0.0
            a = 1 - delta if a > 1 - delta else (a if a >= 0 else 0.0)
            S_ = a * Xbar + (1 - a) * Y
        X = X + line_search(cost, x, agg(S_) - x) * (S_ - X)
        Xbar = S_
    return X, gap, k



