"""Logit splitting over the downhill successors at every node (efficient links, [9] in README.md); loop-free,
since the distance to the destination strictly decreases along every split."""
import sys
import time

import numpy as np
from numba import njit
from scipy.sparse.linalg import LinearOperator, eigsh

import net
import static as S


@njit(cache=True)
def _dial(indptr, head, lid, order, dff, dests, dem, t, theta, x):
    """Logit split over efficient out-links (dff[u] < dff[v]) at every node, all destinations; adds flows to x."""
    N = indptr.shape[0] - 1
    V = np.empty(N)
    f = np.empty(N)
    for b in range(dests.shape[0]):
        d, df = dests[b], dff[b]
        V[:] = np.inf
        V[d] = 0.0
        for r in range(N):  # ascending free-flow distance: successors first
            v = order[b, r]
            if v < 0:
                break
            if v == d:
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
        f[:] = dem[b]
        for r in range(N - 1, -1, -1):  # descending: push flow toward d
            v = order[b, r]
            if v < 0 or v == d or f[v] == 0.0 or V[v] == np.inf:
                continue
            for e in range(indptr[v], indptr[v + 1]):
                u = head[e]
                if df[u] < df[v] and V[u] < np.inf:
                    q = f[v] * np.exp(-theta * (t[lid[e]] + V[u] - V[v]))
                    x[lid[e]] += q
                    f[u] += q


class Soft:
    """Soft-splitting loader L(c) over the successors that are downhill w.r.t. the distances at costs c_dag."""

    def __init__(self, G, Q, theta, c_dag):
        o = np.argsort(G.tail, kind="stable")
        self.indptr = np.searchsorted(G.tail[o], np.arange(G.N + 1))
        self.head, self.lid = G.g.head[o], o
        self.G, self.dem, self.dests, self.theta, self.m = G, G.demand(Q, G.dest), G.dest, theta, G.m
        self.dist, self.order = self.dag(c_dag)

    def dag(self, c):
        dist = self.G.shortest(c, self.dests)[0]
        order = np.argsort(dist, axis=1, kind="stable")
        return dist, np.where(np.isfinite(np.take_along_axis(dist, order, 1)), order, -1)

    def __call__(self, c):
        x = np.zeros(self.m)
        _dial(self.indptr, self.head, self.lid, self.order, self.dist, self.dests, self.dem, c, self.theta, x)
        return x



