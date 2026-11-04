"""Dominator tree, strongly connected components, strong bridges and strong articulation points with few queries.

The algorithm of ../README.md. Every read of the graph goes through G, which counts oracle applications of BBHT and
Durr-Hoyer sampled from the exact Grover law, each stopping after budget * sqrt(N) as a device would. All other work
uses classical data and costs no queries. mode "matrix" searches all n vertices; mode "array" searches the list of the
vertex, as out- and in-lists. No circuits here; see qiskit_check.py.
Limits: statistical; counts on these families carry no guarantee beyond ../README.md.
"""
import math
import numpy as np


class G:
    def __init__(self, A, rng, mode="matrix", budget=16):
        self.A, self.rng, self.mode, self.budget = A.astype(bool), rng, mode, budget
        self.n = len(A)
        self.apps = 0
        self.lists = {1: [np.flatnonzero(self.A[v]) for v in range(self.n)], -1: [np.flatnonzero(self.A[:, v]) for v in range(self.n)]}

    def candidates(self, v, d):
        """Entries a search at v in direction d runs over: (vertices, present)."""
        if self.mode == "matrix":
            return np.arange(self.n), (self.A[v] if d == 1 else self.A[:, v])
        c = self.lists[d][v]
        return c, np.ones(len(c), dtype=bool)

    def search(self, v, d, good):
        """A random entry at v in direction d, present, whose vertex satisfies good; or None after the budget."""
        c, present = self.candidates(v, d)
        N = len(c)
        if N == 0:
            return None
        hits = np.flatnonzero(present & good[c])
        t = len(hits)
        theta = math.asin(math.sqrt(t / N))
        limit, m, spent = self.budget * math.sqrt(N), 1.0, 0
        while spent <= limit:
            j = int(self.rng.integers(0, int(m)))
            spent += 2 * j + 1
            if t and self.rng.random() < math.sin((2 * j + 1) * theta) ** 2:
                self.apps += spent
                return int(c[hits[self.rng.integers(t)]])
            m = min(m * 8 / 7, math.sqrt(N) + 1)
        self.apps += spent
        return None

    def minimum(self, v, d, value):
        """Durr-Hoyer: the smallest value[x] over entries x at v in direction d. value = inf is never returned."""
        c, present = self.candidates(v, d)
        N = len(c)
        if N == 0:
            return None
        f = np.where(present, value[c], np.inf)
        cur = int(self.rng.integers(N))
        limit, spent = self.budget * math.sqrt(N), 1
        while spent <= limit:
            better = np.flatnonzero(f < f[cur])
            t = len(better)
            theta = math.asin(math.sqrt(t / N))
            m, found = 1.0, False
            while not found and spent <= limit:
                j = int(self.rng.integers(0, int(m)))
                spent += 2 * j + 1
                found = t > 0 and self.rng.random() < math.sin((2 * j + 1) * theta) ** 2
                m = min(m * 8 / 7, math.sqrt(N) + 1)
            if found:
                cur = int(better[self.rng.integers(t)])
        self.apps += spent
        return f[cur] if np.isfinite(f[cur]) else None


def dfs(g, root, d=1, allowed=None, visited=None):
    """Depth-first search by repeated search for an unvisited neighbour. Returns preorder, finish order, parent."""
    n = g.n
    visited = np.zeros(n, dtype=bool) if visited is None else visited
    good = ~visited if allowed is None else (~visited & allowed)
    parent = np.full(n, -1)
    pre, post, stack = [root], [], [root]
    visited[root], good[root] = True, False
    while stack:
        v = stack[-1]
        x = g.search(v, d, good)
        if x is None:
            post.append(stack.pop())
        else:
            visited[x], good[x] = True, False
            parent[x] = v
            pre.append(x)
            stack.append(x)
    return pre, post, parent


def dominators(g, root, d=1, allowed=None):
    """idom in the flow graph from root along direction d, on the vertices reached; idom[root] = root, -1 if unreached."""
    n = g.n
    pre, _, parent = dfs(g, root, d, allowed)
    dfn = np.full(n, n + 1)
    dfn[pre] = np.arange(len(pre))
    semi = dfn.astype(float)
    # forest of processed vertices; label[v] = vertex of smallest semi on the path to the forest root
    anc, label = np.full(n, -1), np.arange(n)

    def evaluate(v):
        path = []
        while anc[v] != -1 and anc[anc[v]] != -1:
            path.append(v)
            v = anc[v]
        for x in reversed(path):
            if semi[label[anc[x]]] < semi[label[x]]:
                label[x] = label[anc[x]]
            anc[x] = anc[anc[x]]
        return label[path[0]] if path else label[v]

    for w in reversed(pre[1:]):
        # value of predecessor v: its own number if below w, else the smallest semi on its forest path. No queries.
        value = np.full(n, np.inf)
        cands = g.candidates(w, -d)[0]
        for v in cands:
            if dfn[v] <= n and (allowed is None or allowed[v]):
                value[v] = dfn[v] if dfn[v] < dfn[w] else semi[evaluate(int(v))]
        s = g.minimum(w, -d, value)
        semi[w] = dfn[parent[w]] if s is None else min(s, dfn[parent[w]])  # the tree edge is an entry, guards against a miss
        anc[w] = parent[w]
    idom = np.full(n, -1)
    idom[root] = root
    for w in pre[1:]:  # semidominators give idom as a nearest common ancestor, no queries (Georgiadis)
        u = parent[w]
        while dfn[u] > semi[w]:
            u = idom[u]
        idom[w] = u
    return idom, dfn


def components(g):
    """Strongly connected components by Kosaraju: two rounds of depth-first search."""
    visited, order = np.zeros(g.n, dtype=bool), []
    for r in range(g.n):
        if not visited[r]:
            order += dfs(g, r, 1, None, visited)[1]
    visited, comps = np.zeros(g.n, dtype=bool), []
    for r in reversed(order):
        if not visited[r]:
            comps.append(sorted(dfs(g, r, -1, None, visited)[0]))
    return comps


def intervals(idom, dfn):
    """Entry and exit numbers of the dominator tree, so that a dominance test costs no queries."""
    n = len(idom)
    kids = [[] for _ in range(n)]
    roots = []
    for v in range(n):
        if idom[v] == v:
            roots.append(v)
        elif idom[v] != -1:
            kids[idom[v]].append(v)
    a, b, t = np.zeros(n, dtype=int), np.zeros(n, dtype=int), 0
    for r in roots:
        stack = [(r, 0)]
        while stack:
            v, i = stack.pop()
            if i == 0:
                a[v] = t
                t += 1
            if i < len(kids[v]):
                stack.append((v, i + 1))
                stack.append((kids[v][i], 0))
            else:
                b[v] = t
    return a, b


def bridges(g, root, d, allowed):
    """Bridges of the flow graph: (idom(v), v) when every other predecessor of v is dominated by v."""
    idom, dfn = dominators(g, root, d, allowed)
    a, b = intervals(idom, dfn)
    out = []
    for v in np.flatnonzero(allowed):
        if v == root or idom[v] == -1:
            continue
        good = allowed & (idom != -1) & ~((a >= a[v]) & (a < b[v]))  # reachable predecessors not dominated by v
        good[idom[v]] = False
        if g.search(int(v), -d, good) is None:
            out.append((int(idom[v]), int(v)) if d == 1 else (int(v), int(idom[v])))
    return out, idom


def strong(g):
    """Strong bridges and strong articulation points of the whole graph."""
    B, P = set(), set()
    for comp in components(g):
        if len(comp) < 2:
            continue
        allowed = np.zeros(g.n, dtype=bool)
        allowed[comp] = True
        s = comp[0]
        for d in (1, -1):
            br, idom = bridges(g, s, d, allowed)
            B.update(br)
            P.update(int(x) for x in idom[comp] if x != s)
        if len(comp) > 2:
            rest = allowed.copy()
            rest[s] = False
            r = int(np.flatnonzero(rest)[0])
            ok = all(len(dfs(g, r, d, rest)[0]) == len(comp) - 1 for d in (1, -1))
            if not ok:
                P.add(s)
    return B, P
