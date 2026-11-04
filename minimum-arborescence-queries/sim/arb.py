"""Minimum-cost arborescence by Edmonds contraction with quantum minimum finding.

The algorithm of ../README.md. Everything that touches the weights goes through build(),
which is the "d smallest values of different type" problem of Durr et al., Theorem 6.
Two back ends for that call:

  exact : returns a correct answer; charges sqrt(d*N) to the cost. Scales to thousands of vertices.
  bbht  : runs their greedy algorithm, sampling each Grover search from its exact outcome law
          (BBHT with success probability sin^2((2j+1)theta)), and counts oracle applications.
          Stops after budget*sqrt(d*N) applications, so it can fail, and that is measured.

Limits: bbht is a statistical simulation of the query algorithm, it runs no circuit (see qiskit_check.py).
Gate counts and QRAM are not modelled. Worst cases are hand-built families, not a proof of worst case.
"""
import math
import numpy as np

INF = np.int64(1) << 60


class Group:
    __slots__ = ("verts", "K", "entries", "ptr", "complete")

    def __init__(self, verts, K):
        self.verts, self.K, self.entries, self.ptr, self.complete = verts, K, [], 0, False


class Stats:
    def __init__(self):
        self.calls = self.sum_K = self.sum_N = self.rebuilds = self.failed = self.applications = 0
        self.cost = self.naive = 0.0


def top_k_exact(f, types, d, rng, stats):
    """Row-wise: f has shape (len(types), len(verts)). Returns [(value, row, col)] sorted."""
    col = np.argmin(f, axis=1)
    val = f[np.arange(f.shape[0]), col]
    idx = np.flatnonzero(val < INF)
    if len(idx) > d:
        idx = idx[np.argpartition(val[idx], d - 1)[:d]]
    idx = idx[np.argsort(val[idx], kind="stable")]
    return [(int(val[i]), int(i), int(col[i])) for i in idx]


def top_k_bbht(f, types, d, rng, stats, budget=None):
    """Greedy algorithm of Durr et al. section 3 with exact Grover statistics. d = requested list size."""
    A, B = f.shape
    N = A * B
    fl = f.ravel()
    rows = np.repeat(np.arange(A), B)
    # ties broken by index, so that f is injective
    order = np.lexsort((np.arange(N), fl))
    rank = np.empty(N, dtype=np.int64)
    rank[order] = np.arange(N)
    rep = np.full(A, -1, dtype=np.int64)  # rep[row] = rank of the entry held for that type, -1 = no entry
    cap = np.int64(N + 1)
    limit = None if budget is None else budget * math.sqrt(d * N)
    used = 0
    held = 0
    while True:
        worst = cap if held < d else rep[rep >= 0].max()
        bound = np.where(rep >= 0, rep, worst)
        good = np.flatnonzero((rank < bound[rows]) & (fl < INF))
        t = len(good)
        if t == 0:
            break
        # BBHT search for a good element: 2j+1 oracle applications per attempt
        theta = math.asin(math.sqrt(t / N))
        m = 1.0
        found = False
        while not found:
            j = int(rng.integers(0, int(m)))
            used += 2 * j + 1
            if limit is not None and used > limit:
                stats.applications += used
                stats.failed += 1
                return _collect(rep, rank, order, f, A, B)
            found = rng.random() < math.sin((2 * j + 1) * theta) ** 2
            m = min(m * 8 / 7, math.sqrt(N) + 1)
        x = int(good[rng.integers(0, t)])
        r = rows[x]
        if rep[r] >= 0:
            rep[r] = rank[x]
        elif held < d:
            rep[r] = rank[x]
            held += 1
        else:
            rep[int(np.argmax(rep))] = -1
            rep[r] = rank[x]
    stats.applications += used
    return _collect(rep, rank, order, f, A, B)


def _collect(rep, rank, order, f, A, B):
    out = []
    for r in np.flatnonzero(rep >= 0):
        x = int(order[rep[r]])
        col = x % B
        out.append((int(f[r, col]), int(r), int(col)))
    out.sort()
    return out


class Run:
    def __init__(self, W, root=0, mode="exact", seed=0, budget=None):
        self.W, self.n, self.root = W, W.shape[0], root
        self.mode, self.budget, self.rng = mode, budget, np.random.default_rng(seed)
        self.stats = Stats()
        n = self.n
        self.degin = (W < INF).sum(axis=0)
        self.comp = np.arange(n)             # container of each vertex
        self.y = np.zeros(n, dtype=np.int64)  # dual offset of each vertex
        self.members = {v: [v] for v in range(n)}
        self.groups = {v: {} for v in range(n)}
        self.next_id = n
        # forest of contractions, kept to expand the answer and to output the dual
        self.children, self.node_y, self.in_edge, self.up = {}, {v: 0 for v in range(n)}, {}, {}
        for v in range(n):
            if v != root:
                self._install(v, Group(np.array([v]), 1))

    def _build(self, c, g):
        s = self.stats
        verts = g.verts
        # f(u,v) = w(u,v) - y(v), infinite for sources already inside the container
        f = self.W[:, verts] - self.y[verts]
        f[self.W[:, verts] >= INF] = INF
        f[self.comp == c, :] = INF
        d = min(g.K, self.n)
        N = int(self.degin[verts].sum())
        s.calls += 1
        s.sum_K += d
        s.sum_N += N
        s.cost += math.sqrt(d * max(N, 1))
        if callable(self.mode):
            res = self.mode(self.W[:, verts], self.y[verts], self.comp == c, d, self.rng, s)
        elif self.mode == "exact":
            res = top_k_exact(f, None, d, self.rng, s)
        else:
            res = top_k_bbht(f, None, d, self.rng, s, self.budget)
        g.entries = [(val, u, int(verts[col])) for val, u, col in res]
        g.ptr = 0
        g.complete = len(res) < d

    def _install(self, c, g):
        """Insert group g into container c, merging equal size classes. Builds the result."""
        groups = self.groups[c]
        cl = int(math.log2(len(g.verts)))
        while cl in groups:
            o = groups.pop(cl)
            g = Group(np.concatenate([g.verts, o.verts]), 0)
            cl = int(math.log2(len(g.verts)))
        g.K = len(g.verts)
        groups[cl] = g
        self._build(c, g)

    def _min_in(self, c):
        """Cheapest edge entering container c, as (reduced cost, u, v), or None."""
        best = None
        for g in self.groups[c].values():
            while True:
                while g.ptr < len(g.entries) and self.comp[g.entries[g.ptr][1]] == c:
                    g.ptr += 1
                if g.ptr < len(g.entries) or g.complete:
                    break
                g.K *= 2
                self.stats.rebuilds += 1
                self._build(c, g)
            if g.ptr < len(g.entries):
                _, u, v = g.entries[g.ptr]
                val = int(self.W[u, v] - self.y[v])
                if best is None or val < best[0]:
                    best = (val, u, v)
        return best

    def _contract(self, cycle):
        new = self.next_id
        self.next_id += 1
        self.children[new] = list(cycle)
        for c in cycle:
            self.up[c] = new
        self.node_y[new] = 0
        big = max(cycle, key=lambda c: len(self.members[c]))
        small = [c for c in cycle if c != big]
        mem = self.members.pop(big)
        grp = self.groups.pop(big)
        moved = []
        for c in small:
            moved += self.members.pop(c)
            self.groups.pop(c)
        all_mem = mem + moved
        self.comp[np.array(all_mem)] = new
        self.members[new], self.groups[new] = all_mem, grp
        if moved:
            self._install(new, Group(np.array(moved), 0))
        return new

    def solve(self):
        """Path-growing contraction. Returns (parent array, cost) or None if no arborescence exists."""
        n, s = self.n, self.stats
        attached = {self.root}
        for v0 in range(n):
            a = int(self.comp[v0])
            if a in attached:
                continue
            path = []
            while True:
                s.naive += math.sqrt(max(int(self.degin[self.members[a]].sum()), 1))
                e = self._min_in(a)
                if e is None:
                    return None
                val, u, v = e
                self.node_y[a] += val
                self.y[self.members[a]] += val
                self.in_edge[a] = (u, v)
                b = int(self.comp[u])
                if b in attached:
                    attached.update(path)
                    attached.add(a)
                    break
                if b in path:
                    i = path.index(b)
                    a = self._contract(path[i:] + [a])
                    path = path[:i]
                else:
                    path.append(a)
                    a = b
        return self._expand()

    def _child_with(self, node, v):
        x = v
        while self.up.get(x) != node:
            x = self.up[x]
        return x

    def _expand(self):
        parent = np.full(self.n, -1)
        tops = [c for c in set(int(x) for x in self.comp) if c != self.root]
        stack = [(c, self.in_edge[c]) for c in tops]
        while stack:
            node, (u, v) = stack.pop()
            if node < self.n:
                parent[node] = u
                continue
            hit = self._child_with(node, v)
            stack.append((hit, (u, v)))
            for c in self.children[node]:
                if c != hit:
                    stack.append((c, self.in_edge[c]))
        cost = int(sum(self.W[parent[v], v] for v in range(self.n) if v != self.root))
        return parent, cost

    def verify(self, parent, cost):
        """Independent optimality check by weak duality, no trust in the run. O(n^2 * nodes)."""
        W, n, root = self.W, self.n, self.root
        assert parent[root] == -1
        for v in range(n):
            x, steps = v, 0
            while x != root:
                x = int(parent[x])
                steps += 1
                assert x >= 0 and steps <= n, "not an arborescence"
        sets = {v: np.zeros(n, dtype=bool) for v in self.node_y}
        for v in range(n):
            x = v
            sets[x][v] = True
            while x in self.up:
                x = self.up[x]
                sets[x][v] = True
        slack = W.astype(np.float64)
        slack[W >= INF] = np.inf
        total = 0
        for node, y in self.node_y.items():
            assert (y >= 0 or sets[node].sum() == 1) and (y == 0 or not sets[node][root])  # singletons may be negative (Lemma 2)
            total += y
            if y:
                slack -= y * np.outer(~sets[node], sets[node])
                entering = sum(1 for v in range(n) if v != root and sets[node][v] and not sets[node][int(parent[v])])
                assert entering == 1, "arborescence enters a dual set more than once"
        off = ~np.eye(n, dtype=bool)
        off[:, root] = False  # edges into the root are never used
        assert (slack[off] >= 0).all(), "dual infeasible"
        assert total == cost, "duality gap"
        return True


def solve(W, root=0, mode="exact", seed=0, budget=None):
    r = Run(W.copy(), root, mode, seed, budget)
    return r, r.solve()
