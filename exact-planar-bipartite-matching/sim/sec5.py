"""Section 5 of notes/DAG_DFS.md as written: the search of the condensation, with the out-tree and the separator on the graph of H.

python3 -I sim/sec5.py SEED SECS [big]   no FAIL expected
python3 -I sim/sec5.py ctl SEED SECS     each control must fire
Checks: Lemma 5 (a class holds part of one piece), one round of step 5, Lemma 3 in vertices, the search tree of the condensation
by a replay, the numbers by the formula of Section 5 against the replay, and the theorem on every arc.
Reachability is computed directly: no rounds here. Points are strong components, named by their least vertex."""
import collections, json, os, random, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
import dagdfs as dd
import dirs
import fam

VIRT = -1


class Run:
    def __init__(self, V, arcs, rng, ctl, small, st):
        self.V, self.arcs, self.rng, self.ctl, self.small, self.st = V, arcs, rng, ctl, small, st
        H = nx.DiGraph()
        H.add_nodes_from(V)
        H.add_edges_from((u, v) for u in arcs for v in arcs[u])
        self.H = H
        self.comp, self.mem = {}, {}
        for c in nx.strongly_connected_components(H):
            p = min(c)
            self.mem[p] = set(c)
            for v in c:
                self.comp[v] = p
        self.pre, self.tpar, self.tkids = {}, {}, collections.defaultdict(list)
        for p, c in self.mem.items():
            self.fix_tree(p, c)
        self.out = collections.defaultdict(set)  # arcs of the condensation
        for u in arcs:
            for v in arcs[u]:
                if self.comp[u] != self.comp[v]:
                    self.out[self.comp[u]].add(self.comp[v])
        self.kids, self.tail = collections.defaultdict(list), {}

    def fix_tree(self, p, c):
        """T_C: any spanning tree of the component, with its pre-order."""
        U = nx.Graph(self.H.subgraph(c).to_undirected())
        seen, stack, i = {p}, [p], 0
        order = []
        while stack:
            u = stack.pop(self.rng.randrange(len(stack)))
            order.append(u)
            for v in U[u]:
                if v not in seen:
                    seen.add(v)
                    self.tpar[v] = u
                    stack.append(v)
        kids = collections.defaultdict(list)
        for v in c:
            if v in self.tpar:
                kids[self.tpar[v]].append(v)
        walk = [p]
        while walk:
            u = walk.pop()
            self.pre[u] = i
            i += 1
            k = kids[u]
            self.rng.shuffle(k)
            self.tkids[u] = k
            walk += reversed(k)

    def verts(self, pts):
        return set().union(*(self.mem[p] for p in pts)) if pts else set()

    def key(self, k, i, a, q):
        if self.ctl == 'shallow':
            return (i, self.pre[a], q)
        if self.ctl == 'idorder':
            return (k - i, q, self.pre[a])
        return (k - i, self.pre[a], q)

    def lemma1(self, path, K):
        """Lemma 1 on points. Returns the classes (head, entry vertex, points)."""
        R = K - set(path)
        k = len(path) - 1
        best = {}
        for i, p in enumerate(path):
            for a in self.mem[p]:
                for b in self.arcs.get(a, ()):
                    q = self.comp[b]
                    if q in R:
                        ky = self.key(k, i, a, q)
                        if q not in best or ky < best[q][0]:
                            best[q] = (ky, i, a, b)
        cls, done = [], set()
        for q in sorted(best, key=lambda q: best[q][0]):
            if q in done:
                continue  # its class does not count
            g, st = {q}, [q]
            while st:
                u = st.pop()
                for v in self.out[u]:
                    if v in R and v not in done and v not in g:
                        g.add(v)
                        st.append(v)
            done |= g
            cls.append((q, best[q][3], g))
            ky, i, a, _ = best[q]
            self.kids[path[i]].append((ky, q))
            self.tail[q] = a
        if done != R:
            self.st['FAIL.classes_not_cover'] += 1
        for i, p in enumerate(path):
            self.kids[p].sort()
            self.kids[p] = [q for _, q in self.kids[p]]
            if i + 1 < len(path):
                self.kids[p].insert(0, path[i + 1])
                self.tail[path[i + 1]] = None
        return cls

    def greedy_path(self, q, K):
        path, on = [q], {q}
        while True:
            c = [v for v in self.out[path[-1]] if v in K and v not in on]
            if not c:
                return path
            path.append(self.rng.choice(c))
            on.add(path[-1])

    def solve(self, x, K):
        """x: entry vertex of the root point. K: a set of points, all reached from it."""
        q = self.comp[x]
        KV = self.verts(K)
        if len(KV) < self.small:
            for h, z, g in self.lemma1(self.greedy_path(q, K), K):
                self.solve(z, g)
            return
        arcs = {u: {v for v in self.arcs.get(u, ()) if v in KV} for u in KV}
        par = dd.out_tree(x, KV, arcs, self.rng)
        pu, pv = dd.separator(x, KV, arcs, par, self.st)
        pi = self.points_of(pu)
        tau = self.points_of([v for v in pv if v not in set(pu)])
        on = set(pi)
        pieces, cur = [], []
        for p in tau:
            if p in on:
                if cur:
                    pieces.append(cur)
                cur = []
            else:
                cur.append(p)
        if cur:
            pieces.append(cur)
        self.st['chk.split'] += 1
        if len(pieces) > 1:
            self.st['n.tau_reenters'] += 1
            self.st['max.pieces'] = max(self.st['max.pieces'], len(pieces))
        left = {p for b in pieces for p in b}
        where = {p: i for i, b in enumerate(pieces) for p in b}
        out = []
        for h, z, g in self.lemma1(pi, K):
            if self.ctl == 'noround':
                out.append((h, z, g))
                continue
            touched = {where[p] for p in g if p in left}
            self.st['chk.lemma5'] += 1
            if len(touched) > 1:
                self.st['FAIL.lemma5_two_pieces'] += 1
            if not touched:
                out.append((h, z, g))
                continue
            beta = [p for p in pieces[min(touched)] if p in g]
            idx = [pieces[min(touched)].index(p) for p in beta]
            if idx != list(range(idx[0], idx[0] + len(idx))):
                self.st['FAIL.lemma5_not_contiguous'] += 1
            path = self.to_block(h, g, beta)
            self.st['chk.step5'] += 1
            for hh, zz, gg in self.lemma1(path, g):
                if gg & left and not set(beta) >= (gg & left):
                    self.st['FAIL.lemma5_two_pieces'] += 1
                if gg & set(beta):
                    self.st['FAIL.step5_needs_two_rounds'] += 1
                out.append((hh, zz, gg))
        for h, z, g in out:
            self.st['chk.lemma3'] += 1
            if len(self.verts(g)) * 4 > 3 * len(KV):
                self.st['FAIL.lemma3'] += 1
            self.solve(z, g)

    def points_of(self, vs):
        out = []
        for v in vs:
            p = self.comp[v]
            if out and out[-1] == p:
                continue
            if p in out:
                self.st['FAIL.path_returns_to_a_point'] += 1
            out.append(p)
        return out

    def to_block(self, h, g, beta):
        """Lemma 2(b) on the condensation: from the head through Z to the first point of beta, then along beta."""
        if h in beta:
            k = beta.index(h)
            if k and self.ctl != 'shallow':
                self.st['FAIL.lemma2_not_first'] += 1
            return beta[k:]
        b = set(beta)
        par, st = {h: None}, [h]
        while st:
            u = st.pop()
            for v in self.out[u]:
                if v in g and v not in b and v not in par:
                    par[v] = u
                    st.append(v)
        for k, s in enumerate(beta):
            for u in par:
                if s in self.out[u]:
                    if k and self.ctl != 'shallow':
                        self.st['FAIL.lemma2_not_first'] += 1
                    p = [u]
                    while par[p[-1]] is not None:
                        p.append(par[p[-1]])
                    return p[::-1] + beta[k:]
        self.st['FAIL.lemma2_no_entry'] += 1
        return [h]

    def numbers(self):
        """The numbers by the formula of Section 5: next point by (P), weighted pre-order on T_C by (T2), earlier heads at the tail."""
        size = {}

        def sz(p):
            size[p] = (p != VIRT) + sum(sz(c) for c in self.kids[p])
            return size[p]
        sys.setrecursionlimit(max(10000, 4 * len(self.V)))
        sz(VIRT)
        off = {}
        for p, ch in list(self.kids.items()):
            if p == VIRT:
                t = 0
                for c in ch:
                    off[c] = t
                    t += size[c]
                continue
            nxt = 0
            at = collections.defaultdict(list)
            for c in ch:
                if self.tail[c] is None:
                    off[c] = 0
                    nxt = size[c]
                else:
                    at[self.tail[c]].append(c)
            w = {a: sum(size[c] for c in cs) for a, cs in at.items()}
            below = {}

            def fill(a):  # subtree sums of w on T_C
                below[a] = w.get(a, 0) + sum(fill(b) for b in self.tkids[a])
                return below[a]
            fill(p)

            def down(a, acc):  # ancestor sums: everything before a in pre-order of T_C
                W[a] = acc
                acc += w.get(a, 0)
                for b in self.tkids[a]:
                    down(b, acc)
                    acc += below[b]
            W = {}
            down(p, 0)
            for a, cs in at.items():
                t = nxt + W[a]
                for c in cs:
                    off[c] = t
                    t += size[c]
        e = {}

        def go(p, acc):
            e[p] = acc
            for c in self.kids[p]:
                go(c, acc + off[c])
        go(VIRT, 0)
        return {p: e[p] + size[p] - 1 for p in self.mem}

    def replay(self):
        """A real search of the condensation: children in order, then the other arcs."""
        seen, post = set(), {}
        sys.setrecursionlimit(max(10000, 4 * len(self.V)))
        t = [0]

        def visit(p):
            seen.add(p)
            for c in self.kids[p]:
                if c in seen:
                    self.st['FAIL.replay_child_seen'] += 1
                    continue
                visit(c)
            for v in self.out[p]:
                if v not in seen:
                    self.st['FAIL.replay_extra_visit'] += 1
                    visit(v)
            post[p] = t[0]
            t[0] += 1
        for r in self.kids[VIRT]:
            visit(r)
        if len(seen) != len(self.mem):
            self.st['FAIL.replay_cover'] += 1
        return post


def ladder(m):
    """The forced ladder: tau leaves and re-enters the components of pi."""
    V, arcs = {}, collections.defaultdict(set)
    v = lambda x: V.setdefault(x, len(V))
    for j in range(m):
        arcs[v(('p', j))].add(v(('q', j)))
        arcs[v(('q', j))].add(v(('p', j)))
        if j + 1 < m:
            arcs[v(('p', j))].add(v(('p', j + 1)))
            arcs[v(('q', j))].add(v(('w', j)))
            arcs[v(('w', j))].add(v(('q', j + 1)))
    return set(V.values()), arcs


def one(seed, big, ctl=None):
    rng = random.Random(seed)
    st = collections.Counter()
    k = rng.randrange(8)
    if k == 0:
        V, arcs = ladder(rng.randrange(2, 16))
    else:
        _, V, _, arcs = dirs.digraph(rng, big)
    V = set(V)
    G = nx.Graph()
    G.add_nodes_from(V)
    G.add_edges_from((u, v) for u in arcs for v in arcs[u])
    if not nx.check_planarity(G)[0]:
        st['FAIL.not_planar'] += 1
    small = rng.choice([4, 6, 12])
    r = Run(V, arcs, rng, ctl, small, st)
    # the roots: one vertex of each source component, ordered by pre-order in a BFS tree of each part of G
    tgt = {q for p in r.out for q in r.out[p]}
    roots = [p for p in r.mem if p not in tgt]
    bfs = {}
    for c in nx.connected_components(G):
        for v in nx.bfs_tree(G, min(c)):
            bfs[v] = len(bfs)
    # the virtual vertex: roots in BFS order, each takes what is still free
    free, tops = set(r.mem), []
    for p in sorted(roots, key=lambda p: bfs[p]):
        g, stk = {p}, [p]
        while stk:
            u = stk.pop()
            for v in r.out[u]:
                if v in free and v not in g:
                    g.add(v)
                    stk.append(v)
        free -= g
        tops.append((p, g))
        r.kids[VIRT].append(p)
        r.tail[p] = None
    for p, g in tops:
        r.solve(min(r.mem[p]), g)
    st['runs'] += 1
    st['points'] += len(r.mem)
    st['max.n'] = max(st['max.n'], len(V))
    st['cycles'] += len(r.mem) < len(V)
    post = r.replay()
    num = r.numbers()
    for p in r.mem:
        st['chk.numbers'] += 1
        if num[p] != post[p]:
            st['FAIL.numbers_formula'] += 1
    c = len(r.mem)
    for u in arcs:
        for v in arcs[u]:
            st['chk.arcs'] += 1
            if r.comp[u] != r.comp[v] and num[r.comp[u]] <= num[r.comp[v]]:
                st['FAIL.order_arc'] += 1
    if sorted(c - num[p] for p in r.mem) != list(range(1, c + 1)):
        st['FAIL.not_dense'] += 1
    return st


def lane(seed, secs, big, ctl=None):
    t0, tot, i = time.time(), collections.Counter(), 0
    while time.time() - t0 < secs:
        s = one(seed * 10 ** 6 + i, big, ctl)
        i += 1
        for k, v in s.items():
            if k.startswith('max.'):
                tot[k] = max(tot[k], v)
            else:
                tot[k] += v
    return dict(sorted(tot.items()))


if __name__ == '__main__':
    if sys.argv[1] == 'ctl':
        seed, secs = int(sys.argv[2]), float(sys.argv[3])
        for c in ('shallow', 'idorder', 'noround'):
            r = lane(seed, secs, False, c)
            print(c, json.dumps({k: v for k, v in r.items() if k.startswith('FAIL') or k == 'runs'}), flush=True)
    else:
        print(json.dumps(lane(int(sys.argv[1]), float(sys.argv[2]), len(sys.argv) > 3)))
