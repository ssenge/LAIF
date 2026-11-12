"""Dominator tree of a planar digraph: centralized simulation of notes/DOMINATORS.md.

Checks the logic of the note. It does not simulate rounds. Values that the note computes by aggregates over segments of
the path and over the parts {p_a} + {y : a(y) = a} are computed here from the same data, in the same order. Every FAIL
counter is a claim of the note. The final tree is compared with networkx, and on small instances with vertex removal.

python3 -I dom.py SEED SECS [big]    main lane
python3 -I dom.py ctl SEED SECS      negative controls
python3 -I dom.py scale              large instances
"""
import collections, json, os, random, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
import dagdfs as dd
import gdfs

INF = 10 ** 9


def spans(k):
    """Segments of positions 1..k by level: Z = [l, c], Y = [c + 1, r]. Position t has the binary code t - 1."""
    size, lev = 1, 0
    while size < k:
        l = 1
        while l + size <= k:
            yield lev, l, l + size - 1, min(k, l + 2 * size - 1)
            l += 2 * size
        size *= 2
        lev += 1


def scan(A, B, l, c, r, mode):
    """Largest good x up to each x, first leaf in Y of each centre in Z, and X(j), the first t in Y with A(t) < j."""
    pa, pb, last, g = INF, -INF, None, {}
    for x in range(c + 1, r + 2):
        if x >= c + 2 and (pb < x or mode == 'nogood'):
            last = x
        g[x] = last
        if x <= r:
            pa, pb = min(pa, A[x]), max(pb, B[x])
    first, cur = {}, r + 1
    for t in range(r, c, -1):
        if A[t] < l:
            cur = t
        elif A[t] <= c:
            first[A[t]] = t
    X = {}
    for j in range(l, c + 1):
        X[j] = cur
        if j in first:
            cur = min(cur, first[j])
    return g, first, X


def ends(k, A, B, mode):
    """m(j): the largest x with (j, x) closed, as the maximum over the levels where j is in Z."""
    m = {j: j + 1 for j in range(1, k + 1)}
    for lev, l, c, r in spans(k):
        g, first, X = scan(A, B, l, c, r, mode)
        sa, sb = INF, -INF
        for j in range(c, l - 1, -1):
            x = g[X[j]]
            if (sa >= j or mode == 'nosuf') and x is not None and (x > sb or mode == 'noM'):
                if mode != 'firstonly' or m[j] == j + 1:
                    m[j] = max(m[j], x)
            sa, sb = min(sa, A[j]), max(sb, B[j])
    return m


def labels(k, A, B, m, st, mode):
    """lam[lev, a]: last chain member at or before a. dlt[lev, t]: deepest chain member with m > t."""
    lam, dlt = {}, {}
    for lev, l, c, r in spans(k):
        g, first, X = scan(A, B, l, c, r, mode)
        C = [j for j in range(l, c + 1) if m[j] > c + 1]
        st['max.chain'] = max(st['max.chain'], len(C))
        cur, after = None, {}
        for a in range(l, c + 1):
            if a in m and m[a] > c + 1:
                cur = a
            lam[lev, a] = cur
        cur = None
        for a in range(c, l - 1, -1):
            after[a] = cur
            if m[a] > c + 1:
                cur = a
        marks, routes = {}, []
        for a, t in first.items():
            j0, j1 = lam[lev, a], after[a]
            if j0 is None or j1 is None or (m[j0] >= r if mode == 'ringr' else m[j0] > r) or m[j0] <= m[j1] or (t != X[j1] and mode != 'nota'):
                continue
            pos = g[t]
            if pos != m[j1]:
                st['FAIL.mark_pos'] += 1
            if pos in marks:
                st['FAIL.mark_twice'] += 1
            marks[pos] = j1 if mode == 'markj1' else j0
            routes.append((pos, t))
            st['n.star_marks'] += 1
        routes.sort()
        if any(b[0] <= a[1] for a, b in zip(routes, routes[1:])):
            st['FAIL.routes_meet'] += 1
        past = [j for j in C if m[j] > r]
        J = past[-1] if past else None
        rest = C[len(past):]
        if rest and m[rest[0]] <= r and mode != 'nopast':
            if m[rest[0]] in marks:
                st['FAIL.mark_twice'] += 1
            marks[m[rest[0]]] = J
            st['n.past_marks'] += 1
        cur = C[-1] if C else None
        for t in range(c + 1, r + 1):
            if t in marks:
                cur = marks[t]
            dlt[lev, t] = cur
            truth = [j for j in C if m[j] > t]
            st['chk.delta'] += 1
            if mode in ('ok', 'markj1', 'ringr', 'nota') and cur != (truth[-1] if truth else None):
                st['FAIL.delta'] += 1
    return lam, dlt


def deepest_on_path(t, k, dlt):
    """Deepest dominator of the path vertex at position t, from its own label."""
    lev = 0
    while (1 << lev) < k:
        d = dlt.get((lev, t))
        if d is not None:
            return d
        lev += 1
    return None


def deepest_off(a, b, k, lam, dlt, mode):
    """Deepest dominator on the path of a vertex off it, from the labels of p_a and p_b."""
    if a == 0:
        return None
    if a == b:
        return a
    lev = ((a - 1) ^ (b - 1)).bit_length() - 1
    x, y = lam.get((lev, a)), dlt.get((lev, b))
    if x is not None and y is not None:
        return max(x, y) if mode == 'maxld' else min(x, y)
    lev += 1
    while (1 << lev) < k:
        d = dlt.get((lev, b))
        if d is not None:
            return d
        lev += 1
    return None


def tails(order, R, E, O, arcs):
    """Value of each vertex off the path: the first index in order that reaches it through vertices off the path."""
    val, left = {}, set(O)
    for i in order:
        src = [z for z in (E if i == 0 else arcs.get(R[i - 1], ())) if z in left]
        if src:
            got = dd.reach(arcs, src, left)
            for y in got:
                val[y] = i
            left -= got
    return val, left


def path_step(Q, R, E, arcs, st, mode, check):
    """Deepest dominator on the path R of each vertex of Q, with None for the virtual root."""
    k, pos = len(R), {v: i + 1 for i, v in enumerate(R)}
    O = Q - set(R)
    a, l1 = tails(range(k + 1), R, E, O, arcs)
    b, l2 = tails(range(k, -1, -1), R, E, O, arcs)
    if l1 or l2:
        st['FAIL.not_reached'] += 1
    if mode == 'onea':
        b = dict(a)
    A, B = {t: INF for t in range(1, k + 1)}, {t: -INF for t in range(1, k + 1)}
    for t in range(2, k + 1):
        if R[t - 1] in E:
            A[t], B[t] = 0, 0
    for u in Q:
        for v in arcs.get(u, ()):
            if v in pos:
                t = pos[v]
                if u in pos:
                    A[t], B[t] = min(A[t], pos[u]), max(B[t], pos[u])
                else:
                    A[t], B[t] = min(A[t], a[u]), max(B[t], b[u])
    if mode == 'noback':
        B = {t: min(B[t], t - 1) for t in B}
    m = ends(k, A, B, mode)
    lam, dlt = labels(k, A, B, m, st, mode)
    out = {y: deepest_off(a[y], b[y], k, lam, dlt, mode) for y in O}
    for t in range(1, k + 1):
        out[R[t - 1]] = deepest_on_path(t, k, dlt)
    st['max.k'] = max(st['max.k'], k)
    st['n.long_interval'] += sum(1 for j in m if m[j] > j + 1)
    st['n.past_B'] += sum(1 for j in m if m[j] <= k and A[m[j]] >= j)
    if check and mode in ('ok', 'markj1', 'ringr', 'nota'):
        keyz = {}
        for i in range(k + 1):
            for z in (E if i == 0 else arcs.get(R[i - 1], ())):
                if z in O and (i, z) < keyz.get(z, (INF, 0)):
                    keyz[z] = (i, z)
        cls = dd.classes_direct(keyz, arcs, O)
        pre, code = dd.classes_bits(keyz, arcs, O, max(Q) + 1)
        st['chk.a_bits'] += 1
        if any(keyz[cls[y]][0] != a[y] or code[cls[y]] != pre[y] for y in O):
            st['FAIL.a_bits'] += 1
        for j, p in enumerate(R, 1):
            got = dd.reach(arcs, [e for e in E if e != p], Q - {p})
            true_m = next((t for t in range(j + 1, k + 1) if R[t - 1] in got), k + 1)
            st['chk.m'] += 1
            if true_m != m[j]:
                st['FAIL.m'] += 1
            for y in O:
                if (y not in got) != (j <= a[y] and b[y] < m[j]):
                    st['FAIL.formula'] += 1
            for i in range(j):
                if R[i] not in got and i + 1 != j:
                    st['FAIL.prefix'] += 1
        ints = sorted((j, m[j]) for j in m)
        for (p1, q1) in ints:
            for (p2, q2) in ints:
                if p1 < p2 < q1 < q2:
                    st['FAIL.not_laminar'] += 1
        for y in Q:
            truth = None
            for j, p in enumerate(R, 1):
                if p != y and y not in dd.reach(arcs, [e for e in E if e != p], Q - {p}):
                    truth = j
            st['chk.deepest'] += 1
            if out[y] != truth:
                st['FAIL.deepest'] += 1
    return {y: (R[d - 1] if d is not None else None) for y, d in out.items()}


class Run:
    """One dominator computation along the paths of the general search."""

    def __init__(self, arcs, r, st, mode, rng):
        self.arcs, self.st, self.mode, self.rng = arcs, st, mode, rng
        self.idom, self.ent = {}, {r}

    def on_path(self, Q, R, new):
        E = {R[0]} if self.mode == 'noentry' else self.ent & Q
        if R[0] not in E:
            self.st['FAIL.root_not_entry'] += 1
        check = len(Q) * len(R) <= 1500 or self.rng.random() < .002
        for y, d in path_step(Q, R, E, self.arcs, self.st, self.mode, check).items():
            if d is not None:
                self.idom[y] = d
        cls = {y: z for z, K in new for y in K}
        for u in Q:
            for v in self.arcs.get(u, ()):
                if v in cls and cls.get(u) != cls[v]:
                    self.ent.add(v)

    def on_small(self, x, K, arcs, kids):
        dd.small(x, K, arcs, kids)
        G = nx.DiGraph()
        G.add_node('root')
        for e in ({x} if self.mode == 'noentry' else self.ent & K):
            G.add_edge('root', e)
        G.add_edges_from((u, v) for u in K for v in arcs.get(u, ()) if v in K)
        for y, d in nx.immediate_dominators(G, 'root').items():
            if y != 'root' and d != 'root':
                self.idom[y] = d


def dominators(arcs, r, n, rng, st, mode='ok'):
    run = Run(arcs, r, st, mode, rng)
    gdfs.ON_PATH, gdfs.ON_SMALL = run.on_path, run.on_small
    try:
        gdfs.solve(arcs, [r], n, rng, st, 'ok')
    finally:
        gdfs.ON_PATH = gdfs.ON_SMALL = None
    return run.idom


def dag_dominators(arcs, r, n, rng, st, s, mode='ok'):
    """The same path step on the passes of sim/dagdfs.py, with no general search."""
    run = Run(arcs, r, st, mode, rng)
    sp, sm = dd.split, dd.small

    def split(K, path, *rest):
        new = sp(K, path, *rest)
        run.on_path(K, path, new)
        return new

    def small(x, K, a, kids):
        dd.small = sm
        run.on_small(x, K, a, kids)
        dd.small = small
    dd.split, dd.small = split, small
    try:
        dd.dag_dfs(arcs, [r], n, rng, st, 'ok', s)
    finally:
        dd.split, dd.small = sp, sm
    return run.idom


def jumps(k, rng):
    """A directed path with non-crossing chords on both sides, in both directions, some through a vertex off the path, so that intervals nest and jumps run back."""
    arcs = collections.defaultdict(set)
    for i in range(k - 1):
        arcs[i].add(i + 1)
    nxt = k
    for side in range(2):
        stack = [(0, k - 1)]
        while stack:
            lo, hi = stack.pop()
            if hi - lo < 2 or rng.random() < .25:
                continue
            a = rng.randrange(lo, hi - 1)
            b = rng.randrange(a + 2, hi + 1)
            u, v = (a, b) if rng.random() < .6 else (b, a)
            if rng.random() < .4:
                arcs[u].add(nxt)
                arcs[nxt].add(v)
                if rng.random() < .3:
                    arcs[nxt].add(nxt + 1)
                    nxt += 1
                nxt += 1
            else:
                arcs[u].add(v)
            stack += [(lo, a), (a, b), (b, hi)]
    return arcs


def nest(k, rng):
    """Nested forward jumps around the middle of the path, each landing at or past the point it opens up, with back jumps to that point."""
    arcs = collections.defaultdict(set)
    for i in range(k - 1):
        arcs[i].add(i + 1)
    lo, hi, nxt = rng.randrange(1, 4), k - 1 - rng.randrange(0, 3), k
    while hi - lo > 2:
        a, t = lo, hi
        if rng.random() < .5 and hi - lo > 4:
            arcs[hi].add(hi - 2)
            hi -= 2
        if rng.random() < .3:
            arcs[a].add(nxt)
            arcs[nxt].add(t)
            nxt += 1
        else:
            arcs[a].add(t)
        lo += rng.randrange(1, 4)
        hi -= rng.randrange(1, 4)
    return arcs


def instance(rng, big):
    if rng.random() < .35:
        k = rng.randrange(6, 240 if big else 70)
        return ('jumps', jumps(k, rng)) if rng.random() < .5 else ('nest', nest(k, rng))
    return gdfs.instance(rng, big)


def truth_by_removal(arcs, r, V):
    all_ = dd.reach(arcs, [r], V)
    doms = {y: set() for y in all_}
    for p in all_ - {r}:
        got = dd.reach(arcs, [r], V - {p})
        for y in all_ - got - {p}:
            doms[y].add(p)
    return {y: max(doms[y], key=lambda p: len(doms[p]), default=r) for y in all_ if y != r}


def run_one(rng, st, big=False, mode='ok'):
    name, arcs = instance(rng, big)
    V = set(arcs) | {v for vs in arcs.values() for v in vs}
    if len(V) < 2:
        return
    U = nx.Graph()
    U.add_nodes_from(V)
    U.add_edges_from((u, v) for u in arcs for v in arcs[u])
    st['chk.planar'] += 1
    if not nx.check_planarity(U)[0]:
        st['FAIL.not_planar'] += 1
        return
    arcs = {u: set(vs) for u, vs in arcs.items()}
    r = 0 if name == 'jumps' and rng.random() < .7 else rng.choice(sorted(V))
    idom = dominators(arcs, r, len(V), rng, st, mode)
    G = nx.DiGraph()
    G.add_node(r)
    G.add_edges_from((u, v) for u in arcs for v in arcs[u])
    true = {y: d for y, d in nx.immediate_dominators(G, r).items() if y != r}
    st['chk.tree'] += 1
    if len(V) <= 60:
        st['chk.removal'] += 1
        if truth_by_removal(arcs, r, V) != true:
            st['FAIL.networkx'] += 1
    bad = sum(1 for y in true if idom.get(y) != true[y])
    if bad or set(idom) - set(true):
        st['FAIL.tree'] += 1
    deep = collections.Counter()
    for y in true:
        h, c = y, 0
        while h != r:
            h, c = true[h], c + 1
        deep[y] = c
    st['n.vertices'] += len(true)
    st['n.nontrivial'] += sum(1 for y in true if true[y] != r)
    st['max.depth'] = max(st['max.depth'], max(deep.values(), default=0))
    st['max.n'] = max(st['max.n'], len(V))
    st['runs'] += 1
    st['fam.' + name.split('.')[0]] += 1


def dag_lane(seed, secs, big=False):
    """Corollary 3: DAGs, and digraphs with cycles at the cost of more passes per level."""
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    while time.time() - t0 < secs:
        name, V, E, arcs = dd.digraph(rng, big)
        if len(V) < 2:
            continue
        st['chk.planar'] += 1
        if not nx.check_planarity(nx.Graph(E))[0]:
            st['FAIL.not_planar'] += 1
        arcs = {u: set(vs) for u, vs in arcs.items()}
        G = nx.DiGraph()
        G.add_nodes_from(V)
        G.add_edges_from((u, v) for u in arcs for v in arcs[u])
        s = max(len(c) for c in nx.strongly_connected_components(G))
        r = rng.choice(sorted(V))
        idom = dag_dominators(arcs, r, len(V), rng, st, s)
        true = {y: d for y, d in nx.immediate_dominators(G, r).items() if y != r}
        st['runs'] += 1
        st['runs.dag'] += int(s == 1)
        st['max.scc'] = max(st['max.scc'], s)
        st['max.n'] = max(st['max.n'], len(V))
        st['n.nontrivial'] += sum(1 for y in true if true[y] != r)
        if idom != true:
            st['FAIL.tree'] += 1
    return dict(sorted((k, int(v)) for k, v in st.items()))


def stress_path(rng, st, mode='ok'):
    """The path step alone with the whole path of a jump instance as R, so that long chains and late landings occur."""
    k = rng.randrange(6, 48)
    arcs = (nest if rng.random() < .5 else jumps)(k, rng)
    arcs = {u: set(vs) for u, vs in arcs.items()}
    V = set(arcs) | {v for vs in arcs.values() for v in vs}
    Q = dd.reach(arcs, [0], V)
    R = list(range(k))
    if rng.random() < .3:
        R = R[:rng.randrange(2, k + 1)]
    E = {0} | {v for v in Q if rng.random() < rng.choice([0, 0, 0, .03])}
    path_step(Q, R, E, arcs, st, mode, True)
    st['stress_path'] += 1


def stress(rng, st, mode='ok'):
    """The path step alone on an arbitrary digraph, planar or not, with a random path from the root and random entries."""
    n = rng.randrange(3, 28)
    p = rng.choice([1.2, 1.6, 2.2, 3.0]) / n
    arcs = {u: {v for v in range(n) if v != u and rng.random() < p} for u in range(n)}
    z = rng.randrange(n)
    Q = dd.reach(arcs, [z], set(range(n)))
    R, cur = [z], z
    while rng.random() < .93:
        opts = [v for v in arcs[cur] if v not in R]
        if not opts:
            break
        cur = rng.choice(opts)
        R.append(cur)
    E = {z} | {v for v in Q if rng.random() < rng.choice([0, .05, .15])}
    path_step(Q, R, E, arcs, st, mode, True)
    st['stress'] += 1


def lane(seed, secs, big=False):
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    while time.time() - t0 < secs:
        run_one(rng, st, big)
        for _ in range(3):
            stress(rng, st)
            stress_path(rng, st)
    return dict(sorted((k, int(v)) for k, v in st.items()))


CTL = ['noentry', 'noback', 'onea', 'nosuf', 'noM', 'nogood', 'firstonly', 'nopast', 'maxld']


def controls(seed, secs):
    """Each control changes one rule. Only the final tree counts, so a control shows that the tree needs this rule."""
    out = {}
    for c in CTL:
        rng = random.Random(seed)
        st = collections.Counter()
        t0 = time.time()
        while time.time() - t0 < secs:
            run_one(rng, st, False, c)
        out[c] = {k: int(st[k]) for k in sorted(st) if k.startswith('FAIL') or k == 'runs'}
    return out


RING = ['markj1', 'ringr', 'nota']


def ring_controls(seed, secs):
    """Controls of the rings, on the path step alone, where the internal checks see them."""
    out = {}
    for c in ['ok'] + RING:
        rng = random.Random(seed)
        st = collections.Counter()
        t0 = time.time()
        while time.time() - t0 < secs:
            stress_path(rng, st, c)
            st['runs'] += 1
        out[c] = {k: int(st[k]) for k in sorted(st) if k.startswith('FAIL') or k in ('runs', 'n.star_marks')}
    return out


def scale():
    rng = random.Random(1)
    for name, make, sizes in (('jumps', lambda s: jumps(s, rng), (400, 1600, 6400)), ('bigrid', lambda s: gdfs.bigrid(s, s, .7, rng), (20, 40, 80)), ('ladder', gdfs.ladder, (200, 800, 3200))):
        for s in sizes:
            arcs = {u: set(vs) for u, vs in make(s).items()}
            V = set(arcs) | {v for vs in arcs.values() for v in vs}
            st = collections.Counter()
            t0 = time.time()
            idom = dominators(arcs, 0, len(V), rng, st)
            G = nx.DiGraph()
            G.add_node(0)
            G.add_edges_from((u, v) for u in arcs for v in arcs[u])
            true = {y: d for y, d in nx.immediate_dominators(G, 0).items() if y != 0}
            print(json.dumps({'fam': name, 'n': len(V), 'reached': len(true) + 1, 'ok': idom == true, 'nontrivial': sum(1 for y in true if true[y] != 0), 'max_k': st['max.k'], 'max_chain': st['max.chain'], 'levels': st['max.levels'], 'secs': round(time.time() - t0, 1), 'fails': {k: v for k, v in st.items() if k.startswith('FAIL')}}), flush=True)


if __name__ == '__main__':
    if sys.argv[1] == 'ctl':
        print(json.dumps(controls(int(sys.argv[2]), float(sys.argv[3])), indent=0))
    elif sys.argv[1] == 'ringctl':
        print(json.dumps(ring_controls(int(sys.argv[2]), float(sys.argv[3]))))
    elif sys.argv[1] == 'dag':
        print(json.dumps(dag_lane(int(sys.argv[2]), float(sys.argv[3]), len(sys.argv) > 4)))
    elif sys.argv[1] == 'scale':
        scale()
    else:
        print(json.dumps(lane(int(sys.argv[1]), float(sys.argv[2]), len(sys.argv) > 3)))
