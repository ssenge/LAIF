"""Independent engine for notes/GENERAL_DFS.md, written from the note only. No repo imports.

All problems of a level run in lockstep. Every primitive is one global call on a union digraph, and it is counted once,
whichever number of parts takes part. A part only sees what the call returns. That is the point: it tests "for all these at once".

python3 -I -B eng.py main SEED SECS [big]    all checks, every instance verified planar
python3 -I -B eng.py ctl  SEED SECS          negative controls
python3 -I -B eng.py scale                   calls against log n on large instances
"""
import collections, json, math, random, sys, time
import networkx as nx

SMALL = 12


# ------------------------------------------------------------------------------- plain graph tools, own code
def fwd(arcs, srcs, allow):
    seen = {s for s in srcs if s in allow}
    st = list(seen)
    while st:
        u = st.pop()
        for v in arcs.get(u, ()):
            if v in allow and v not in seen:
                seen.add(v)
                st.append(v)
    return seen


def rev_arcs(arcs):
    r = collections.defaultdict(set)
    for u, vs in arcs.items():
        for v in vs:
            r[v].add(u)
    return r


def scc_list(arcs, allow, rev=None):
    """Kosaraju, iterative."""
    rev = rev if rev is not None else rev_arcs(arcs)
    seen, order = set(), []
    for s in allow:
        if s in seen:
            continue
        seen.add(s)
        st = [(s, iter(arcs.get(s, ())))]
        while st:
            u, it = st[-1]
            for v in it:
                if v in allow and v not in seen:
                    seen.add(v)
                    st.append((v, iter(arcs.get(v, ()))))
                    break
            else:
                st.pop()
                order.append(u)
    out, done = [], set()
    for s in reversed(order):
        if s in done:
            continue
        c = {s}
        done.add(s)
        st = [s]
        while st:
            u = st.pop()
            for v in rev.get(u, ()):
                if v in allow and v not in done:
                    done.add(v)
                    c.add(v)
                    st.append(v)
        out.append(c)
    return out


def und(arcs, allow):
    a = collections.defaultdict(set)
    for u in allow:
        for v in arcs.get(u, ()):
            if v in allow:
                a[u].add(v)
                a[v].add(u)
    return a


def comps(adj, allow):
    left, out = set(allow), []
    while left:
        s = left.pop()
        c = {s}
        st = [s]
        while st:
            u = st.pop()
            for v in adj.get(u, ()):
                if v in left:
                    left.discard(v)
                    c.add(v)
                    st.append(v)
        out.append(c)
    return out


def tree_path(par, v):
    p = [v]
    while p[-1] in par:
        p.append(par[p[-1]])
    return p[::-1]


def out_tree(z, Q, arcs, rng, how=None):
    """A spanning out-tree of D[Q]: any spanning out-tree can come out of shape 'any'."""
    how = how or rng.choice(['bfs', 'dfs', 'any', 'any', 'rand', 'long'])
    par, seen = {}, {z}
    if how == 'bfs':
        fr = [z]
        for u in fr:
            vs = [v for v in arcs.get(u, ()) if v in Q and v not in seen]
            rng.shuffle(vs)
            for v in vs:
                seen.add(v)
                par[v] = u
                fr.append(v)
        return par
    if how in ('dfs', 'long'):
        # a real DFS tree, the longest paths of the family
        st = [(z, None)]
        stack = [z]
        while stack:
            u = stack[-1]
            vs = [v for v in arcs.get(u, ()) if v in Q and v not in seen]
            if not vs:
                stack.pop()
                continue
            v = rng.choice(vs)
            seen.add(v)
            par[v] = u
            stack.append(v)
        return par
    fr = [(z, v) for v in arcs.get(z, ()) if v in Q]
    while fr:
        i = rng.randrange(len(fr)) if how == 'any' else (len(fr) - 1 if rng.random() < .7 else 0)
        fr[i], fr[-1] = fr[-1], fr[i]
        u, v = fr.pop()
        if v in seen:
            continue
        seen.add(v)
        par[v] = u
        fr += [(v, w) for w in arcs.get(v, ()) if w in Q and w not in seen]
    return par


def replay(kids, root, arcs, allv):
    """A real search that follows the children in order, and must find no unvisited head when it leaves a vertex. Returns error count, pre, post."""
    seen = {root}
    pre, post = {root: 0}, {}
    st = [(root, iter(kids.get(root, ())))]
    err = 0
    while st:
        u, it = st[-1]
        c = next(it, None)
        if c is None:
            st.pop()
            post[u] = len(post)
            err += sum(1 for v in arcs.get(u, ()) if v not in seen)
        else:
            if c in seen or c not in arcs.get(u, ()):
                err += 1
                continue
            seen.add(c)
            pre[c] = len(pre)
            st.append((c, iter(kids.get(c, ()))))
    if seen != allv:
        err += 1
    return err, pre, post


def t2_numbers(kids, root):
    """(T2) with the formulas of notes/DIRECTED.md: pre = e + depth, post = e + size - 1, e = sum over the root path of the sizes of earlier siblings."""
    order, stack = [], [root]
    par = {}
    while stack:
        u = stack.pop()
        order.append(u)
        for c in kids.get(u, ()):
            par[c] = u
            stack.append(c)
    size = collections.Counter()
    for u in reversed(order):
        size[u] += 1
        if u in par:
            size[par[u]] += size[u]
    e, depth = {root: 0}, {root: 0}
    for u in order:
        acc = 0
        for c in kids.get(u, ()):
            e[c] = e[u] + acc
            depth[c] = depth[u] + 1
            acc += size[c]
    return {u: e[u] + depth[u] for u in order}, {u: e[u] + size[u] - 1 for u in order}


# ------------------------------------------------------------------------------- instances, every one checked planar
def mk():
    return collections.defaultdict(set)


def orient(a, u, v, rng, pbi):
    r = rng.random()
    if r < pbi:
        a[u].add(v)
        a[v].add(u)
    elif rng.random() < .5:
        a[u].add(v)
    else:
        a[v].add(u)


def grid(rng, a_, b_, pbi, diag=0.0):
    A = mk()
    for i in range(a_):
        for j in range(b_):
            u = i * b_ + j
            if j + 1 < b_:
                orient(A, u, u + 1, rng, pbi)
            if i + 1 < a_:
                orient(A, u, u + b_, rng, pbi)
            if j + 1 < b_ and i + 1 < a_ and rng.random() < diag:
                orient(A, u, u + b_ + 1, rng, pbi)
    return A


def stacked(rng, m, pbi):
    """A random stacked triangulation."""
    A, tris = mk(), [(0, 1, 2)]
    for u, v in ((0, 1), (1, 2), (0, 2)):
        orient(A, u, v, rng, pbi)
    for x in range(3, m):
        i = rng.randrange(len(tris))
        t = tris[i]
        tris[i] = tris[-1]
        tris.pop()
        for y in t:
            orient(A, x, y, rng, pbi)
        tris += [(t[0], t[1], x), (t[1], t[2], x), (t[0], t[2], x)]
    return A


def rings(rng, r, l, inward):
    """Concentric directed rings with spokes, strongly connected when inward and outward spokes both exist."""
    A = mk()
    idx = lambda i, j: i * l + j % l
    for i in range(r):
        d = rng.random() < .5
        for j in range(l):
            u, v = idx(i, j), idx(i, j + 1)
            if d:
                A[u].add(v)
            else:
                A[v].add(u)
        if i + 1 < r:
            for j in range(l):
                if rng.random() < inward:
                    A[idx(i, j)].add(idx(i + 1, j))
                if rng.random() < inward * .7:
                    A[idx(i + 1, j)].add(idx(i, j))
    return A


def flower(rng, p, l):
    A = mk()
    c, nx_ = 0, 1
    tips = []
    for _ in range(p):
        cyc = [c] + list(range(nx_, nx_ + l - 1))
        nx_ += l - 1
        for u, v in zip(cyc, cyc[1:] + cyc[:1]):
            A[u].add(v)
        tips.append(cyc[len(cyc) // 2])
    return A


def biladder(rng, k):
    A = mk()
    for i in range(k - 1):
        for s in (0, 1):
            A[2 * i + s].add(2 * i + 2 + s)
            A[2 * i + 2 + s].add(2 * i + s)
    for i in range(k):
        A[2 * i].add(2 * i + 1)
        A[2 * i + 1].add(2 * i)
    return A


def cyclechain(rng, m, g):
    """A directed chain of g-cycles joined by single arcs."""
    A, prev = mk(), None
    x = 0
    for _ in range(m):
        cyc = list(range(x, x + g))
        x += g
        for u, v in zip(cyc, cyc[1:] + cyc[:1]):
            A[u].add(v)
        if prev is not None:
            A[prev].add(cyc[0])
        prev = cyc[g // 2]
    return A


def with_stars(rng, A, frac, big):
    """Add pendant sinks at random vertices. Pendant sinks are what makes vertices low: with |Q| <= 16 nothing is low."""
    V = sorted(set(A) | {v for vs in A.values() for v in vs})
    x = (max(V) if V else 0) + 1
    if not V:
        return A
    t = rng.randrange(1, max(2, int(len(V) * frac) + 1))
    for _ in range(t):
        h = rng.choice(V)
        for _ in range(rng.randrange(1, big + 1)):
            A[h].add(x)
            x += 1
    return A


def nest_exit(rng, s, k):
    """A bidirected s by s grid with one exit vertex to a star of k leaves. L shrinks by the cycle, the reach stays huge, so passes pile up."""
    A = grid(rng, s, s, 1.0)
    e = rng.randrange(s * s)
    x = s * s
    for _ in range(k):
        A[e].add(x)
        x += 1
    return A


def nest2(rng, depth, s0, k):
    """Nested bidirected rings with a star at the centre vertex: the strong component must be cut many times around the centre."""
    A = mk()
    base = 0
    rs = []
    for d in range(depth):
        l = max(3, s0 - d)
        ring = list(range(base, base + l))
        base += l
        for u, v in zip(ring, ring[1:] + ring[:1]):
            A[u].add(v)
            A[v].add(u)
        rs.append(ring)
    for r1, r2 in zip(rs, rs[1:]):
        for i in range(0, len(r2), max(1, len(r2) // 3)):
            u, v = r1[i * len(r1) // len(r2)], r2[i]
            A[u].add(v)
            A[v].add(u)
    c = rs[-1][0]
    for _ in range(k):
        A[c].add(base)
        base += 1
    return A


NEST_ONLY = False


def instance_nest(rng):
    """Instances built to make Lemma 6 work hard: a large strong component with one or a few exits to stars, so that the component is cut many times."""
    c = rng.randrange(5)
    s = rng.randrange(5, 34)
    if c == 0:
        A = grid(rng, s, s, rng.choice([1, 1, .97, .93]))
    elif c == 1:
        A = stacked(rng, s * s, rng.choice([1, 1, .95]))
    elif c == 2:
        A = biladder(rng, s * s // 2)
    elif c == 3:
        A = rings(rng, s // 2 + 2, s, .8)
    else:
        A = nest2(rng, s // 2 + 2, s + 3, 1)
    V = sorted(set(A) | {v for vs in A.values() for v in vs})
    x = max(V) + 1
    # the star holds most of the mass, spread on few hubs which are all reached late: each hub is a small part
    hubs_ = rng.sample(V, min(len(V), rng.choice([1, 1, 2, 3, 5])))
    k = rng.choice([1, 2, 4, 8]) * len(V)
    for h in hubs_:
        for _ in range(k // len(hubs_)):
            A[h].add(x)
            x += 1
    return 'nestonly', {u: set(v) for u, v in A.items()}


def instance(rng, big):
    if NEST_ONLY:
        return instance_nest(rng)
    s = 30 if big else 14
    c = rng.randrange(10)
    star = rng.random() < .75
    if c == 0:
        A, name = grid(rng, rng.randrange(2, s), rng.randrange(2, s), rng.choice([1, .9, .7, .5, .2, 0]), rng.choice([0, .3, .8])), 'grid'
    elif c == 1:
        A, name = stacked(rng, rng.randrange(4, s * s // 2), rng.choice([1, .8, .5, .2])), 'stacked'
    elif c == 2:
        A, name = rings(rng, rng.randrange(2, s // 2 + 2), rng.randrange(3, s), rng.choice([.2, .5, .9])), 'rings'
    elif c == 3:
        A, name = flower(rng, rng.randrange(2, s), rng.randrange(3, s)), 'flower'
    elif c == 4:
        A, name = biladder(rng, rng.randrange(3, 3 * s)), 'biladder'
    elif c == 5:
        A, name = cyclechain(rng, rng.randrange(2, s), rng.randrange(2, s // 2 + 2)), 'chain'
    elif c == 6:
        z = rng.randrange(3, s // 2 + 3)
        A, name = nest_exit(rng, z, rng.randrange(1, 8 * z * z)), 'nest_exit'
        star = False
    elif c == 7:
        A, name = nest2(rng, rng.randrange(2, s // 2 + 3), rng.randrange(5, s), rng.randrange(1, 12 * s)), 'nest2'
        star = False
    elif c == 8:
        A, name = grid(rng, rng.randrange(2, s), rng.randrange(2, s), 1.0), 'bigrid'
    else:
        A, name = stacked(rng, rng.randrange(4, s * s // 2), 1.0), 'bistack'
    if star:
        A = with_stars(rng, A, rng.choice([.02, .1, .3]), rng.choice([2, 6, 20, 60]))
    return name, {u: set(v) for u, v in A.items()}


def check_planar(arcs):
    G = nx.Graph()
    for u, vs in arcs.items():
        G.add_node(u)
        for v in vs:
            G.add_edge(u, v)
    ok, emb = nx.check_planarity(G)
    if ok and G.number_of_nodes() >= 3 and G.number_of_edges() > 3 * G.number_of_nodes() - 6:
        raise RuntimeError('nx disagrees with Euler')
    return ok, G, emb


# ------------------------------------------------------------------------------- separator (S): any tree path that meets 3/4, worst-case choice
def tree_path_set(par, u, v):
    pu, pv = tree_path(par, u), tree_path(par, v)
    a = {x: i for i, x in enumerate(pu)}
    lca = next(x for x in reversed(pv) if x in a)
    return pu[a[lca]:], pv[pv.index(lca) + 1:], lca


def separator(Q, par, arcs, st, rng, mode):
    """Returns (u, v), the ends of a path of F whose removal leaves underlying components of D[Q] of at most 3/4. Search: all pairs for small sets, else
    fundamental cycles of a triangulation plus random pairs. Choice among the valid: random, or the worst for the algorithm."""
    adj = und(arcs, Q)
    Ql = sorted(Q)
    N = len(Ql)
    if N <= 40:
        cand = [(a, b) for i, a in enumerate(Ql) for b in Ql[i:]]
        rng.shuffle(cand)
    else:
        G = nx.Graph()
        G.add_nodes_from(Ql)
        for u in Ql:
            for v in adj[u]:
                G.add_edge(u, v)
        ok, emb = nx.check_planarity(G)
        if not ok:
            st['FAIL.not_planar'] += 1
        tri, _ = nx.algorithms.planar_drawing.triangulate_embedding(emb, True)
        cand = list(tri.edges())
        rng.shuffle(cand)
        cand = cand[:30] + [(rng.choice(Ql), rng.choice(Ql)) for _ in range(10)] + cand[30:]
    valid = []
    choice = rng.choice(['first', 'first', 'worst', 'smallP'])
    for a, b in cand:
        x, y, lca = tree_path_set(par, a, b)
        P = set(x) | set(y)
        big = max((len(c) for c in comps(adj, Q - P)), default=0)
        if mode == 'c_badsep' or 4 * big <= 3 * N:
            valid.append((big, len(P), a, b))
            if choice == 'first' or (N > 40 and len(valid) > 8):
                break
    if not valid:
        st['FAIL.no_separator'] += 1
        return None
    st['sep.pairs_valid'] += len(valid)
    if choice == 'worst':
        got = max(valid)
    elif choice == 'smallP':
        got = min(valid, key=lambda t: t[1])
    else:
        got = valid[0]
    st['max.sep_side_pct'] = max(st['max.sep_side_pct'], 100 * got[0] // N)
    return got[2], got[3]


# ------------------------------------------------------------------------------- lockstep driver
class Lockstep:
    """Parts are generators. They yield requests, and all parts that ask are served by one global call per kind."""

    def __init__(self, st, base):
        self.st, self.base = st, base

    def run(self, gens):
        st = self.st
        pend = {}
        res = {}
        for k, g in gens.items():
            try:
                pend[k] = next(g)
            except StopIteration as e:
                res[k] = e.value
        while pend:
            kinds = collections.defaultdict(list)
            for k, r in pend.items():
                kinds[r[0]].append(k)
            kind = sorted(kinds)[0]
            who = kinds[kind]
            answers = self.serve(kind, {k: pend[k] for k in who})
            for k in who:
                try:
                    pend[k] = gens[k].send(answers[k])
                except StopIteration as e:
                    del pend[k]
                    res[k] = e.value
        return res

    def serve(self, kind, reqs):
        st, arcs = self.st, self.base
        out = {}
        if kind == 'test':
            # one computation of identifiers on the union of the digraphs D[L \ S], sizes by (P), one aggregate per L
            st['call.scc'] += 1
            st['call.pa'] += 2
            allow = set()
            own = {}
            for k, (_, L, S, th) in reqs.items():
                x = L - S
                allow |= x
                for v in x:
                    own[v] = k
            restr = {u: {v for v in arcs.get(u, ()) if v in allow and own.get(v) == own[u]} for u in allow}
            for c in scc_list(restr, allow):
                k = own[next(iter(c))]
                L, th = reqs[k][1], reqs[k][3]
                if th[1] * len(c) > th[0] * len(L):
                    if k in out:
                        st['FAIL.two_heavy'] += 1
                    out[k] = c
            for k in reqs:
                out.setdefault(k, None)
            return out
        if kind == 'forest':
            # one Out-Forest Theorem, on the union of the digraphs (reversed if asked); forward and reversed parts in one call would still be one digraph on G
            st['call.forest'] += 1
            for k, (_, z, X, rv, rng) in reqs.items():
                a = rev_arcs({u: arcs.get(u, ()) for u in X}) if rv else arcs
                par = out_tree(z, X, a, rng)
                if set(par) | {z} != X:
                    st['FAIL.forest_not_spanning'] += 1
                out[k] = par
            st['call.t2'] += 1
            return out
        if kind == 'sep':
            st['call.sep'] += 1
            st['call.pa'] += 1
            for k, (_, Q, par, rng, mode) in reqs.items():
                out[k] = separator(Q, par, arcs, st, rng, mode)
            return out
        if kind == 'pa':
            st['call.pa'] += 1
            for k in reqs:
                out[k] = None
            return out
        raise ValueError(kind)


# ------------------------------------------------------------------------------- Lemma 3 and Corollary 4, as a part
def least_gen(lo, hi, L, mk_set, th):
    """Least i in lo..hi with no heavy left for mk_set(i). Binary search. Returns i."""
    while lo < hi:
        m = (lo + hi) // 2
        h = yield ('test', L, mk_set(m), th)
        if h is not None:
            lo = m + 1
        else:
            hi = m
    return lo


def trim_gen(L, P, O, th, st):
    if not P:
        h = yield ('test', L, set(O), th)
        if h is not None:
            st['FAIL.trim_empty_heavy'] += 1
        return [], None, None
    h = yield ('test', L, set(O), th)
    if h is None:
        return [], None, None
    pos = {v: i for i, v in enumerate(P)}
    i = yield from least_gen(0, len(P) - 1, L, lambda m: set(O) | {v for v in P if pos[v] <= m}, th)
    X = yield ('test', L, set(O) | {v for v in P if pos[v] < i}, th)
    if X is None or P[i] not in X:
        st['FAIL.trim_X'] += 1
    # h greatest with none for p_h..p_i: search d = i - h
    d = yield from least_gen(0, i, L, lambda m: set(O) | {v for v in P if i - m <= pos[v] <= i}, th)
    h_ = i - d
    Y = yield ('test', L, set(O) | {v for v in P if h_ < pos[v] <= i}, th)
    if Y is None or P[h_] not in Y:
        st['FAIL.trim_Y'] += 1
    return P[h_:i + 1], X, Y


def link_gen(a, X, b, Y, arcs, rng, st, forbid):
    """A simple path from a through X to the meeting vertex and through Y to b, with positions from depth alone."""
    both = X & Y
    if not both:
        st['FAIL.heavy_disjoint'] += 1
        return None
    w = min(both)  # an aggregate over L
    p1 = yield ('forest', a, X, False, rng)
    p2 = yield ('forest', b, Y, True, rng)
    first, second = tree_path(p1, w), tree_path(p2, w)[::-1]
    on2 = {v: i for i, v in enumerate(second)}
    k = next(i for i, v in enumerate(first) if v in on2)  # an aggregate of the marks, by position on the first path
    q = first[:k] + second[on2[first[k]]:]
    yield ('pa', )
    # who knows what: depth on the first tree and on the reversed tree give the position of each vertex
    d1 = {a: 0}
    for x in first[1:]:
        d1[x] = d1[p1[x]] + 1
    d2 = {b: 0}
    for x in reversed(second[:-1]):
        d2[x] = d2[p2[x]] + 1
    wprime = first[k]
    for i, x in enumerate(q):
        guess = d1[x] if i <= k else d1[wprime] + d2[wprime] - d2[x]
        if guess != i:
            st['FAIL.position_on_link'] += 1
    if len(set(q)) != len(q) or q[0] != a or q[-1] != b or set(q[1:-1]) & forbid:
        st['FAIL.link_shape'] += 1
    for u, v in zip(q, q[1:]):
        if v not in arcs.get(u, ()):
            st['FAIL.link_arc'] += 1
    return q


def close_gen(U, L, arcs, th, rng, st):
    pos = {v: i for i, v in enumerate(U)}
    t = yield from least_gen(0, len(U) - 1, L, lambda m: {v for v in U if pos[v] <= m}, th)
    X = yield ('test', L, {v for v in U if pos[v] < t}, th)
    d = yield from least_gen(0, t, L, lambda m: {v for v in U if t - m <= pos[v] <= t}, th)
    s = t - d
    if s == t:
        return [U[t]]
    Y = yield ('test', L, {v for v in U if s < pos[v] <= t}, th)
    if X is None or Y is None or U[t] not in X or U[s] not in Y or U[s] in X or U[t] in Y:
        st['FAIL.close_ends'] += 1
    q = yield from link_gen(U[t], X, U[s], Y, arcs, rng, st, set(U[s:t + 1]))
    if q is None:
        return U[s:t + 1]
    return U[s:t + 1] + q[1:-1]


def search_tree_small(r, L, arcs, rng):
    """A depth-first search of D[L], with the last-visit order."""
    seen, par, post = {r}, {}, []
    stack = [(r, None)]
    st = [r]
    while st:
        u = st[-1]
        vs = [v for v in arcs.get(u, ()) if v in L and v not in seen]
        if vs:
            v = rng.choice(vs)
            seen.add(v)
            par[v] = u
            st.append(v)
        else:
            st.pop()
            post.append(u)
    return par, post


def cor4_gen(L, arcs, rng, st, mode, th):
    """Corollary 4 for one strongly connected L. Yields requests, returns the cycle."""
    N = len(L)
    if N == 1:
        return list(L)
    r = min(L)
    if N < SMALL:
        par, post = search_tree_small(r, L, arcs, rng)
        v = post[(N + 1) // 2 - 1]
        A, B = tree_path(par, v), []
        big = max((len(c) for c in scc_list(arcs, L - set(A))), default=0)
        st['chk.kao_half'] += 1
        if 2 * big > N:
            st['FAIL.kao_half'] += 1
    else:
        par = yield ('forest', r, L, False, rng)
        got = yield ('sep', L, par, rng, mode)
        if got is None:
            st['FAIL.cor4_no_sep'] += 1
            return [r]
        x, y, lca = tree_path_set(par, *got)
        if rng.random() < .5:
            A, B = x, y
        else:
            A, B = [lca] + y, x[1:]
        if mode == 'c_onepath_cycle':
            B = []
    A1, X1, _ = yield from trim_gen(L, A, set(B), th, st)
    B1, _, Y2 = yield from trim_gen(L, B, set(A1), th, st)
    if not A1 and not B1:
        st['FAIL.both_dropped'] += 1
        return [r]
    if not A1 or not B1:
        U = A1 or B1
    else:
        q = yield from link_gen(A1[-1], X1, B1[0], Y2, arcs, rng, st, set(A1) | set(B1))
        if q is None:
            return [r]
        U = A1 + q[1:-1] + B1
    if len(set(U)) != len(U) or any(v not in arcs.get(u, ()) for u, v in zip(U, U[1:])):
        st['FAIL.U_not_path'] += 1
    h = yield ('test', L, set(U), th)
    if h is not None:
        st['FAIL.U_heavy'] += 1
        if mode == 'c_onepath_cycle':
            return U[:1]
    C = yield from close_gen(U, L, arcs, th, rng, st)
    return C


# ------------------------------------------------------------------------------- Split Lemma: bit search, then a literal check
def split_part(Q, R, arcs, st, nkey):
    """Keys, classes by the literal definition. Returns list of (head, tail, K), and key of each head."""
    rest = Q - set(R)
    k = len(R) - 1
    key, tail = {}, {}
    for i, v in enumerate(R):
        for z in arcs.get(v, ()):
            if z in rest:
                c = (k - i) * nkey + z
                if z not in key or c < key[z]:
                    key[z], tail[z] = c, v
    return rest, key, tail


def split_global(parts, arcs, st, nkey, check=True, mode=None):
    """parts: list of (Q, R). One global bit search with the Multi-Source Lemma on the kept arcs. A class is what the search says."""
    allrest = {}
    keys, tails = {}, {}
    for ix, (Q, R) in enumerate(parts):
        rest, key, tail = split_part(Q, R, arcs, st, nkey)
        for v in rest:
            allrest[v] = ix
        keys.update(key)
        tails.update(tail)
    if mode == 'c_shallow':
        # control: shallow vertices of the path first
        keys = {}
        tails = {}
        for ix, (Q, R) in enumerate(parts):
            rest = Q - set(R)
            for i, v in enumerate(R):
                for z in arcs.get(v, ()):
                    if z in rest and (z not in keys or i * nkey + z < keys[z]):
                        keys[z], tails[z] = i * nkey + z, v
    b = max((c for c in keys.values()), default=1).bit_length()
    pre = {v: 0 for v in allrest}
    for bit in range(b, 0, -1):
        st['call.ms'] += 1
        kept = collections.defaultdict(set)
        for u in allrest:
            for v in arcs.get(u, ()):
                if v in allrest and allrest[v] == allrest[u] and pre[u] == pre[v]:
                    kept[u].add(v)
        src = [z for z, c in keys.items() if c >> bit == pre[z] and not (c >> (bit - 1)) & 1]
        got = fwd(kept, src, set(allrest))
        for y in allrest:
            pre[y] = 2 * pre[y] + (0 if y in got else 1)
    # literal definition
    if check:
        st['chk.bitsearch'] += 1
        for ix, (Q, R) in enumerate(parts):
            rest = Q - set(R)
            local = {}
            sub = {u: {v for v in arcs.get(u, ()) if v in rest} for u in rest}
            for z in sorted((z for z in keys if z in rest), key=keys.get):
                for y in fwd(sub, [z], rest):
                    if y not in local:
                        local[y] = keys[z]
            if any(local.get(y) != pre[y] for y in rest):
                st['FAIL.bitsearch'] += 1
    st['call.pa'] += 1
    out = [[] for _ in parts]
    groups = collections.defaultdict(set)
    for y, c in pre.items():
        groups[(allrest[y], c)].add(y)
    for z, c in keys.items():
        if z in pre and pre[z] == c:
            ix = allrest[z]
            K = groups[(ix, c)]
            out[ix].append((z, tails[z], K, c))
    for ix, (Q, R) in enumerate(parts):
        rest = Q - set(R)
        cov = set()
        for z, t, K, c in out[ix]:
            if cov & K:
                st['FAIL.split_overlap'] += 1
            cov |= K
            sub = {u: {v for v in arcs.get(u, ()) if v in K} for u in K}
            if fwd(sub, [z], K) != K:
                st['FAIL.class_not_rooted'] += 1
        if cov != rest:
            st['FAIL.split_cover'] += 1
    return out


# ------------------------------------------------------------------------------- the algorithm
def engine(arcs, root, rng, st, mode='ok', small=SMALL):
    V = set(arcs) | {v for vs in arcs.values() for v in vs} | {root}
    n = len(V)
    nkey = max(V) + 2
    K0 = fwd(arcs, [root], V)
    kids = collections.defaultdict(list)
    th = (3, 4) if mode != 'c_theta' else (1, 3)
    probs = [(root, K0)]
    lock = Lockstep(st, arcs)
    limit = math.log(max(n, 2), 4 / 3) + 2
    level = 0
    H_NUM, H_DEN = (7, 8)
    LOW_NUM = 16
    BAD_NUM, BAD_DEN = (15, 16)
    if mode == 'c_a13':
        H_NUM, H_DEN = (13, 16)
    if mode == 'c_bad34':
        BAD_NUM, BAD_DEN = (3, 4)
    while probs:
        level += 1
        st['call.pa'] += 1
        next_probs = []
        active = []  # dicts: W, classes, passes, prevL
        for x, K in probs:
            if len(K) < small:
                sub = {u: {v for v in arcs.get(u, ()) if v in K} for u in K}
                seen = {x}
                stack = [x]
                while stack:
                    u = stack[-1]
                    vs = [v for v in sub[u] if v not in seen]
                    if vs:
                        v = rng.choice(vs)
                        seen.add(v)
                        kids[u].append(v)
                        stack.append(v)
                    else:
                        stack.pop()
                if seen != K:
                    st['FAIL.small_not_reached'] += 1
            else:
                active.append({'W': len(K), 'classes': [(x, K)], 'passes': 0, 'prevL': None, 'prevLC': None})
        while True:
            bads = []
            for a in active:
                b = [c for c in a['classes'] if BAD_DEN * len(c[1]) > BAD_NUM * a['W']]
                if len(b) > 1:
                    st['FAIL.two_bad'] += 1
                if b:
                    bads.append((a, b[0]))
            if not bads:
                break
            # ---- one pass, for all at once
            st['n.global_passes'] += 1
            infos = []
            st['call.forest'] += 1
            st['call.t2'] += 1
            st['call.sep'] += 1
            st['call.pa'] += 1
            for a, (z, Q) in bads:
                a['classes'].remove((z, Q))
                a['passes'] += 1
                W = a['W']
                if a['passes'] > limit:
                    st['FAIL.passes_bound'] += 1
                if len(Q) < 12 and small == SMALL:
                    st['FAIL.bad_below_12'] += 1
                F = out_tree(z, Q, arcs, rng)
                if set(F) | {z} != Q:
                    st['FAIL.forest_not_spanning'] += 1
                sp = separator(Q, F, arcs, st, rng, mode)
                if sp is None:
                    sp = (z, z)
                pi1, pi2 = tree_path(F, sp[0]), tree_path(F, sp[1])
                if mode == 'c_onepath_pivot':
                    pi2 = pi1
                infos.append(dict(a=a, z=z, Q=Q, W=W, F=F, pi=[pi1, pi2]))
            # ---- step 2: binary search on each path, in lockstep, one Multi-Source run and one count per step
            sub = {}
            for info in infos:
                Q = info['Q']
                for u in Q:
                    sub[u] = {v for v in arcs.get(u, ()) if v in Q}
            for t in (0, 1):
                state = {id(i): (0, len(i['pi'][t]) - 1) for i in infos}  # last high index is in [lo, hi]
                while any(lo < hi for lo, hi in state.values()):
                    st['call.ms'] += 1
                    st['call.pa'] += 1
                    srcs = {}
                    for info in infos:
                        lo, hi = state[id(info)]
                        if lo < hi:
                            m = (lo + hi + 1) // 2
                            v = info['pi'][t][m]
                            srcs[id(info)] = (m, v)
                    # one union run: a vertex learns whether some source reaches it, and each class counts its own
                    got = fwd(sub, [v for m, v in srcs.values()], set(sub))
                    for info in infos:
                        if id(info) in srcs:
                            m, v = srcs[id(info)]
                            cnt = len(got & info['Q'])
                            lo, hi = state[id(info)]
                            if H_DEN * cnt > H_NUM * info['W']:
                                state[id(info)] = (m, hi)
                            else:
                                state[id(info)] = (lo, m - 1)
                for info in infos:
                    i = state[id(info)][0]
                    pi = info['pi'][t]
                    info.setdefault('c', {})[t] = pi[i]
                    info.setdefault('n', {})[t] = pi[i + 1] if i + 1 < len(pi) else None
                    info.setdefault('ci', {})[t] = i
            # the counts of c_i and n_i are one more run each
            st['call.ms'] += 2
            st['call.pa'] += 2
            for info in infos:
                Q, W = info['Q'], info['W']
                rq = lambda v: fwd(sub, [v], Q)
                f = {}
                # direct check of the search
                for t in (0, 1):
                    pi, i = info['pi'][t], info['ci'][t]
                    hs = [H_DEN * len(rq(v)) > H_NUM * W for v in pi]
                    if not hs[0]:
                        st['FAIL.root_not_high'] += 1
                    if not (hs[i] and (i + 1 == len(pi) or not hs[i + 1])) or sum(hs) != i + 1:
                        st['FAIL.binary_search'] += 1
                mid = None
                for t in (0, 1):
                    m = info['n'][t]
                    if m is not None and 16 * len(rq(m)) >= W:
                        mid = t
                        break
                if mode == 'c_nomid':
                    mid = None
                info['mid'] = mid
            # ---- step 3 and 4
            # one union computation of identifiers, and two Multi-Source runs
            st['call.ms'] += 2
            st['call.scc'] += 1
            st['call.pa'] += 2
            comps_all = {}
            pend = [i for i in infos if i['mid'] is None]
            if pend:
                allow = set().union(*(i['Q'] for i in pend))
                for c in scc_list(sub, allow):
                    for v in c:
                        comps_all[v] = c
            gens = {}
            for ix, info in enumerate(infos):
                if info['mid'] is not None:
                    st['n.step3'] += 1
                    t = info['mid']
                    pi, i = info['pi'][t], info['ci'][t]
                    info['R'] = pi[:i + 2]
                    info['L'] = None
                    continue
                st['n.step4'] += 1
                Q, W = info['Q'], info['W']
                c1, c2 = info['c'][0], info['c'][1]
                r1 = fwd(sub, [c1], Q)
                r2 = fwd(sub, [c2], Q)
                first_case = c2 in r1 and c1 not in r2
                pick = c2 if first_case else c1
                if mode == 'c_wrongrule':
                    pick = c1 if first_case else c2
                L = comps_all[pick]
                info['L'] = L
                info['pick'] = pick
                # Lemma 2, direct
                st['chk.lemma2'] += 1
                if H_DEN * len(fwd(sub, [pick], Q)) <= H_NUM * W:
                    st['FAIL.L_no_high'] += 1
                for y in fwd(sub, [pick], Q) - L:
                    st['chk.lemma2_v'] += 1
                    if H_DEN * len(fwd(sub, [y], Q)) > H_NUM * W:
                        st['FAIL.below_high'] += 1
                        break
                a = info['a']
                # Lemma 5(b) and Lemma 6: the new L inside the old L minus C
                if a['prevLC'] is not None and a['prevL'] is not None:
                    st['chk.L_nested'] += 1
                    if not L <= a['prevLC']:
                        st['FAIL.L_not_nested'] += 1
                    if 4 * len(L) > 3 * a['prevL']:
                        st['FAIL.L_not_smaller'] += 1
                st['max.L_pct'] = max(st['max.L_pct'], 100 * len(L) // len(Q))
                if mode == 'c_nocycle':
                    def g0(L=L):
                        return [min(L)]
                        yield
                    gens[ix] = g0()
                else:
                    gens[ix] = cor4_gen(L, arcs, rng, st, mode, th)
            cyc = lock.run(gens)
            for ix, C in cyc.items():
                info = infos[ix]
                L, Q, F, z = info['L'], info['Q'], info['F'], info['z']
                st['chk.cycle'] += 1
                if len(set(C)) != len(C) or not set(C) <= L:
                    st['FAIL.cycle_set'] += 1
                if len(C) > 1 and any(v not in arcs.get(u, ()) for u, v in zip(C, C[1:] + C[:1])):
                    st['FAIL.cycle_arcs'] += 1
                left = scc_list(arcs, L - set(C))
                if any(4 * len(s) > 3 * len(L) for s in left):
                    st['FAIL.cycle_heavy'] += 1
                st['max.C_pct'] = max(st['max.C_pct'], 100 * len(C) // len(L))
                # depth by (T2); the least depth is an aggregate over Q
                dep = {z: 0}
                for v in sorted(F, key=lambda v: len(tree_path(F, v))):
                    dep[v] = dep[F[v]] + 1
                c = min(C, key=lambda v: dep[v])
                if mode == 'c_deepest':
                    c = max(C, key=lambda v: dep[v])
                k = C.index(c)
                head = tree_path(F, c)
                R = head + C[k + 1:] + C[:k]
                if mode == 'c_noaround':
                    R = head
                info['R'] = R
                # who knows what: position on R from depth(c), the position on C and the length of C
                pc = {v: i for i, v in enumerate(C)}
                for i, v in enumerate(R):
                    if v in pc and v != c:
                        guess = dep[c] + (pc[v] - pc[c]) % len(C)
                    else:
                        guess = dep[v]
                    if guess != i and mode == 'ok':
                        st['FAIL.position_on_R'] += 1
                info['C'] = set(C)
            # ---- step 5
            for info in infos:
                R, Q, z = info['R'], info['Q'], info['z']
                if len(set(R)) != len(R) or R[0] != z or any(v not in arcs.get(u, ()) for u, v in zip(R, R[1:])) or not set(R) <= Q:
                    st['FAIL.R_not_path'] += 1
            parts = [(i['Q'], i['R']) for i in infos]
            split = split_global(parts, arcs, st, nkey, rng.random() < .3, mode)
            for info, got in zip(infos, split):
                R, Q, W, a = info['R'], info['Q'], info['W'], info['a']
                m = R[-1]
                rm = fwd(sub, [m], Q)
                bwdm = fwd(rev_arcs({u: sub[u] for u in Q}), [m], Q)
                M = rm & bwdm
                for z, tl, K, c in got:
                    st['chk.lemma1'] += 1
                    if tl in M:
                        if not K <= rm:
                            st['FAIL.lemma1a'] += 1
                    elif K & rm:
                        st['FAIL.lemma1b'] += 1
                    if BAD_DEN * len(K) > BAD_NUM * W:
                        if info['L'] is None:
                            st['FAIL.lemma5a'] += 1
                        else:
                            st['chk.lemma5b_bad'] += 1
                            if tl not in info['L'] or z not in info['L']:
                                st['FAIL.lemma5b_tail'] += 1
                            sk = {u: {v for v in arcs.get(u, ()) if v in K} for u in K}
                            for sc in scc_list(sk, K):
                                v = next(iter(sc))
                                if H_DEN * len(fwd(sk, [v], K)) > H_NUM * W:
                                    st['chk.lemma5b_v'] += 1
                                    if not sc <= info['L'] - info['C'] or 4 * len(sc) > 3 * len(info['L']):
                                        st['FAIL.lemma5b'] += 1
                # tree
                pos = {v: i for i, v in enumerate(R)}
                heads = collections.defaultdict(list)
                for z, tl, K, c in sorted(got, key=lambda t: t[3]):
                    heads[tl].append(z)
                for i, v in enumerate(R):
                    kids[v] = ([R[i + 1]] if i + 1 < len(R) else []) + heads[v]
                a['classes'] += [(z, K) for z, tl, K, c in got]
                if info['L'] is not None:
                    a['prevL'], a['prevLC'] = len(info['L']), info['L'] - info['C']
                else:
                    a['prevL'], a['prevLC'] = None, None
                st['max.passes'] = max(st['max.passes'], a['passes'])
                st['max.passes_over_bound_pct'] = max(st['max.passes_over_bound_pct'], int(100 * a['passes'] / limit))
        for a in active:
            for z, K in a['classes']:
                st['chk.nextlevel'] += 1
                if 16 * len(K) > 15 * a['W'] and mode == 'ok':
                    st['FAIL.next_too_big'] += 1
            next_probs += a['classes']
        probs = next_probs
        if level > 400:
            st['FAIL.levels'] += 1
            break
    st['max.levels'] = max(st['max.levels'], level)
    return kids, K0


def source_roots(arcs, V, rng):
    cs = scc_list(arcs, set(V))
    own = {v: i for i, c in enumerate(cs) for v in c}
    has_in = set()
    for u in arcs:
        for v in arcs[u]:
            if own[u] != own[v]:
                has_in.add(own[v])
    return [min(c) for i, c in enumerate(cs) if i not in has_in]


def forest_check(arcs, V, rng, local, mode):
    """The forest of the theorem: a virtual vertex with an arc to one vertex of each source component, the order of the roots fixed first."""
    roots = source_roots(arcs, V, rng)
    rng.shuffle(roots)
    a2 = {u: set(vs) for u, vs in arcs.items()}
    virt = max(V) + 1
    a2[virt] = set(roots)
    # ids of roots must follow the fixed order: the key of a head in the Split Lemma has the identifier as second coordinate, so relabel by the order
    rank = {r: i for i, r in enumerate(roots)}
    left = set(V)
    kids_all = {}
    order = []
    for r in roots:
        K = fwd(arcs, [r], left)
        if r not in K:
            local['FAIL.root_stolen'] += 1
            continue
        sub = {u: {v for v in arcs.get(u, ()) if v in K} for u in K}
        order.append((r, K, sub))
        left -= K
    if left:
        local['FAIL.forest_cover'] += 1
    for r, K, sub in order:
        kids, K0 = engine(sub, r, rng, local, mode)
        if K0 != K:
            local['FAIL.forest_problem'] += 1
        kids_all.update(kids)
    # replay of the whole forest in order of roots
    seen = set()
    err = 0
    for r, K, sub in order:
        if r in seen:
            err += 1
        seen.add(r)
        st_ = [(r, iter(kids_all.get(r, ())))]
        while st_:
            u, it = st_[-1]
            c = next(it, None)
            if c is None:
                st_.pop()
                err += sum(1 for v in arcs.get(u, ()) if v not in seen)
            else:
                if c in seen or c not in arcs.get(u, ()):
                    err += 1
                    continue
                seen.add(c)
                st_.append((c, iter(kids_all.get(c, ()))))
    if seen != set(V):
        err += 1
    local['chk.forest_replay'] += 1
    if err:
        local['FAIL.forest_replay'] += 1


def run_one(rng, st, big, mode):
    name, arcs = instance(rng, big)
    ok, G, emb = check_planar(arcs)
    st['chk.planar'] += 1
    if not ok:
        st['FAIL.instance_not_planar'] += 1
        return
    V = sorted(G.nodes())
    if len(V) < 2:
        return
    root = rng.choice(V)
    local = collections.Counter()
    if rng.random() < .2:
        forest_check(arcs, V, rng, local, mode)
        for k, v in local.items():
            if k.startswith('max.'):
                st[k] = max(st[k], v)
            else:
                st[k] += v
        st['runs_forest'] += 1
        return
    kids, K0 = engine(arcs, root, rng, local, mode)
    err, pre, post = replay(kids, root, arcs, K0)
    local['chk.replay'] += 1
    if err:
        local['FAIL.replay'] += 1
    else:
        p2, q2 = t2_numbers(kids, root)
        if p2 != pre or q2 != post:
            local['FAIL.t2_numbers'] += 1
        for u in K0:
            for v in arcs.get(u, ()):
                if v in K0 and pre[v] > pre[u] and post[v] > post[u]:
                    local['FAIL.arc_right'] += 1
    for k, v in local.items():
        if k.startswith('max.'):
            st[k] = max(st[k], v)
        else:
            st[k] += v
    calls = sum(v for k, v in local.items() if k.startswith('call.'))
    st['max.calls'] = max(st['max.calls'], calls)
    if len(V) > 30:
        st['max.calls_over_log3_x100'] = max(st['max.calls_over_log3_x100'], int(100 * calls / math.log2(len(V)) ** 3))
    st['max.n'] = max(st['max.n'], len(V))
    st['max.K'] = max(st['max.K'], len(K0))
    st['runs'] += 1
    st['fam.' + name] += 1


def lane(seed, secs, big):
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    while time.time() - t0 < secs:
        run_one(rng, st, big, 'ok')
    return dict(sorted((k, int(v)) for k, v in st.items()))


CTL = ['c_shallow', 'c_wrongrule', 'c_nomid', 'c_onepath_pivot', 'c_nocycle', 'c_noaround', 'c_badsep', 'c_a13', 'c_bad34', 'c_deepest', 'c_theta', 'c_onepath_cycle']


def controls(seed, secs):
    out = {}
    for mode in CTL:
        rng = random.Random(seed)
        st = collections.Counter()
        t0 = time.time()
        crashes = 0
        while time.time() - t0 < secs:
            try:
                run_one(rng, st, True, mode)
            except Exception as e:
                crashes += 1
                st['crash.' + type(e).__name__] += 1
        out[mode] = {k: int(v) for k, v in st.items() if k.startswith('FAIL') or k.startswith('crash') or k == 'runs'}
    return out


def scale():
    rng = random.Random(1)
    fams = [('bigrid', lambda m: grid(rng, m, m, 1.0)), ('grid.7', lambda m: grid(rng, m, m, .7)), ('grid.3', lambda m: grid(rng, m, m, .3)),
            ('nest_exit', lambda m: nest_exit(rng, m, 8 * m * m)), ('nest2', lambda m: nest2(rng, m // 2, m + 5, 6 * m * m)),
            ('biladder', lambda m: biladder(rng, m * m // 2)), ('stacked1', lambda m: stacked(rng, m * m, 1.0)), ('stacked.5', lambda m: stacked(rng, m * m, .5))]
    for name, mk_ in fams:
        for m in (8, 16, 32, 64):
            st = collections.Counter()
            A = {u: set(v) for u, v in mk_(m).items()}
            ok, G, _ = check_planar(A)
            V = sorted(G.nodes())
            t0 = time.time()
            root = V[0]
            kids, K0 = engine(A, root, rng, st)
            err, _, _ = replay(kids, root, A, K0)
            fails = {k: v for k, v in st.items() if k.startswith('FAIL')}
            calls = {k[5:]: v for k, v in st.items() if k.startswith('call.')}
            tot = sum(calls.values())
            print(json.dumps({'fam': name, 'planar': ok, 'n': len(V), 'K': len(K0), 'levels': st['max.levels'], 'global_passes': st['n.global_passes'], 'max_passes': st['max.passes'],
                              'step3': st['n.step3'], 'step4': st['n.step4'], 'calls': calls, 'total': tot, 'tot_over_log2n_cubed': round(tot / math.log2(len(V)) ** 3, 2), 'replay_err': err, 'fails': fails, 'secs': round(time.time() - t0, 1)}), flush=True)


if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == 'main':
        print(json.dumps(lane(int(a[1]), float(a[2]), len(a) > 3)))
    elif a[0] == 'nest':
        NEST_ONLY = True
        print(json.dumps(lane(int(a[1]), float(a[2]), True)))
    elif a[0] == 'nestctl':
        NEST_ONLY = True
        print(json.dumps(controls(int(a[1]), float(a[2]))))
    elif a[0] == 'ctl':
        print(json.dumps(controls(int(a[1]), float(a[2]))))
    elif a[0] == 'scale':
        scale()
