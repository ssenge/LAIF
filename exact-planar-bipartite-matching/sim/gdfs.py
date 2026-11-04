"""Depth-first search of any planar digraph: centralized simulation of notes/GENERAL_DFS.md.

Checks the logic of the note. It does not simulate rounds: reachability and strong components are computed directly where
the note uses labels. The separator is a fundamental cycle of a triangulation, picked at random among the valid ones.
Every FAIL counter is a claim of the note.

python3 -I gdfs.py SEED SECS [big]    main lane
python3 -I gdfs.py ctl SEED SECS      negative controls
python3 -I gdfs.py scale              levels and passes against n on large instances
"""
import collections, json, math, os, random, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
import dagdfs as dd
import dirs

SMALL = 12
ON_PATH = ON_SMALL = None  # hooks for sim/dom.py


def sccs(arcs, allowed):
    """Strong components of the digraph on allowed, by Tarjan's algorithm with an explicit stack."""
    index, low, on, stack, out = {}, {}, set(), [], []
    n = 0
    for r in allowed:
        if r in index:
            continue
        index[r] = low[r] = n
        n += 1
        stack.append(r)
        on.add(r)
        work = [(r, iter(arcs.get(r, ())))]
        while work:
            u, it = work[-1]
            for v in it:
                if v not in allowed:
                    continue
                if v not in index:
                    index[v] = low[v] = n
                    n += 1
                    stack.append(v)
                    on.add(v)
                    work.append((v, iter(arcs.get(v, ()))))
                    break
                if v in on:
                    low[u] = min(low[u], index[v])
            else:
                work.pop()
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[u])
                if low[u] == index[u]:
                    c = set()
                    while True:
                        w = stack.pop()
                        on.discard(w)
                        c.add(w)
                        if w == u:
                            break
                    out.append(c)
    return out


def reverse(arcs):
    rev = collections.defaultdict(set)
    for u, vs in arcs.items():
        for v in vs:
            rev[v].add(u)
    return rev


def rand_separator(x, K, arcs, par, st, rng):
    """(S) with an worst-case flavour: any fundamental cycle whose removal leaves at most 3/4, at random. Returns two root paths."""
    U = nx.Graph()
    U.add_nodes_from(K)
    U.add_edges_from((u, v) for u in K for v in arcs.get(u, ()) if v in K)
    ok, emb = nx.check_planarity(U)
    if not ok:
        st['FAIL.not_planar'] += 1
    tri, _ = nx.algorithms.planar_drawing.triangulate_embedding(emb, True)
    tree = {frozenset((v, p)) for v, p in par.items()}
    cand = [e for e in tri.edges() if frozenset(e) not in tree]
    rng.shuffle(cand)
    best, pick = 10 ** 9, None
    for u, v in cand[:30]:
        pu, pv = dd.root_path(par, u), dd.root_path(par, v)
        P = set(pu) ^ set(pv)
        P.add([a for a, b in zip(pu, pv) if a == b][-1])
        big = max((len(c) for c in nx.connected_components(U.subgraph(K - P))), default=0)
        if big * 4 <= 3 * len(K):
            st['chk.balance'] += 1
            st['max.side_x100'] = max(st['max.side_x100'], 100 * big // len(K))
            return pu, pv
        if big < best:
            best, pick = big, (pu, pv)
    return dd.separator(x, K, arcs, par, st)


def small_path(r, L, arcs):
    """A set with fewer than SMALL vertices is solved at one vertex: the path of a search tree to the median in last-visit order, [Kao, Theorem 2]."""
    seen, post, par = {r}, [], {}

    def go(u):
        for v in sorted(arcs.get(u, ())):
            if v in L and v not in seen:
                seen.add(v)
                par[v] = u
                go(v)
        post.append(u)
    go(r)
    return dd.root_path(par, post[(len(post) - 1) // 2])


def over(L, S, arcs, st):
    """The strong component of D[L minus S] with more than 3/4 of L, or None. At most one exists."""
    st['n.scc_tests'] += 1
    for c in sccs(arcs, L - S):
        if len(c) * 4 > 3 * len(L):
            return c
    return None


def least(lo, hi, bad):
    """Least i in lo..hi with bad(i) false. bad(hi) is false, and bad is monotone."""
    while lo < hi:
        m = (lo + hi) // 2
        if bad(m):
            lo = m + 1
        else:
            hi = m
    return lo


def trim(P, other, L, arcs, st):
    """The Trim step: a segment of P, and the heavy components at its two ends. Empty if P is not needed."""
    if not P or not over(L, other, arcs, st):
        return [], None, None
    i = least(1, len(P), lambda i: over(L, other | set(P[:i]), arcs, st))
    X = over(L, other | set(P[:i - 1]), arcs, st)
    h = i - 1 - least(0, i - 1, lambda d: over(L, other | set(P[i - 1 - d:i]), arcs, st))
    Y = over(L, other | set(P[h + 1:i]), arcs, st)
    if P[i - 1] not in X or P[h] not in Y:
        st['FAIL.trim_end'] += 1
    return P[h:i], X, Y


def link(a, X, b, Y, arcs, st, rng):
    """A simple path from a through X to a vertex of both, then through Y to b. It avoids nothing else that X and Y avoid."""
    both = X & Y
    if not both:
        st['FAIL.heavy_disjoint'] += 1
        return None
    w = rng.choice(sorted(both))
    out = dd.out_tree(a, X, arcs, rng)
    inn = dd.out_tree(b, Y, reverse(arcs), rng)
    first = dd.root_path(out, w)
    second = dd.root_path(inn, w)[::-1]
    on = {v: i for i, v in enumerate(second)}
    k = next(i for i, v in enumerate(first) if v in on)
    return first[:k] + second[on[first[k]]:]


def cycle_of_path(U, L, arcs, st, rng, mode):
    """The Cycle step: from a path with no heavy component left to a simple directed cycle with the same property."""
    t = least(1, len(U), lambda i: over(L, set(U[:i]), arcs, st))
    X = over(L, set(U[:t - 1]), arcs, st)
    d = least(0, t - 1, lambda d: over(L, set(U[t - 1 - d:t]), arcs, st))
    s = t - 1 - d
    if s == t - 1:
        return [U[s]]
    Y = over(L, set(U[s + 1:t]), arcs, st)
    q = link(U[t - 1], X, U[s], Y, arcs, st, rng)
    if q is None:
        return U[s:t]
    if set(q[1:-1]) & set(U[s:t]):
        st['FAIL.link_hits_segment'] += 1
    return U[s:t] + q[1:-1]


def cycle_separator(L, arcs, st, rng, mode):
    """Cycle Lemma: a simple directed cycle of D[L], or one vertex, with no strong component of more than 3/4 of L left."""
    if len(L) == 1:
        return list(L)
    r = rng.choice(sorted(L))
    if len(L) < SMALL:
        U = small_path(r, L, arcs)
    else:
        par = dd.out_tree(r, L, arcs, rng)
        pu, pv = rand_separator(r, L, arcs, par, st, rng)
        k = sum(1 for a, b in zip(pu, pv) if a == b)
        A, B = pu[k - 1:], pv[k:]
        if mode == 'onepath_cycle':
            B = []
        if mode == 'nolink':
            U = A + B
        else:
            A2, X1, Y1 = trim(A, set(B), L, arcs, st)
            if not A2:
                U = trim(B, set(), L, arcs, st)[0]
            else:
                B2, X2, Y2 = trim(B, set(A2), L, arcs, st)
                if not B2:
                    U = A2
                else:
                    q = link(A2[-1], X1, B2[0], Y2, arcs, st, rng)
                    if q is None:
                        U = A2
                    else:
                        if (set(q[1:-1]) & (set(A2) | set(B2))):
                            st['FAIL.link_hits_segment'] += 1
                        U = A2 + q[1:-1] + B2
            if len(set(U)) != len(U) or any(v not in arcs.get(u, ()) for u, v in zip(U, U[1:])):
                st['FAIL.join_not_path'] += 1
    if mode == 'nolink' and (len(set(U)) != len(U) or any(v not in arcs.get(u, ()) for u, v in zip(U, U[1:]))):
        U = A
    if over(L, set(U), arcs, st):
        st['FAIL.join_heavy_left'] += 1
        return U[:1]
    C = cycle_of_path(U, L, arcs, st, rng, mode)
    st['chk.cycle'] += 1
    if len(set(C)) != len(C) or not set(C) <= L or any(v not in arcs.get(u, ()) for u, v in zip(C, C[1:] + C[:1])) and len(C) > 1:
        st['FAIL.cycle_not_cycle'] += 1
    if over(L, set(C), arcs, st):
        st['FAIL.cycle_heavy_left'] += 1
    return C


def choose_pivot(x, Q, arcs, par, pu, pv, W, st, mode):
    """Pivot Lemma: a mid vertex on the two paths, or a strong component L whose reach is large while nothing strictly below it is high."""
    size = {}

    def f(v):
        if v not in size:
            st['n.reach_tests'] += 1
            size[v] = len(dd.reach(arcs, [v], Q))
        return size[v]
    high = lambda v: 8 * f(v) > 7 * W
    ends = []
    for p in ((pu,) if mode == 'onepath_pivot' else (pu, pv)):
        if not high(p[0]):
            st['FAIL.root_not_high'] += 1
        i = least(1, len(p), lambda i: i < len(p) and high(p[i]))
        c = p[i - 1]
        ends.append(c)
        if i < len(p) and 16 * f(p[i]) >= W and mode != 'nomid':
            return 'mid', p[:i + 1], f
    a, b = ends[0], ends[-1]
    ra = dd.reach(arcs, [a], Q)
    rb = dd.reach(arcs, [b], Q)
    down = b if (b in ra and a not in rb) else a
    if mode == 'wrongsink':
        down = a if (b in ra and a not in rb) else b
    return 'high', down, f


def one_pass(x, Q, W, arcs, kids, st, rng, mode, n, prev):
    """One pass on a bad class. Returns the new classes and the component that was cut."""
    par = dd.out_tree(x, Q, arcs, rng)
    pu, pv = rand_separator(x, Q, arcs, par, st, rng)
    kind, got, f = choose_pivot(x, Q, arcs, par, pu, pv, W, st, mode)
    if kind == 'mid':
        st['n.mid'] += 1
        R, L = got, None
    else:
        st['n.high'] += 1
        L = next(c for c in sccs(arcs, Q) if got in c)
        if prev is not None:
            st['chk.pieces'] += 1
            if len(L) * 4 > 3 * prev[0] or not L <= prev[1]:
                st['FAIL.pieces'] += 1
        st['max.L_over_Q_x100'] = max(st['max.L_over_Q_x100'], 100 * len(L) // len(Q))
        below = dd.reach(arcs, list(L), Q) - L
        if len(below) <= 200 or rng.random() < 0.1:
            st['chk.below'] += 1
            if any(8 * f(v) > 7 * W for v in below):
                st['FAIL.below_high'] += 1
        if mode == 'nocycle':
            C = [got]
        elif mode == 'pathonly':
            far = dd.out_tree(got, L, arcs, rng)
            C = small_path(got, L, arcs) if len(L) < SMALL else dd.root_path(far, max(L, key=lambda v: len(dd.root_path(far, v))))
        else:
            C = cycle_separator(L, arcs, st, rng, mode)
        depth = {x: 0}
        for v in sorted(par, key=lambda v: len(dd.root_path(par, v))):
            depth[v] = depth[par[v]] + 1
        z = min(C, key=depth.get)
        k = C.index(z)
        R = dd.root_path(par, z) + C[k + 1:] + C[:k]
    if len(set(R)) != len(R) or any(v not in arcs.get(u, ()) for u, v in zip(R, R[1:])) or R[0] != x:
        st['FAIL.R_not_path'] += 1
    keyz, via = dd.order_keys(R, arcs, Q - set(R))
    new = dd.split(Q, R, arcs, kids, st, 'shallow' if mode == 'shallow' else 'ok', rng, n, rng.random() < 0.05)
    if ON_PATH:
        ON_PATH(Q, R, new)
    m = R[-1]
    fm = dd.reach(arcs, [m], Q)
    pt = next(c for c in sccs(arcs, Q) if m in c)
    for z, Kz in new:
        st['chk.tail'] += 1
        if via[z] in pt:
            if not Kz <= fm:
                st['FAIL.split_in_point'] += 1
        elif Kz & fm:
            st['FAIL.split_above_point'] += 1
        if 16 * len(Kz) > 15 * W:
            if kind == 'mid':
                st['FAIL.mid_left_bad'] += 1
            elif via[z] not in L or z not in L:
                st['FAIL.bad_outside_L'] += 1
    return new, ((len(L), L - set(C)) if L else None)


def solve(arcs, roots, n, rng, st, mode='ok'):
    kids = {}
    all_ = dd.reach(arcs, roots, set(arcs) | {v for vs in arcs.values() for v in vs} | set(roots))
    keyz = {r: (i, r) for i, r in enumerate(roots)}
    cls = dd.classes_direct(keyz, arcs, all_)
    groups = collections.defaultdict(set)
    for y, z in cls.items():
        groups[z].add(y)
    probs = [(z, groups[z]) for z in groups]
    tops = [r for r in roots if r in groups]
    level = 0
    limit_passes = 2 + math.log(max(n, 2), 4 / 3)
    while probs:
        new = []
        worst = 0
        for x, K in probs:
            if len(K) < SMALL:
                (ON_SMALL or dd.small)(x, K, arcs, kids)
                continue
            W = len(K)
            now, prev, count = [(x, K)], None, 0
            while True:
                bad = [q for q in now if 16 * len(q[1]) > 15 * W]
                if not bad:
                    break
                if len(bad) > 1:
                    st['FAIL.two_bad'] += 1
                z, Q = bad[0]
                now.remove(bad[0])
                got, prev = one_pass(z, Q, W, arcs, kids, st, rng, mode, n, prev)
                now += got
                count += 1
                if count > limit_passes:
                    st['FAIL.passes'] += 1
                    # ponytail: give up on the bound, keep the search correct by plain passes
                    if count > 4 * n:
                        return tops, kids, all_
            worst = max(worst, count)
            new += now
        st['max.passes_per_level'] = max(st['max.passes_per_level'], worst)
        st['n.passes'] += worst
        probs = new
        level += 1
    st['max.levels'] = max(st['max.levels'], level)
    if level > 2 + math.log(max(n / 12, 1.01), 16 / 15):
        st['FAIL.levels'] += 1
    return tops, kids, all_


# ---------------------------------------------------------------- instances with large or nested strong components
def bigrid(a, b, keep, rng):
    arcs = collections.defaultdict(set)
    for i in range(a):
        for j in range(b):
            u = i * b + j
            for v, ok in ((u + 1, j + 1 < b), (u + b, i + 1 < a)):
                if ok:
                    if rng.random() < keep:
                        arcs[u].add(v)
                        arcs[v].add(u)
                    elif rng.random() < .5:
                        arcs[u].add(v)
                    else:
                        arcs[v].add(u)
    return arcs


def flower(p, l):
    """p petals, directed cycles of length l through a common centre, with a spiral rim through the petals."""
    arcs = collections.defaultdict(set)
    nxt, tips = 1, []
    for _ in range(p):
        cyc = [0] + list(range(nxt, nxt + l - 1))
        nxt += l - 1
        for a, b in zip(cyc, cyc[1:] + cyc[:1]):
            arcs[a].add(b)
        tips.append(cyc[(l + 1) // 2])
    for a, b in zip(tips, tips[1:]):
        arcs[a].add(b)
    return arcs


def ladder(k):
    """Two anti-parallel rails with rungs: a bidirected path entered at its end, thickened."""
    arcs = collections.defaultdict(set)
    for i in range(k - 1):
        arcs[2 * i].add(2 * i + 2)
        arcs[2 * i + 3].add(2 * i + 1)
    for i in range(k):
        arcs[2 * i].add(2 * i + 1)
        if i % 2:
            arcs[2 * i + 1].add(2 * i)
    return arcs


def hubs(m, g, rng):
    """A chain of small strong components along a bidirected or one-way strip: each hub has one tail into the strip and a deeper one onward."""
    arcs = collections.defaultdict(set)
    idx = lambda i, j: 2 * m + i * g + j
    for i in range(m):
        p, q = 2 * i, 2 * i + 1
        arcs[p].add(q)
        arcs[q].add(p)
        if i + 1 < m:
            arcs[q].add(2 * i + 2)
        arcs[p].add(idx(i, 0))
        for j in range(g - 1):
            arcs[idx(i, j)].add(idx(i, j + 1))
            if rng.random() < .5:
                arcs[idx(i, j + 1)].add(idx(i, j))
        if i + 1 < m:
            # strip vertices of one hub reach those of the next
            arcs[idx(i, g - 1)].add(idx(i + 1, g - 1))
            if rng.random() < .3:
                arcs[idx(i + 1, g - 1)].add(idx(i, g - 1))
    return arcs


def nested(rng, depth):
    """Cycles inside cycles joined by a few arcs, so strong components break up slowly."""
    arcs = collections.defaultdict(set)
    k, base, rings = 6 + rng.randrange(10), 0, []
    for d in range(depth):
        rng_size = k + d * rng.randrange(1, 4)
        ring = list(range(base, base + rng_size))
        base += rng_size
        turn = rng.random() < .5
        for a, b in zip(ring, ring[1:] + ring[:1]):
            arcs[a if turn else b].add(b if turn else a)
        rings.append(ring)
    for r1, r2 in zip(rings, rings[1:]):
        for i in range(len(r1)):
            if rng.random() < .4:
                u, v = r1[i], r2[i * len(r2) // len(r1)]
                if rng.random() < .5:
                    arcs[u].add(v)
                if rng.random() < .5:
                    arcs[v].add(u)
    return arcs


def instance(rng, big):
    s = 26 if big else 14
    c = rng.randrange(8)
    if c < 2:
        g = dd.digraph(rng, big, 'general')
        return g[0], g[3]
    if c == 2:
        return 'bigrid', bigrid(rng.randrange(3, s), rng.randrange(3, s), rng.choice([1, .9, .7, .5, .3]), rng)
    if c == 3:
        return 'flower', flower(rng.randrange(2, s), rng.randrange(3, s))
    if c == 4:
        return 'ladder', ladder(rng.randrange(6, 3 * s))
    if c == 5:
        return 'hubs', hubs(rng.randrange(2, s), rng.randrange(1, s), rng)
    if c == 6:
        return 'nested', nested(rng, rng.randrange(2, s // 2 + 2))
    name, V, E, arcs = dd.digraph(rng, big, 'order')
    return name, arcs


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
    n = len(V)
    arcs = {u: set(vs) for u, vs in arcs.items()}
    roots = [rng.choice(sorted(V))]
    if rng.random() < .25:
        comps = list(sccs(arcs, V))
        of = {v: i for i, c in enumerate(comps) for v in c}
        entered = {of[v] for u in arcs for v in arcs[u] if of[u] != of[v]}
        roots = [min(c) for i, c in enumerate(comps) if i not in entered]
        rng.shuffle(roots)
        st['n.forests'] += 1
    tops, kids, all_ = solve(arcs, roots, n, rng, st, mode)
    dd.check(tops, kids, all_, arcs, roots, st, False)
    st['runs'] += 1
    st['max.n'] = max(st['max.n'], n)
    st['max.big_scc'] = max(st['max.big_scc'], max(len(c) for c in sccs(arcs, V)))
    st['fam.' + name.split('.')[0]] += 1


def lane(seed, secs, big=False):
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    while time.time() - t0 < secs:
        run_one(rng, st, big)
    return dict(sorted((k, int(v)) for k, v in st.items()))


CTL = ['shallow', 'wrongsink', 'nomid', 'onepath_pivot', 'nocycle', 'pathonly', 'onepath_cycle', 'nolink']


def controls(seed, secs):
    out = {}
    for mode in CTL:
        rng = random.Random(seed)
        st = collections.Counter()
        t0 = time.time()
        while time.time() - t0 < secs:
            run_one(rng, st, True, mode)
        out[mode] = {k: int(v) for k, v in st.items() if k.startswith('FAIL') or k == 'runs'}
    return out


def scale():
    rng = random.Random(1)
    makers = [('bigrid1', lambda m: bigrid(m, m, 1, rng)), ('bigrid.7', lambda m: bigrid(m, m, .7, rng)), ('bigrid.3', lambda m: bigrid(m, m, .3, rng)),
              ('flower', lambda m: flower(m, m)), ('ladder', lambda m: ladder(m * m // 2)), ('hubs', lambda m: hubs(m // 2, m, rng))]
    for name, make in makers:
        for m in (10, 20, 40, 80):
            st = collections.Counter()
            arcs = make(m)
            V = set(arcs) | {v for vs in arcs.values() for v in vs}
            arcs = {u: set(vs) for u, vs in arcs.items()}
            r = min(V)
            U = nx.Graph()
            U.add_edges_from((u, v) for u in arcs for v in arcs[u])
            st['chk.planar'] += 1
            if not nx.check_planarity(U)[0]:
                st['FAIL.not_planar'] += 1
            t0 = time.time()
            tops, kids, all_ = solve(arcs, [r], len(V), rng, st)
            dd.check(tops, kids, all_, arcs, [r], st, False)
            print(json.dumps({'fam': name, 'n': len(V), 'reach': len(all_), 'levels': st['max.levels'], 'passes': st['n.passes'], 'passes_per_level': st['max.passes_per_level'],
                              'mid': st['n.mid'], 'high': st['n.high'], 'scc_tests': st['n.scc_tests'], 'reach_tests': st['n.reach_tests'], 'secs': round(time.time() - t0, 1),
                              'fails': {k: v for k, v in st.items() if k.startswith('FAIL')}}), flush=True)


if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == 'ctl':
        print(json.dumps(controls(int(a[1]), float(a[2]))))
    elif a[0] == 'scale':
        scale()
    else:
        print(json.dumps(lane(int(a[0]), float(a[1]), len(a) > 2)))
