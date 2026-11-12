"""python3 -I wsmall.py <seed> <seconds> [big]: weighted matching with reachability only.
Edge weights in 0..W by dual steps on the tight digraph, vertex weights by one reach set per insertion.
No distance is computed anywhere. Mode ctl: negative controls, each of which must fail somewhere."""
import collections, heapq, json, os, random, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode = True
sys.setrecursionlimit(100000)
import mm, fam

import networkx as nx


def key(u, v):
    return min(u, v), max(u, v)


def tight_arcs(cur, E, side, s, wt, match, y, wrong):
    """The tight residual digraph, read from side s. Matched edges are tight by (D2)."""
    arcs = collections.defaultdict(list)
    for u, v in E:
        if u in cur and v in cur:
            a, b = (u, v) if side[u] == s else (v, u)
            if match.get(a) == b:
                if wrong != 'nomatched':
                    arcs[b].append(a)
            elif y[a] + y[b] == wt[key(a, b)] or wrong == 'anyarc':
                arcs[a].append(b)
    for x in arcs:
        arcs[x].sort()
    return arcs


def check_state(cur, E, side, H, wt, match, y, W, st):
    """(I1), (I2), y in 0..W, and (I3): a free vertex with y > 0 is a root."""
    for u, v in E:
        if u in cur and v in cur:
            st['chk.feasible'] += 1
            if y[u] + y[v] < wt[key(u, v)]:
                st['FAIL.feasible'] += 1
            if match.get(u) == v:
                st['chk.tight'] += 1
                if y[u] + y[v] != wt[key(u, v)]:
                    st['FAIL.tight'] += 1
    for v in cur:
        st['chk.range'] += 1
        if not 0 <= y[v] <= W:
            st['FAIL.range'] += 1
        st['chk.I3'] += 1
        if v not in match and y[v] > 0 and v not in H:
            st['FAIL.I3'] += 1


def unmatch_end(match, side, s, z):
    if side[z] == s:
        del match[z]


def path_ok(p, arcs, st):
    st['chk.simple'] += 1
    if len(set(p)) != len(p):
        st['FAIL.simple'] += 1
    st['chk.arcs'] += 1
    if any(p[i + 1] not in arcs.get(p[i], ()) for i in range(len(p) - 1)):
        st['FAIL.arcs'] += 1


def batch(iroot, V, E, side, s, cur, H, wt, W, match, y, rng, st, wrong, longstep):
    """Insert all of H, on side s, at once. Returns the numbers of flips and of dual steps."""
    flips = steps = 0
    while True:
        roots = sorted(h for h in H if h not in match and y[h] > 0)
        if wrong == 'stoponeearly':
            roots = [h for h in roots if y[h] > 1]
        if not roots:
            return flips, steps
        st['chk.equal_theta'] += 1
        if len({y[h] for h in roots}) > 1:
            st['FAIL.equal_theta'] += 1
        arcs = tight_arcs(cur, E, side, s, wt, match, y, wrong)
        S = mm.multi_source_labels(iroot, V, arcs, roots, st)
        S &= cur
        st['reach_sets'] += 1
        st['chk.reach'] += 1
        if S != reach(arcs, roots):
            st['FAIL.reach'] += 1
        ends = [x for x in S if (side[x] != s and x not in match) or (side[x] == s and x in match and y[x] == 0)]
        if wrong == 'noswap':
            ends = [x for x in ends if side[x] != s]
        if wrong == 'nofreeb':
            ends = [x for x in ends if side[x] == s]
        if ends:
            z = rng.choice(sorted(ends))
            r = next(r for r in rng.sample(roots, len(roots)) if z in reach(arcs, [r]))
            p = mm.path_lemma(iroot, arcs, r, z, st)
            path_ok(p, arcs, st)
            unmatch_end(match, side, s, z)
            mm.flip(match, p)
            flips += 1
        else:
            d = 1
            if longstep:
                d = min(y[a] for a in S if side[a] == s)
                for u, v in E:
                    if u in cur and v in cur:
                        a, b = (u, v) if side[u] == s else (v, u)
                        if a in S and b not in S:
                            d = min(d, y[a] + y[b] - wt[key(a, b)])
            if wrong == 'overstep':
                d += 1
            st['chk.step_positive'] += 1
            if d <= 0:
                st['FAIL.step_positive'] += 1
                d = 1
            for x in S:
                if side[x] == s:
                    y[x] -= d
                elif wrong != 'oneside':
                    y[x] += d
            steps += 1
        check_state(cur, E, side, H, wt, match, y, W, st)


def reach(arcs, rs):
    seen, stk = set(rs), list(rs)
    while stk:
        for w in arcs.get(stk.pop(), ()):
            if w not in seen:
                seen.add(w)
                stk.append(w)
    return seen


def small_weight(V, E, side, wt, W, rng, st, leaf=6, closure=False, inner=False, wrong=None, longstep=False):
    root, _ = mm.build(V, E, rng, leaf=leaf, closure=closure)
    match, y = {}, {v: 0 for v in V}
    for level in mm.outer_order(root):
        for X in level:
            C = mm.own_set(X)
            hubs = C & X.sep
            cur = C - hubs
            iroot = mm.build(X.V, X.E, rng, leaf=leaf, closure=inner)[0]
            phases = 0
            for s in rng.sample((0, 1), 2):
                H = {h for h in hubs if side[h] == s}
                if not H:
                    continue
                cur |= H
                for h in H:
                    y[h] = W
                f, d = batch(iroot, V, E, side, s, cur, H, wt, W, match, y, rng, st, wrong, longstep)
                st['chk.flips_bound'] += 1
                if f > len(H):
                    st['FAIL.flips_bound'] += 1
                st['chk.steps_bound'] += 1
                if d > W:
                    st['FAIL.steps_bound'] += 1
                phases += f + d
                tag = 'max_dual_steps_in_batch' + ('_long' if longstep else '')
                st[tag] = max(st[tag], d)
            st['max_phases_in_bag' + ('_long' if longstep else '')] = max(st['max_phases_in_bag' + ('_long' if longstep else '')], phases)
            st['max_hubs_in_bag'] = max(st['max_hubs_in_bag'], len(hubs))
    return match, y


def vertex_weight(V, E, side, pi, rng, st, leaf=6, closure=False, inner=False, wrong=None):
    root, _ = mm.build(V, E, rng, leaf=leaf, closure=closure)
    match = {}
    for level in mm.outer_order(root):
        for X in level:
            C = mm.own_set(X)
            hubs = sorted(C & X.sep)
            cur = C - set(hubs)
            iroot = mm.build(X.V, X.E, rng, leaf=leaf, closure=inner)[0]
            for h in hubs:
                cur.add(h)
                arcs = mm.residual(cur, E, side, match, h)
                S = mm.multi_source_labels(iroot, V, arcs, [h], st) & cur
                st['reach_sets'] += 1
                st['chk.reach'] += 1
                if S != reach(arcs, [h]):
                    st['FAIL.reach'] += 1
                gains = {}
                for x in S - {h}:
                    if side[x] != side[h] and x not in match:
                        gains[x] = pi[h] + pi[x]
                    elif side[x] == side[h]:
                        gains[x] = pi[h] - pi[x]
                if wrong == 'noswap':
                    gains = {x: g for x, g in gains.items() if side[x] != side[h]}
                if wrong == 'nofree':
                    gains = {x: g for x, g in gains.items() if side[x] == side[h]}
                if wrong == 'anyfree' and any(side[x] != side[h] for x in gains):
                    z = min(x for x in gains if side[x] != side[h])
                    gains = {z: gains[z]}
                if wrong == 'worst' and gains:
                    z = min(gains, key=lambda x: (gains[x], x))
                    gains = {z: gains[z]}
                if not gains:
                    continue
                z = max(gains, key=lambda x: (gains[x], -x))
                if gains[z] <= 0 and wrong != 'always':
                    continue
                p = mm.path_lemma(iroot, arcs, h, z, st)
                path_ok(p, arcs, st)
                unmatch_end(match, side, side[h], z)
                mm.flip(match, p)
                st['flips'] += 1
    return match


def check_result(m, val, V, E, side, wt, st, tag):
    st['chk.matching'] += 1
    if not mm.is_matching(m, E):
        st['FAIL.matching'] += 1
    st['chk.opt.' + tag] += 1
    if val != mm.opt_weight_exact(V, E, side, wt):
        st['FAIL.opt.' + tag] += 1
    if len(E) <= 18:
        st['chk.brute.' + tag] += 1
        if val != mm.brute_weight(V, E, wt):
            st['FAIL.brute.' + tag] += 1


def one_run(rng, st, big, wrong_s=None, wrong_v=None):
    name, (V, E) = fam.sample(rng, big)
    side = fam.two_colour(V, E)
    assert side is not None
    g = nx.Graph()
    g.add_nodes_from(V)
    g.add_edges_from(E)
    st['chk.planar'] += 1
    if not nx.check_planarity(g)[0]:
        st['FAIL.planar'] += 1
    leaf = rng.choice([3, 4, 6, 10])
    closure = rng.choice([False, True, 'two'])
    inner = rng.choice([False, True, 'two'])
    st['runs'] += 1
    st['runs|' + name] += 1
    if wrong_v is None:
        W = rng.choice([1, 2, 3, 5, 10, 30, 1000, 10 ** 6])
        how = rng.choice(['uniform', 'ends', 'zeros'])
        if how == 'uniform':
            wt = {key(u, v): rng.randrange(0, W + 1) for u, v in E}
        elif how == 'ends':
            wt = {key(u, v): rng.choice([0, W]) for u, v in E}
        else:
            wt = {key(u, v): rng.choice([0, 0, 0, rng.randrange(0, W + 1)]) for u, v in E}
        longstep = W > 30 or rng.random() < 0.5
        m, y = small_weight(V, E, side, wt, W, rng, st, leaf, closure, inner, wrong_s, longstep)
        val = mm.weight_of(m, wt)
        check_result(m, val, V, E, side, wt, st, 'edge')
        st['chk.duality'] += 1
        if sum(y.values()) != val:
            st['FAIL.duality'] += 1
        mm.check_duals(set(V), E, side, wt, m, y, st)
    if wrong_s is None:
        top = rng.choice([1, 3, 10, 10 ** 6])
        pi = {v: rng.randrange(0, top + 1) for v in V}
        if rng.random() < 0.3:
            pi = {v: (pi[v] if side[v] == 0 else 0) for v in V}
        wt = {key(u, v): pi[u] + pi[v] for u, v in E}
        m = vertex_weight(V, E, side, pi, rng, st, leaf, closure, inner, wrong_v)
        check_result(m, mm.weight_of(m, wt), V, E, side, wt, st, 'vertex')


def lane(seed, secs, big):
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    while time.time() - t0 < secs:
        one_run(rng, st, big)
    return st


def controls(seed, secs):
    """Each control runs until a failure or the time is up; it must report some FAIL line."""
    res = {}
    cases = [('edge', w) for w in ['anyarc', 'nomatched', 'noswap', 'nofreeb', 'oneside', 'overstep', 'stoponeearly']]
    cases += [('vertex', w) for w in ['noswap', 'nofree', 'anyfree', 'worst', 'always']]
    for kind, w in cases:
        rng = random.Random(seed)
        st = collections.Counter()
        t0 = time.time()
        crashes = 0
        while time.time() - t0 < secs:
            try:
                if kind == 'edge':
                    one_run(rng, st, False, wrong_s=w)
                else:
                    one_run(rng, st, False, wrong_v=w)
            except (AssertionError, KeyError, StopIteration, ValueError):
                crashes += 1
        res[kind + ':' + w] = {'runs': st['runs'], 'crashes': crashes,
                               'fails': {k: v for k, v in st.items() if k.startswith('FAIL')}}
    return res


def spider(m):
    """A tree of diameter 4 with W = m + 1 on which the search takes W dual steps, also with long steps."""
    h, V, E, side, wt, match, y = 0, [0], [], {0: 0}, {}, {}, {0: m + 1}
    for i in range(1, m + 1):
        bi, ai = 2 * i - 1, 2 * i
        V += [bi, ai]
        E += [(h, bi), (bi, ai)]
        side[bi], side[ai] = 1, 0
        wt[key(h, bi)], wt[key(bi, ai)] = i, m + 1
        match[bi], match[ai] = ai, bi
        y[bi], y[ai] = 0, m + 1
    st = collections.Counter()
    rng = random.Random(1)
    iroot = mm.build(V, E, rng, leaf=4)[0]
    f, d = batch(iroot, V, E, side, 0, set(V), {h}, wt, m + 1, match, y, rng, st, None, True)
    assert (f, d) == (0, m + 1) and sum(y.values()) == mm.opt_weight_exact(V, E, side, wt) == m * (m + 1)
    assert not [k for k in st if k.startswith('FAIL')]
    return d


def chords(k, lam):
    """Path a0 b1 a1 ... b_k with chords a_{t-1} b_{t+1} of reduced length lam[t], and a free vertex b' with
    an edge of slack 1 to a_{k-1}. Returns the distances between path vertices before the flip of the path,
    and d(h', b') after it, with h' a new vertex with a tight edge to b1. All weights are in 0..L."""
    a = lambda i: 2 * i
    b = lambda i: 2 * i - 1
    path = [a(0)]
    for i in range(1, k):
        path += [b(i), a(i)]
    path.append(b(k))
    hh, bb = 2 * k, 2 * k + 1
    L = sum(lam.values()) + 2
    side = {v: v % 2 for v in path + [hh, bb]}
    y = {v: (0 if side[v] else L) for v in side}
    wt = {key(u, v): L for u, v in zip(path, path[1:])}
    for t in range(1, k):
        wt[key(a(t - 1), b(t + 1))] = L - lam[t]
    wt[key(a(k - 1), bb)] = L - 1
    wt[key(hh, b(1))] = L
    E = list(wt)
    assert nx.check_planarity(nx.Graph(E))[0] and all(side[u] != side[v] and w >= 0 for (u, v), w in wt.items())
    match = {}
    for i in range(1, k):
        match[b(i)], match[a(i)] = a(i), b(i)

    def dist(src, C):
        arcs = mm.residual(C, E, side, match, a(0))
        d, pq = {src: 0}, [(0, src)]
        while pq:
            x, v = heapq.heappop(pq)
            if x == d[v]:
                for w in arcs.get(v, ()):
                    n = x + y[v] + y[w] - wt[key(v, w)]
                    if n < d.get(w, n + 1):
                        d[w] = n
                        heapq.heappush(pq, (n, w))
        return d

    C = set(path) | {bb}
    before = {v: {w: x for w, x in dist(v, C).items() if w != bb} for v in path}
    mm.flip(match, path)
    return before, dist(hh, C | {hh}).get(bb)


def limits():
    for m in (1, 2, 5, 20):
        assert spider(m) == m + 1
    k = 12
    one, two = {t: 1 for t in range(1, k)}, {t: 2 + t for t in range(1, k)}
    b1, d1 = chords(k, one)
    b2, d2 = chords(k, two)
    assert b1 == b2 and d1 == sum(one.values()) + 1 and d2 == sum(two.values()) + 1 and d1 != d2
    return {'spider steps at m = 20': spider(20), 'distances before the flip equal': b1 == b2, 'after the flip': [d1, d2]}


if __name__ == '__main__':
    if sys.argv[1] == 'limits':
        print(json.dumps(limits()))
    elif sys.argv[1] == 'ctl':
        print(json.dumps(controls(int(sys.argv[2]), float(sys.argv[3])), indent=0))
    else:
        st = lane(int(sys.argv[1]), float(sys.argv[2]), len(sys.argv) > 3)
        print(json.dumps(dict(sorted(st.items())), indent=0))
