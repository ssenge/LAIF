"""python3 -I run.py <seed> <seconds> [big]: random lane; prints counters as JSON.
Mode ctl: negative controls, each of which must fail somewhere."""
import collections, json, os, random, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode = True
sys.setrecursionlimit(100000)
import mm, fam

try:
    import networkx as nx
except ImportError:
    nx = None


def planar(V, E):
    if nx is None:
        return True
    g = nx.Graph()
    g.add_nodes_from(V)
    g.add_edges_from(E)
    return nx.check_planarity(g)[0]


def lane(seed, secs, big):
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    while time.time() - t0 < secs:
        name, (V, E) = fam.sample(rng, big)
        side = fam.two_colour(V, E)
        assert side is not None
        if nx is not None:
            st['chk.planar'] += 1
            if not planar(V, E):
                st['FAIL.planar'] += 1
        leaf = rng.choice([3, 4, 6, 10])
        closure = rng.choice([False, True, 'two'])
        inner = rng.choice([False, True, 'two'])
        m = mm.max_matching(len(V), V, E, side, rng, st, leaf=leaf, closure=closure, inner_closure=inner)
        opt = mm.hopcroft_karp(V, E, side)
        st['runs'] += 1
        st['runs|' + name] += 1
        st['chk.matching'] += 1
        if not mm.is_matching(m, E):
            st['FAIL.matching'] += 1
        st['chk.max'] += 1
        if len(m) // 2 != opt:
            st['FAIL.max'] += 1
        arcs, Z = mm.konig_check(V, E, side, m, st)
        froot, _ = mm.build(V, E, rng, leaf=leaf, closure=closure)
        free = sorted(v for v in V if side[v] == 0 and v not in m)
        st['chk.multi_source'] += 1
        if mm.multi_source_labels(froot, V, arcs, free, st) != Z:
            st['FAIL.multi_source'] += 1
        # weighted
        W = rng.choice([1, 3, 10, 1000])
        wt = {(min(u, v), max(u, v)): rng.randrange(0 if W > 1 else 1, W + 1) for u, v in E}
        mw, y = mm.max_weight(V, E, side, wt, rng, st, leaf=leaf, closure=closure, inner_closure=inner)
        val = mm.weight_of(mw, wt)
        o2 = mm.opt_weight_exact(V, E, side, wt)
        st['chk.weighted_matching'] += 1
        if not mm.is_matching(mw, E):
            st['FAIL.weighted_matching'] += 1
        st['chk.weight_opt'] += 1
        if val != o2:
            st['FAIL.weight_opt'] += 1
        st['chk.weak_duality'] += 1
        if sum(y.values()) != val:
            st['FAIL.weak_duality'] += 1
        if len(E) <= 18:
            st['chk.brute'] += 1
            if mm.brute_weight(V, E, wt) != val:
                st['FAIL.brute'] += 1
    return st


def far_pair(V, arcs, rng):
    """A reachable pair with a long shortest path."""
    best = None
    for s in rng.sample(sorted(V), min(6, len(V))):
        d = {s: 0}
        q = collections.deque([s])
        while q:
            x = q.popleft()
            for y in arcs.get(x, ()):
                if y not in d:
                    d[y] = d[x] + 1
                    q.append(y)
        t = max(d, key=d.get)
        if t != s and (best is None or d[t] > best[0]):
            best = (d[t], s, t)
    return best and best[1:]


def reach_all(arcs, s):
    seen, stk = {s}, [s]
    while stk:
        for y in arcs.get(stk.pop(), ()):
            if y not in seen:
                seen.add(y)
                stk.append(y)
    return seen


def path_instance(rng, big):
    k = rng.randrange(8)
    m = 16 if big else 9
    if k >= 6:
        V, E, arcs = fam.manhattan(rng.randrange(2, m), rng.randrange(2, m), rng)
        pr = far_pair(V, arcs, rng)
        return pr and ('manhattan', V, E, arcs, pr[0], pr[1])
    if k == 5:
        V, E, arcs, s, t = fam.griddag(rng.randrange(2, m), rng.randrange(2, m), rng)
        return 'griddag', V, E, arcs, s, t
    if k == 0:
        V, E, arcs, s, t = fam.snake(rng.randrange(2, m), rng.randrange(2, m), rng)
        return 'snake', V, E, arcs, s, t
    if k == 1:
        n = rng.randrange(3, m)
        V, E, arcs, s, t = fam.spiral(n, rng)
        return 'spiral', V, E, arcs, s, t
    name, (V, E) = fam.sample(rng, big)
    how = 'dag' if k == 2 else 'rand'
    arcs = fam.orient(V, E, rng, how)
    pr = far_pair(V, arcs, rng)
    if pr is None:
        return None
    return how + '|' + name, V, E, arcs, pr[0], pr[1]


def path_lane(seed, secs, big, **kw):
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    while time.time() - t0 < secs:
        inst = path_instance(rng, big)
        if inst is None:
            continue
        name, V, E, arcs, s, t = inst
        if s not in reach_all(arcs, s) or t not in reach_all(arcs, s):
            continue
        if nx is not None:
            st['chk.planar'] += 1
            if not planar(V, E):
                st['FAIL.planar'] += 1
        root, _ = mm.build(V, E, rng, leaf=rng.choice([2, 3, 4, 6]), closure=rng.choice([False, True, 'two']))
        st['runs'] += 1
        st['runs|' + name.split('|')[0]] += 1
        try:
            p = mm.path_lemma(root, arcs, s, t, st, ties=rng if rng.random() < 0.7 else None, **kw)
        except AssertionError:
            st['abort'] += 1
            continue
        st['max_path'] = max(st['max_path'], len(p))
        st['chk.ends'] += 1
        if p[0] != s or p[-1] != t:
            st['FAIL.ends'] += 1
        st['chk.simple'] += 1
        if len(set(p)) != len(p):
            st['FAIL.simple'] += 1
        st['chk.arcs'] += 1
        if any(p[i + 1] not in arcs.get(p[i], ()) for i in range(len(p) - 1)):
            st['FAIL.arcs'] += 1
    return st


def controls(seed, secs):
    """Each deliberately wrong variant has to be caught."""
    out = {}
    for name in ['no_minhop', 'no_erase', 'no_both', 'skip_hub', 'hung_nomin', 'hung_stopfree']:
        rng = random.Random(seed)
        st = collections.Counter()
        t0 = time.time()
        while time.time() - t0 < secs:
            nm, (V, E) = fam.sample(rng, rng.random() < 0.5)
            side = fam.two_colour(V, E)
            st['runs'] += 1
            try:
                if name in ('no_minhop', 'no_erase', 'no_both', 'skip_hub'):
                    kw = dict(leaf=3, closure=rng.choice([False, 'two']), inner_closure=rng.choice([False, 'two']))
                    if name in ('no_minhop', 'no_both'):
                        kw['minhop'] = False
                    if name in ('no_erase', 'no_both'):
                        kw['erase'] = False
                    if name == 'skip_hub':
                        kw['skip_hub'] = lambda h: h % 7 == 3
                    m = mm.max_matching(len(V), V, E, side, rng, st, **kw)
                    if len(m) // 2 != mm.hopcroft_karp(V, E, side):
                        st['FAIL.max'] += 1
                else:
                    wt = {(min(u, v), max(u, v)): rng.randrange(0, 11) for u, v in E}
                    mw, y = mm.max_weight(V, E, side, wt, rng, st, leaf=3, wrong=name.split('_')[1].replace('stopfree', 'stop_at_free'))
                    if mm.weight_of(mw, wt) != mm.opt_weight_exact(V, E, side, wt):
                        st['FAIL.weight_opt'] += 1
            except (AssertionError, KeyError) as e:
                st['abort'] += 1
        out[name] = {k: v for k, v in st.items() if k.startswith('FAIL') or k in ('runs', 'abort')}
    for name, kw in [('path_no_minhop', dict(minhop=False)), ('path_no_erase', dict(erase=False))]:
        st = path_lane(seed, secs, False, budget=4000, **kw)
        out[name] = {k: v for k, v in st.items() if k.startswith('FAIL') or k in ('runs', 'abort')}
    return out


if __name__ == '__main__':
    if sys.argv[1] == 'ctl':
        print(json.dumps(controls(int(sys.argv[2]), float(sys.argv[3])), indent=0))
    elif sys.argv[1] == 'path':
        st = path_lane(int(sys.argv[2]), float(sys.argv[3]), len(sys.argv) > 4)
        print(json.dumps(dict(st), sort_keys=True))
    else:
        st = lane(int(sys.argv[1]), float(sys.argv[2]), len(sys.argv) > 3)
        print(json.dumps(dict(st), sort_keys=True))
