"""Two more uses of who.py.
python3 -I -B who2.py gdfs SEED SECS   : who.py path step, local states and explicit parts, on the real paths of the General Search (repo gdfs.py as a path source only)
python3 -I -B who2.py scale            : applications of (P) and runs of the Multi-Source Lemma per pass against the path length
python3 -I -B who2.py lit              : the Section 4 text read literally on the 22-vertex instance, through the General Search
"""
import collections, json, math, os, random, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..'))
import networkx as nx
import who
import gdfs, dagdfs as dd


def on_gdfs(arcs, r, st, rng, literal=False):
    V = set(arcs) | {v for vs in arcs.values() for v in vs}
    U = nx.Graph()
    U.add_nodes_from(V)
    U.add_edges_from((u, v) for u in arcs for v in arcs[u])
    if not nx.is_connected(U):
        comps = [sorted(c, key=str)[0] for c in nx.connected_components(U)]
        for x, y in zip(comps, comps[1:]):
            U.add_edge(x, y)
    sim = who.Sim(U, arcs, st)
    sim.ent = {r: True}
    Q0 = who.direct(arcs, [r], V)

    def on_path(Q, R, new):
        sim.passP = 0
        out = who.path_step_all(sim, {0: (Q, R)})
        st['max.P_per_pass'] = max(st['max.P_per_pass'], sim.passP)
        st['passes'] += 1
        for y, d in out.items():
            if d:
                sim.rec[y] = R[d - 1]
        # entries by own rule, classes from local e(y)
        S = sim.S
        cl = {y: S[y]['eb'] for y in Q - set(R)}
        own = {y: z for z, K in new for y in K}
        # the classes of the local keys equal those of the Split Lemma in the repo, up to names
        grp = collections.defaultdict(set)
        for y, e in cl.items():
            grp[e].add(y)
        rep = {frozenset(K) for z, K in new}
        if {frozenset(K) for K in grp.values()} != rep:
            st['FAIL.classes_differ'] += 1
        src = (V if literal else Q)
        for u in src:
            for v in arcs.get(u, ()):
                if v in own and own.get(u) != own[v]:
                    sim.ent[v] = True

    def on_small(x, K, arcs_, kids):
        dd.small(x, K, arcs_, kids)
        E = {v for v in K if sim.ent.get(v)}
        for y in K:
            d = who.truth_small(K, E, arcs, y)
            if d is not None:
                sim.rec[y] = d
    gdfs.ON_PATH, gdfs.ON_SMALL = on_path, on_small
    try:
        gdfs.solve(arcs, [r], len(V), rng, st, 'ok')
    finally:
        gdfs.ON_PATH = gdfs.ON_SMALL = None
    return sim.rec


def lane(seed, secs):
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    while time.time() - t0 < secs:
        q = rng.random()
        if q < .15:
            arcs = who.rings2(rng.randrange(3, 10), rng)
        elif q < .3:
            arcs = who.wheel_hub(rng.randrange(8, 70), rng)
        elif q < .45:
            arcs = who.rings(rng.randrange(5, 30), rng)
        else:
            _, arcs = gdfs.instance(rng, False)
        arcs = {u: set(vs) for u, vs in arcs.items()}
        V = set(arcs) | {v for vs in arcs.values() for v in vs}
        if len(V) < 2:
            continue
        U = nx.Graph()
        U.add_nodes_from(V)
        U.add_edges_from((u, v) for u in arcs for v in arcs[u])
        st['chk.planar'] += 1
        if not nx.check_planarity(U)[0]:
            st['FAIL.not_planar'] += 1
            continue
        r = rng.choice(sorted(V))
        rec = on_gdfs(arcs, r, st, rng)
        true = who.truth(arcs, r, V)
        st['runs'] += 1
        st['n.vertices'] += len(true)
        st['n.nontrivial'] += sum(1 for y in true if true[y] != r)
        st['max.n'] = max(st['max.n'], len(V))
        if rec != true:
            st['FAIL.tree'] += 1
    print(json.dumps({k: int(v) for k, v in sorted(st.items()) if not k.startswith('chk.b') and not k.startswith('chk.c') and not k.startswith('n.') or k in ('n.vertices', 'n.nontrivial')}))


def scale():
    rng = random.Random(3)
    for p in (6, 8, 10, 12):
        k = 2 ** p
        # a path with the ring structure and an off-path hub: k positions
        arcs = collections.defaultdict(set)
        for i in range(k - 1):
            arcs[i].add(i + 1)
        a, top, mid, nxt = 0, k - 1, k // 2, k
        while a < mid - 1 and top > mid + 6:
            T = top - rng.randrange(0, 2)
            t = T - rng.randrange(0, 2)
            arcs[a].add(T)
            if T - t >= 1:
                arcs[T].add(t)
            top = t - 1
            a += rng.randrange(1, 3)
        V = set(arcs) | {v for vs in arcs.values() for v in vs}
        U = nx.Graph()
        U.add_nodes_from(V)
        U.add_edges_from((u, v) for u in arcs for v in arcs[u])
        planar = nx.check_planarity(U)[0]
        st = collections.Counter()
        sim = who.Sim(U, arcs, st)
        sim.ent = {0: True}
        sim.passP = 0
        Q = who.direct(arcs, [0], V)
        t0 = time.time()
        out = who.path_step_all(sim, {0: (Q, list(range(k)))})
        print(json.dumps({'k': k, 'n': len(V), 'planar': planar, 'P': st['P'], 'P/log2^2': round(st['P'] / p ** 2, 2), 'MS': st['MS'], 'exchanges': st['rounds_ex'], 'ring_sends': st['ring_sends'], 'route_cross': st['route_cross'], 'fails': {x: v for x, v in st.items() if x.startswith('FAIL')}, 'secs': round(time.time() - t0, 1)}), flush=True)


def lit():
    arcs = {0: set()}
    nxt = 1
    for i in range(7):
        w, y, x = nxt, nxt + 1, nxt + 2
        nxt += 3
        arcs[0].add(w)
        arcs[w] = {y}
        arcs[x] = {y}
    st = collections.Counter()
    rng = random.Random(1)
    V = set(arcs) | {v for vs in arcs.values() for v in vs}
    true = who.truth(arcs, 0, who.direct(arcs, [0], V))
    for literal in (False, True):
        rec = on_gdfs(arcs, 0, st, rng, literal)
        print('literal' if literal else 'reached only', 'wrong at', {y: (rec.get(y), true[y]) for y in true if rec.get(y) != true[y]}, {k: v for k, v in st.items() if k.startswith('FAIL')})


if __name__ == '__main__':
    if sys.argv[1] == 'gdfs':
        lane(int(sys.argv[2]), float(sys.argv[3]))
    elif sys.argv[1] == 'scale':
        scale()
    else:
        lit()
