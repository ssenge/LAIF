"""Deterministic exact maximum flow from disk labels with a prescribed first cut, end to end.

For a flow instance this builds the network N of notes/MAXFLOW.md, Section 4, with its slit
cycle S, and the disk hierarchy of disks.py on N with S as the first cut. In every pass of the
scaling the portal table comes from the root of this hierarchy: the least walks between the
vertices of S through the port metrics of the children of the root, with free moves at a vertex.
Then the table is perturbed within [d, (1+eps) d], as a stand-in for the error of the labels,
turned into bounds by Lemma N(6), and passed to the Step Lemma of mf.py. The result is compared
with an independent maximum flow, and the flow is checked on every edge.
Run: python -I pipeline.py <seed> <seconds> [big]
"""
import collections, math, os, random, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'maxflow'))
sys.path.insert(0, HERE)
import networkx as nx
import disks
import forced
import mf


def n_network(I):
    groups, arcs = forced.build_N(I, 1)
    q = forced.slit_cycle(I, groups)
    data = forced.embedding_N(I, groups, arcs)
    E = nx.PlanarEmbedding()
    E.set_data(data)
    E.check_structure()
    return groups, arcs, q, E


def lengths_of(I, arcs, idx, C, nN):
    """Scaled lengths L = 2|V(N)| K l_C + 1 on the arcs of N, lightest of parallel arcs."""
    Mbig = nN * (max(C.values()) + 1) + 1
    lens = {}
    for pair, lst in arcs.items():
        best = {}
        for u, v, k, luv, lvu in lst:
            if k == 'R':
                a, b = 0, 0
            elif k == 'S':
                a, b = Mbig, Mbig
            else:
                a, b = C[luv], C[lvu]
            for x, y, z in ((u, v, a), (v, u, b)):
                if (x, y) not in best or best[x, y] > z:
                    best[x, y] = z
        for (x, y), z in best.items():
            lens[idx[x], idx[y]] = 2 * nN * mf.K * z + 1
    return lens


def build_levels(M, Md, t, C0, rng):
    levels = [{2 * next(d for d in range(M.D) if M.vert[d] == t.root) + 1}]
    C = C0
    while True:
        G0 = levels[-1]
        disks.is_level(t, Md, G0)
        comp, cnt, mk = disks.npof(t, Md, G0)
        if not mk:
            return levels
        if len(levels) > 1:
            C = disks.choose_cut(t, Md, G0, rng)
        levels.append(disks.nxt(t, Md, G0, C))


def root_table(M, Md, levels, verts):
    """Least walks between the vertices `verts` through the exact port metrics of the children of the root."""
    sp = disks.split(Md, levels[1])
    vc = disks.cycles(sp.rot, Md.D)
    adj = {}
    for z in range(Md.D):
        adj.setdefault(vc[z], []).append((vc[sp.rev(z)], Md.length(z)))
    corners = sorted(levels[1])
    lam = {p: dijk(adj, vc[p]) for p in corners}
    cadj = {p: [] for p in corners}
    for p in corners:
        for q in corners:
            if p != q and vc[q] in lam[p]:
                cadj[p].append((q, lam[p][vc[q]]))
            if p != q and Md.vert(p) == Md.vert(q):
                cadj[p].append((q, 0))
    tab = {}
    for x in verts:
        px = next(p for p in corners if Md.vert(p) == x)
        dc = dijk(cadj, px)
        for y in verts:
            tab[x, y] = min(dc.get(q, math.inf) for q in corners if Md.vert(q) == y)
    return tab


def dijk(adj, s):
    import heapq
    dist, pq = {s: 0}, [(0, s)]
    while pq:
        d, v = heapq.heappop(pq)
        if d > dist[v]:
            continue
        for w, l in adj.get(v, []):
            if d + l < dist.get(w, math.inf):
                dist[w] = d + l
                heapq.heappush(pq, (d + l, w))
    return dist


def case(rng, st, big):
    I = forced.flow_instance(rng, big)
    if not I.R:
        return
    groups, arcs, q, E = n_network(I)
    nodes = sorted(E.nodes(), key=str)
    idx = {x: i for i, x in enumerate(nodes)}
    nN = len(nodes)
    G = nx.Graph()
    G.add_nodes_from(range(nN))
    for pair in arcs:
        a, b = tuple(pair)
        G.add_edge(idx[a], idx[b])
    emb = nx.PlanarEmbedding()
    emb.set_data({idx[v]: [idx[w] for w in E.neighbors_cw_order(v)] for v in nodes})
    qi = [idx[x] for x in q]
    # orient q as a face walk of emb
    if set(emb.traverse_face(qi[0], qi[1])) != set(qi):
        qi = qi[::-1]
    walk = emb.traverse_face(qi[0], qi[1])
    assert set(walk) == set(qi) and len(walk) == len(qi), 'slit cycle is not a face'
    lens0 = lengths_of(I, arcs, idx, I.cap, nN)
    M = disks.Map(G, emb, lens0).finish()
    face_darts = [M.idx[(walk[j], walk[(j + 1) % len(walk)])] for j in range(len(walk))]
    _, Md, t, path = disks.build(G, emb, lens0, face_darts, rng)
    Md = disks.Doubled(M)
    t = disks.Tree(M, t.parent, t.root)
    da, db = face_darts[-1], face_darts[0]
    levels = build_levels(M, Md, t, {2 * da + 1, 2 * db + 1}, rng)
    st['maxH'] = max(st['maxH'], len(levels) - 1)
    # one corner node per portal face
    corner_of = {}
    for x in q:
        if x[0] == 'c':
            corner_of.setdefault(I.rgt[x[1]], idx[x])
    assert set(I.portals) <= set(corner_of)

    def bounds(I_, C, rng_, mode, st_, wrong=None):
        M.len = [0] * M.D
        L = lengths_of(I, arcs, idx, C, nN)
        for d in range(M.D):
            M.len[d] = L[M.vert[d], M.head[d]]
        verts = sorted(set(corner_of[p] for p in I.portals))
        tab = root_table(M, Md, levels, verts)
        adjC = mf.gamma_adj(I, lambda d: C[d])
        b = {}
        for u in I.portals:
            dc = mf.dijkstra(I.nf, adjC, {u: 0})
            for v in I.portals:
                dl = tab[corner_of[u], corner_of[v]]
                # Lemma N(5): the distance in N between corners is the distance in Gamma, scaled
                st_['chk.N5'] += 1
                if not (2 * nN * mf.K * dc[v] <= dl < 2 * nN * mf.K * dc[v] + nN):
                    st_['FAIL.N5'] += 1
                dt = mf.noise(rng_, dl, mode)
                b[u, v] = dt * mf.EPS_DEN // ((mf.EPS_DEN + mf.EPS_NUM) * 2 * nN)
                st_['chk.B'] += 1
                if b[u, v] > mf.K * dc[v] or b[u, v] * (mf.EPS_DEN + 3 * mf.EPS_NUM) < mf.K * dc[v] * mf.EPS_DEN:
                    st_['FAIL.B'] += 1
        return b

    old = mf.portal_bounds
    mf.portal_bounds = bounds
    try:
        nm = rng.choice(['rand', 'two', 'hi', 'lo'])
        # tau from mU: parallel arcs are possible in general, see MAXFLOW.md Section 3
        m = len(I.darts)
        U = max(I.cap.values()) or 1
        tau = 0
        while 5 ** tau < (I.nf + 1) * (m * U + 1):
            tau += 1
        lam, f = mf.run(I, rng, nm, st, iters=tau)
    finally:
        mf.portal_bounds = old
    st['runs'] += 1
    st['chk.value'] += 1
    if lam != mf.maxflow(I, I.cap):
        st['FAIL.value'] += 1
    mf.check_flow(I, f, lam, st)
    st['max_S'] = max(st['max_S'], len(qi))


def main():
    seed, secs = int(sys.argv[1]), float(sys.argv[2])
    big = len(sys.argv) > 3 and sys.argv[3] == 'big'
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    while time.time() - t0 < secs:
        case(rng, st, big)
    fails = {k: v for k, v in st.items() if k.startswith('FAIL')}
    print(seed, dict(st))
    print('FAILS', fails)


if __name__ == '__main__':
    main()
