"""Stress checks for the Root Cut Lemma of notes/DETFLOW.md: arbitrary trees containing S - ab, the root
anywhere, w0 any corner with b = 1 at the root, hard families (S through every vertex, wheel rims, faces of
length 3, degree 1 and 2), and per level: connected skeleton, ports on one cycle of psi, tour cycle = bag,
genus 0, port, gap and hub counts, walk lengths in bags, congestion, pair property, balance from level 1,
height, and all root hub values from exact child metrics. Run: python -I stress.py <seed> <seconds>"""
import sys, random, math, time, heapq, collections
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import networkx as nx
import disks as K

import os
NMAX = int(os.environ.get("NMAX", "30"))
FAIL = collections.Counter()
ST = collections.Counter()
EX = {}

def fail(tag, info):
    FAIL[tag] += 1
    if tag not in EX:
        EX[tag] = info

def first_return(f, S, x):
    return K.first_return(f, S, x)

def uf_groups(items, pairs):
    p = {x: x for x in items}
    def f(x):
        while p[x] != x:
            p[x] = p[p[x]]; x = p[x]
        return x
    for a, b in pairs:
        p[f(a)] = f(b)
    g = collections.defaultdict(set)
    for x in items:
        g[f(x)].add(x)
    return list(g.values())

def make_tree(G, path, ab, rng, mode):
    """Spanning tree containing the path edges, not the edge ab; root anywhere."""
    pe = {frozenset((path[i], path[i + 1])) for i in range(len(path) - 1)}
    p = {v: v for v in G}
    def f(x):
        while p[x] != x:
            p[x] = p[p[x]]; x = p[x]
        return x
    T = nx.Graph(); T.add_nodes_from(G)
    for e in pe:
        u, v = tuple(e); p[f(u)] = f(v); T.add_edge(u, v)
    others = [e for e in G.edges() if frozenset(e) not in pe and frozenset(e) != ab]
    if mode == 'bfs':
        seen = set(path); q = list(path)
        for u in q:
            for v in G[u]:
                if v not in seen:
                    seen.add(v); T.add_edge(u, v); q.append(v)
    elif mode == 'dfs':
        # DFS-like: greedy long paths
        start = rng.choice(path)
        seen = set(path); stack = [start]
        order = []
        # random DFS from path vertices
        for s in rng.sample(path, len(path)):
            stack = [s]
            while stack:
                x = stack[-1]
                nb = [y for y in G[x] if y not in seen and frozenset((x, y)) != ab]
                if nb:
                    y = rng.choice(nb); seen.add(y); T.add_edge(x, y); p[f(x)] = f(y); stack.append(y)
                else:
                    stack.pop()
    else:
        rng.shuffle(others)
        for u, v in others:
            if f(u) != f(v):
                p[f(u)] = f(v); T.add_edge(u, v)
    if not nx.is_connected(T):
        return None
    assert T.number_of_edges() == G.number_of_nodes() - 1
    assert not T.has_edge(*tuple(ab)) or len(ab) < 2
    rmode = rng.random()
    if rmode < 0.3:
        root = rng.choice(path)
    elif rmode < 0.5:
        root = rng.choice([path[0], path[-1]])
    else:
        root = rng.choice(list(G))
    parent = {}
    for u, v in nx.bfs_edges(T, root):
        parent[v] = u
    return parent, root

def check_instance(G, emb, lens, face_darts, rng, mode):
    M = K.Map(G, emb, lens).finish()
    Md = K.Doubled(M)
    cyc = [M.vert[d] for d in face_darts]
    a, b = cyc[-1], cyc[0]
    ab = frozenset((a, b))
    r = make_tree(G, cyc, ab, rng, mode)
    if r is None:
        return
    parent, root = r
    t = K.Tree(M, parent, root)
    n = M.n
    h = max(t.dep.values())
    rootc = [2 * d + 1 for d in range(M.D) if M.vert[d] == root]
    w0 = rng.choice(rootc)
    da, db = face_darts[-1], face_darts[0]
    x, y = 2 * da + 1, 2 * db + 1
    if w0 in (x, y):
        ST['w0_is_xy'] += 1
    k = 1
    while 2 * n >= 2 ** k:
        k += 1
    Hmax = 1 + 3 * k
    levels, cuts = [{w0}], []
    C = {x, y}
    info = dict(n=n, edges=sorted(G.edges()), S=cyc, root=root, parent=parent, w0=w0, x=x, y=y, mode=mode)
    while True:
        G0 = levels[-1]
        try:
            K.is_level(t, Md, G0)
        except AssertionError as e:
            fail('is_level:' + str(e), info); return
        comp, cnt, mk = K.npof(t, Md, G0)
        if not mk:
            break
        if len(levels) > 1:
            try:
                C = K.choose_cut(t, Md, G0, rng)
            except AssertionError as e:
                fail('choose_cut:' + str(e), info); return
        per = collections.Counter(comp[c] for c in C)
        if max(per.values()) > 2:
            fail('two', info)
        G1 = K.nxt(t, Md, G0, C)
        for c in C:
            if c % 2 == 0 and 2 * (Md.rev(c) // 2) not in G1:
                fail('pair', info)
        if len(levels) > 1:
            comp1, cnt1, _ = K.npof(t, Md, G1)
            for z in mk:
                if 4 * cnt1.get(comp1[z], 0) + 2 > 3 * cnt[comp[z]]:
                    fail('balance', info); break
        cuts.append(C); levels.append(G1)
        if len(levels) - 1 > Hmax:
            fail('height', info); return
    H = len(levels) - 1
    ST['maxH'] = max(ST['maxH'], H)
    if set(cyc) - K.has_corner(Md, levels[1]):
        fail('part4', info)
    face_cyc_of = None
    for d, Gd in enumerate(levels):
        sp = K.split(Md, Gd)
        comp = K.components(sp)
        # skeleton connected
        A = lambda z: first_return(Md.rot, Gd, z)
        B = lambda z: first_return(Md.face, Gd, z)
        grp = uf_groups(list(Gd), [(z, A(z)) for z in Gd] + [(z, B(z)) for z in Gd])
        if len(grp) != 1:
            fail('skel', info)
        psi = lambda z: A(B(z))
        bags = collections.defaultdict(list)
        for z in range(Md.D):
            bags[comp[z]].append(z)
        ports = collections.defaultdict(set)
        for z in Gd:
            ports[comp[z]].add(z)
        mk = K.marks(t, Md, Gd)
        cn = K.cone(Md, Gd)
        tour = lambda z: (cn.rev(cn.rot(z)) if cn.rot(z) in mk else cn.rot(z))
        tc = K.cycles(tour, Md.D)
        rotc = K.cycles(sp.rot, Md.D)
        facec = K.cycles(sp.face, Md.D)
        for bg, darts in bags.items():
            P = ports[bg]
            if not P:
                fail('bag_without_port', info); continue
            # one psi cycle
            s = next(iter(P)); cy = {s}; z = psi(s)
            while z != s:
                cy.add(z); z = psi(z)
            if cy != P:
                fail('psi_cycle', info)
            # tour cycle = bag
            if {tc[z] for z in darts} != {tc[darts[0]]}:
                fail('tour_cycle', dict(info, depth=d))
            # genus 0
            V = len({rotc[z] for z in darts}); E = len(darts) // 2; F = len({facec[z] for z in darts})
            if V - E + F != 2:
                fail('genus', dict(info, depth=d))
            # diam
            J = len(P); Gg = sum(1 for z in P if z % 2)
            if J > 1 + d * (2 + 4 * h): fail('ports', info)
            if Gg > 1 + 2 * d: fail('gaps', info)
            adj = collections.defaultdict(set)
            vs = set()
            for z in darts:
                u, v = Md.vert(z), Md.vert(Md.rev(z))
                adj[u].add(v); vs.add(u)
            bound = (Gg + 1) * (2 * (h + J) + 1)
            spanb = (2 * H + 2) * (2 * (h + (1 + H * (2 + 4 * h))) + 1)
            src = rng.sample(sorted(vs), min(len(vs), 6))
            for s0 in src:
                dist = {s0: 0}; q = [s0]
                for u in q:
                    for v in adj[u]:
                        if v not in dist:
                            dist[v] = dist[u] + 1; q.append(v)
                if set(dist) != vs:
                    fail('bag_disconnected', info); break
                mx = max(dist.values())
                ST['diam_ratio_max'] = max(ST['diam_ratio_max'], mx / bound)
                if mx > bound: fail('bag_diam', info)
                if mx > spanb: fail('span', info)
        # congestion
        for dd in range(M.D):
            if dd < M.rev[dd]:
                bs = {comp[2 * dd], comp[2 * dd + 1], comp[2 * M.rev[dd]], comp[2 * M.rev[dd] + 1]}
                if len(bs) > 2: fail('congestion', info)
        if d + 1 < len(levels):
            hubs = collections.defaultdict(set)
            for z in levels[d + 1]:
                hubs[comp[z]].add(Md.vert(z))
            hb = max(len(s) for s in hubs.values())
            if hb > 1 + (H + 1) * (2 + 4 * h): fail('hubs', info)
            if hb > 1 + (d + 1) * (2 + 4 * h): fail('hubs_depth', info)
    # x and y in different bags at level 1
    sp1 = K.split(Md, levels[1]); c1 = K.components(sp1)
    if c1[x] == c1[y] and x != y:
        fail('xy_same_bag', info)
    # root values for all hubs of the root vs dist in G (directed)
    vc = K.cycles(sp1.rot, Md.D)
    adj = collections.defaultdict(list)
    for z in range(Md.D):
        adj[vc[z]].append((vc[sp1.rev(z)], Md.length(z)))
    def dij(adj, s):
        dist = {s: 0}; pq = [(0, s)]
        while pq:
            dv, v = heapq.heappop(pq)
            if dv > dist[v]: continue
            for w, l in adj.get(v, []):
                if dv + l < dist.get(w, math.inf):
                    dist[w] = dv + l; heapq.heappush(pq, (dv + l, w))
        return dist
    corners = sorted(levels[1])
    lam = {p: dij(adj, vc[p]) for p in corners}
    cadj = {p: [] for p in corners}
    for p in corners:
        for q in corners:
            if p != q and vc[q] in lam[p]: cadj[p].append((q, lam[p][vc[q]]))
            if p != q and Md.vert(p) == Md.vert(q): cadj[p].append((q, 0))
    Gd = nx.DiGraph()
    for dd in range(M.D):
        Gd.add_edge(M.vert[dd], M.head[dd], weight=M.len[dd])
    hubsR = sorted({Md.vert(p) for p in corners})
    for u in rng.sample(hubsR, min(len(hubsR), 8)):
        dG = nx.single_source_dijkstra_path_length(Gd, u)
        pu = next(p for p in corners if Md.vert(p) == u)
        dc = dij(cadj, pu)
        for v in hubsR:
            best = min(dc.get(q, math.inf) for q in corners if Md.vert(q) == v)
            ST['rootvals'] += 1
            if best != dG[v]: fail('root_value', info)
    ST['inst'] += 1
    ST['maxS_frac'] = max(ST['maxS_frac'], len(cyc) / n)
    ST['maxh'] = max(ST['maxh'], h)

def simple_faces(G, emb):
    return [f for f in K.facial_walks(G, emb) if len(f) >= 3 and len(set(f)) == len(f)]

def family(rng):
    fam = rng.choice(['cycle', 'cyclechords', 'wheel_rim', 'tri', 'subdiv', 'pendants', 'ladder', 'fan', 'bigface', 'grid', 'k4chain'])
    n = rng.randint(4, NMAX)
    big = None
    if fam == 'cycle':
        G = nx.cycle_graph(n)
    elif fam == 'cyclechords':
        G = nx.cycle_graph(n)
        for _ in range(rng.randint(1, n)):
            i, j = rng.sample(range(n), 2); G.add_edge(i, j)
            if not nx.check_planarity(G)[0]: G.remove_edge(i, j)
        big = list(range(n))
    elif fam == 'wheel_rim':
        G = nx.wheel_graph(n); big = list(range(1, n))
    elif fam == 'fan':
        G = nx.path_graph(n); G.add_node(n)
        for i in range(n): G.add_edge(i, n)
    elif fam == 'tri':
        import scipy.spatial as ss
        pts = [(rng.random(), rng.random()) for _ in range(n)]
        tri = ss.Delaunay(pts)
        G = nx.Graph(); G.add_nodes_from(range(n))
        for s in tri.simplices:
            for i in range(3): G.add_edge(int(s[i]), int(s[(i + 1) % 3]))
    elif fam == 'subdiv':
        H0 = nx.wheel_graph(rng.randint(4, 8)); G = nx.Graph(); c = 1000
        for u, v in H0.edges():
            k = rng.randint(0, 3); prev = u
            for _ in range(k): G.add_edge(prev, c); prev = c; c += 1
            G.add_edge(prev, v)
    elif fam == 'pendants':
        G = nx.cycle_graph(rng.randint(3, 10)); c = 100
        for _ in range(rng.randint(1, 15)):
            u = rng.choice(list(G)); G.add_edge(u, c); c += 1
    elif fam == 'ladder':
        G = nx.ladder_graph(rng.randint(2, 10))
    elif fam == 'grid':
        G = nx.grid_2d_graph(rng.randint(2, 5), rng.randint(2, 5))
    elif fam == 'bigface':
        # long cycle S with a small dense blob attached at one vertex and a long tail
        L = rng.randint(3, 20); G = nx.cycle_graph(L); c = 100
        for _ in range(rng.randint(0, 8)):
            u = rng.choice(list(G)); v = c; c += 1; G.add_edge(u, v)
            w = rng.choice(list(G))
            if w == v: continue
            G.add_edge(v, w)
            if not nx.check_planarity(G)[0]: G.remove_edge(v, w)
    else:
        G = nx.complete_graph(4); c = 4
        for _ in range(rng.randint(0, 4)):
            u, v = rng.sample(list(G), 2); G.add_edge(u, c); G.add_edge(v, c); G.add_edge(c, c + 1); G.add_edge(u, c + 1); c += 2
            if not nx.check_planarity(G)[0]: return None
    G.remove_edges_from(list(nx.selfloop_edges(G)))
    mapping = {v: i for i, v in enumerate(G)}
    G = nx.relabel_nodes(G, mapping)
    if not nx.is_connected(G): return None
    ok, emb = nx.check_planarity(G)
    if not ok: return None
    W = rng.choice([1, 2, 10, 1000, 10**6])
    lens = {}
    for u, v in G.edges():
        if rng.random() < 0.3:
            lens[(u, v)] = 1; lens[(v, u)] = W
        else:
            lens[(u, v)] = rng.randint(1, W); lens[(v, u)] = rng.randint(1, W)
    faces = simple_faces(G, emb)
    if not faces: return None
    # prefer the biggest face sometimes
    if rng.random() < 0.5:
        f = max(faces, key=len)
    else:
        f = rng.choice(faces)
    i = rng.randrange(len(f)); f = f[i:] + f[:i]
    M0 = K.Map(G, emb, lens)
    darts = [M0.idx[(f[j], f[(j + 1) % len(f)])] for j in range(len(f))]
    return fam, G, emb, lens, darts

def main():
    seed, secs = int(sys.argv[1]), float(sys.argv[2])
    rng = random.Random(seed)
    t0 = time.time(); fams = collections.Counter()
    while time.time() - t0 < secs:
        I = family(rng)
        if I is None: continue
        fam, G, emb, lens, darts = I
        mode = rng.choice(['rand', 'dfs'])
        check_instance(G, emb, lens, darts, rng, mode)
        fams[fam] += 1
    print('ST', dict(ST)); print('fams', dict(fams)); print('FAIL', dict(FAIL))
    for k, v in EX.items():
        print('EX', k, v)

if __name__ == '__main__':
    main()
