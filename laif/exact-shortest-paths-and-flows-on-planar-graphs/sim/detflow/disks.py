"""The disk hierarchy of notes/DISKS.md, with the first cut prescribed along a facial cycle.

The definitions follow lean/SsspFlow (Disks.lean, Bags.lean, Tour.lean, Splice.lean):
doubled map, levels, split, cone, tour of the marks, balance rule, walks up the tree.
The first cut is the pair of corners of one face F at the two ends a, b of an edge ab of F,
where the rest of the boundary of F is a path of the tree. Every later cut follows the rule.

Checks per instance (assert):
  every level is a level (IsLevel), every cut has at most two corners per bag and the pair
  property, later cuts are balanced, no vertex is without a corner after 1 + 3k levels,
  port, gap and hub counts, congestion two per depth, every vertex of the face is a hub of
  the root, and the values: for every bag the least walks between its hubs through the exact
  port metrics of its children, with free moves at a vertex, equal the distances in the bag;
  at the root they are the distances in G between the vertices of the face.
Run: python -I disks.py <seed> <seconds> [bal0] [nofree]
  bal0 counts forced first cuts that are not balanced; nofree drops the free moves at a vertex,
  which must make root values wrong (control).
"""
import heapq, math, random, sys, time
import networkx as nx


# ---------- planar maps ----------

class Map:
    """Darts 0..2m-1 of a plane graph: rot (next dart around the tail), rev, vert, length."""
    def __init__(self, G, emb, lens):
        self.n = G.number_of_nodes()
        idx = {}
        darts = []
        for u, v in G.edges():
            for a, b in ((u, v), (v, u)):
                idx[(a, b)] = len(darts)
                darts.append((a, b))
        self.darts, self.idx = darts, idx
        self.rev = [idx[(b, a)] for a, b in darts]
        self.vert = [a for a, b in darts]
        self.head = [b for a, b in darts]
        self.rot = [idx[(a, emb[a][b]['cw'])] for a, b in darts]
        self.len = [lens[(a, b)] for a, b in darts]
        self.D = len(darts)

    def face(self, d):  # rot^-1 (rev d)
        return self.rotinv[self.rev[d]]

    def finish(self):
        self.rotinv = [0] * self.D
        for d, e in enumerate(self.rot):
            self.rotinv[e] = d
        return self


def first_return(f, S, x):
    if x not in S:
        return x
    y = f(x)
    while y not in S:
        y = f(y)
    return y


class Doubled:
    """The doubled map: darts (d, b) coded 2d + b."""
    def __init__(self, M):
        self.M = M
        self.D = 2 * M.D

    def rot(self, z):
        d, b = divmod(z, 2)
        return 2 * self.M.rot[d] if b else 2 * d + 1

    def rotinv(self, z):
        d, b = divmod(z, 2)
        return 2 * d if b else 2 * self.M.rotinv[d] + 1

    def rev(self, z):
        d, b = divmod(z, 2)
        return 2 * self.M.rev[d] + (1 - b)

    def face(self, z):
        return self.rotinv(self.rev(z))

    def vert(self, z):
        return self.M.vert[z // 2]

    def length(self, z):
        return self.M.len[z // 2]


class Glued:
    """glue nu: rot' = rot o nu, rev unchanged."""
    def __init__(self, base, nu):
        self.base, self.nu = base, nu
        self.D = base.D
        self._rot = [base.rot(nu(z)) for z in range(base.D)]
        self._inv = [0] * base.D
        for z, w in enumerate(self._rot):
            self._inv[w] = z

    def rot(self, z):
        return self._rot[z]

    def rotinv(self, z):
        return self._inv[z]

    def rev(self, z):
        return self.base.rev(z)

    def face(self, z):
        return self._inv[self.rev(z)]


def split(Md, G):
    # glue (nodeReturn G)^-1: rot'(z) = rot(nodeReturn^-1 z)
    inv = {}
    for x in G:
        inv[first_return(Md.rot, G, x)] = x
    return Glued(Md, lambda z: inv.get(z, z))


def cone(Md, G):
    return Glued(Md, lambda z: first_return(Md.face, G, z))


def components(m):
    """Components under rot and rev: list of component ids."""
    comp = [-1] * m.D
    c = 0
    for s in range(m.D):
        if comp[s] >= 0:
            continue
        st = [s]
        comp[s] = c
        while st:
            x = st.pop()
            for y in (m.rot(x), m.rev(x)):
                if comp[y] < 0:
                    comp[y] = c
                    st.append(y)
        c += 1
    return comp


def cycles(f, D):
    cyc = [-1] * D
    for s in range(D):
        if cyc[s] < 0:
            x = s
            while cyc[x] < 0:
                cyc[x] = s
                x = f(x)
    return cyc


# ---------- the tree ----------

class Tree:
    def __init__(self, M, parent, root):
        self.M, self.root, self.parent = M, root, parent
        self.dep = {root: 0}
        order = [root]
        ch = {}
        for v, p in parent.items():
            ch.setdefault(p, []).append(v)
        for v in order:
            for w in ch.get(v, []):
                self.dep[w] = self.dep[v] + 1
                order.append(w)
        assert len(order) == M.n
        self.up = {v: M.idx[(v, p)] for v, p in parent.items()}

    def c1(self, v):
        return 2 * self.up[v] + 1

    def c0(self, v):
        return 2 * self.M.rev[self.up[v]]

    def r0(self, v):
        return 2 * self.up[v]

    def anc(self, v):
        out = [v]
        while v != self.root:
            v = self.parent[v]
            out.append(v)
        return out


def has_corner(Md, G):
    return {Md.vert(z) for z in G}


def marks(t, Md, G):
    hc = has_corner(Md, G)
    out = set()
    for v in range(t.M.n):
        if v not in hc:
            assert v != t.root
            out |= {t.c1(v), t.c0(v)}
    return out


def rails_up(t, Md, G, c):
    hc = has_corner(Md, G)
    out = set()
    for w in t.anc(Md.vert(c)):
        if w in hc:
            break
        out |= {t.r0(w), t.c0(w)}
    return out


def nxt(t, Md, G, C):
    out = set(G)
    for c in C:
        out.add(c)
        out |= rails_up(t, Md, G, c)
    return out


def is_level(t, Md, G):
    assert any(Md.vert(z) == t.root for z in G)
    for z in G:
        v = Md.vert(z)
        if v != t.root:
            assert t.r0(v) in G and t.c0(v) in G, "rails"
    for z in G:
        if z % 2 == 0:
            assert 2 * (Md.rev(z) // 2) in G, "pairs"
    # skeleton connected: vertices with corners connected by tree edges with both rails
    hc = has_corner(Md, G)
    for v in hc:
        for w in t.anc(v):
            assert w in hc


def npof(t, Md, G):
    """Marks per component of the split."""
    sp = split(Md, G)
    comp = components(sp)
    mk = marks(t, Md, G)
    cnt = {}
    for z in mk:
        cnt[comp[z]] = cnt.get(comp[z], 0) + 1
    return comp, cnt, mk


# ---------- the rule ----------

def arc_mass(order, pos, F, x, y):
    """Marks in the arc (x, y] of a cycle given as a list."""
    i, j = pos[x], pos[y]
    L = len(order)
    k, c = (i + 1) % L, 0
    while True:
        if order[k] in F:
            c += 1
        if k == j:
            break
        k = (k + 1) % L
    return c


def choose_cut(t, Md, G, rng):
    sp_comp, cnt, mk = npof(t, Md, G)
    cn = cone(Md, G)
    tour = lambda z: (cn.rev(cn.rot(z)) if cn.rot(z) in mk else cn.rot(z))
    fcyc = cycles(cn.face, Md.D)
    C = set()
    bags = set(sp_comp)
    for b in bags:
        m = cnt.get(b, 0)
        darts = [z for z in range(Md.D) if sp_comp[z] == b]
        if m == 0:
            continue
        if m < 4:
            hc = has_corner(Md, G)
            np_v = sorted({Md.vert(z) for z in darts} - hc)
            v = rng.choice(np_v)
            C.add(t.r0(v))
            continue
        # tour cycle of the bag: all darts of the bag in one cycle of the tour of the cone
        s = darts[0]
        order = [s]
        x = tour(s)
        while x != s:
            order.append(x)
            x = tour(x)
        assert set(order) == set(darts), "tour cycle is not the bag"
        pos = {z: i for i, z in enumerate(order)}
        good = []
        byface = {}
        for z in order:
            byface.setdefault(fcyc[z], []).append(z)
        for f, zs in byface.items():
            for x in zs:
                for y in zs:
                    if x != y and 4 * arc_mass(order, pos, mk, x, y) + 2 <= 3 * m \
                            and 4 * arc_mass(order, pos, mk, y, x) + 2 <= 3 * m:
                        good.append((x, y))
        assert good, "balance lemma"
        x, y = rng.choice(good)
        C |= {x, y}
    return C


# ---------- one instance ----------

def build(G, emb, lens, face_darts, rng):
    """face_darts: the darts of a simple facial walk; the last one is the edge ab off the tree."""
    M = Map(G, emb, lens).finish()
    Md = Doubled(M)
    cyc = [M.vert[d] for d in face_darts]
    path = cyc  # a = cyc[-1] -> b = cyc[0] is the edge off the tree; path cyc[0..L-1] in the tree
    root = path[rng.randrange(len(path))]
    parent = {}
    ri = path.index(root)
    for i in range(ri):
        parent[path[i]] = path[i + 1]
    for i in range(ri + 1, len(path)):
        parent[path[i]] = path[i - 1]
    seen = set(path)
    dq = list(path)
    while dq:
        x = dq.pop(0)
        for y in G[x]:
            if y not in seen:
                seen.add(y)
                parent[y] = x
                dq.append(y)
    t = Tree(M, parent, root)
    return M, Md, t, path


CTRL = set()


def run_instance(G, emb, lens, face_darts, rng, st):
    M, Md, t, path = build(G, emb, lens, face_darts, rng)
    n = M.n
    h = max(t.dep.values())
    # w0: a corner with b = 1 at the root
    w0 = 2 * next(d for d in range(M.D) if M.vert[d] == t.root) + 1
    levels, cuts = [{w0}], []
    # forced first cut: the corners (d, 1) of the face at a and at b
    a, b = path[-1], path[0]
    da, db = face_darts[-1], face_darts[0]
    assert M.vert[da] == a and M.vert[db] == b
    C0 = {2 * da + 1, 2 * db + 1}
    k = 1
    while 2 * n >= 2 ** k:
        k += 1
    Hmax = 1 + 3 * k
    C = C0
    while True:
        G0 = levels[-1]
        is_level(t, Md, G0)
        comp, cnt, mk = npof(t, Md, G0)
        if not mk:
            break
        if len(levels) > 1:
            C = choose_cut(t, Md, G0, rng)
        # two per bag, pair
        per = {}
        for c in C:
            per[comp[c]] = per.get(comp[c], 0) + 1
        assert max(per.values()) <= 2
        G1 = nxt(t, Md, G0, C)
        for c in C:
            if c % 2 == 0:
                assert 2 * (Md.rev(c) // 2) in G1, "IsCut.pair"
        comp1, cnt1, _ = npof(t, Md, G1)
        if len(levels) > 1 or 'bal0' in CTRL:
            for z in mk:
                if 4 * cnt1.get(comp1[z], 0) + 2 > 3 * cnt[comp[z]]:
                    if len(levels) == 1:
                        st['unbal0'] = st.get('unbal0', 0) + 1
                        break
                    raise AssertionError("balance")
        cuts.append(C)
        levels.append(G1)
        assert len(levels) - 1 <= Hmax, "height"
    H = len(levels) - 1
    st['maxH'] = max(st.get('maxH', 0), H)
    st['maxHrel'] = max(st.get('maxHrel', 0), H / Hmax)
    # the vertices of the face are hubs of the root
    assert set(path) <= has_corner(Md, levels[1])
    # counts and congestion
    for d, Gd in enumerate(levels):
        sp = split(Md, Gd)
        comp = components(sp)
        ports, gaps = {}, {}
        for z in Gd:
            ports[comp[z]] = ports.get(comp[z], 0) + 1
            if z % 2:
                gaps[comp[z]] = gaps.get(comp[z], 0) + 1
        assert max(ports.values()) <= 1 + d * (2 + 4 * h), "ports"
        assert max(gaps.values()) <= 1 + 2 * d, "gaps"
        for e in range(M.D // 2):
            pass
        # every edge of G: its two copies lie in at most two bags of this depth
        for dd in range(M.D):
            if dd < M.rev[dd]:
                bags = {comp[2 * dd], comp[2 * dd + 1], comp[2 * M.rev[dd]], comp[2 * M.rev[dd] + 1]}
                assert len(bags) <= 2, "congestion"
        if d + 1 < len(levels):
            hubs = {}
            for z in levels[d + 1]:
                hubs.setdefault(comp[z], set()).add(Md.vert(z))
            assert max(len(s) for s in hubs.values()) <= 1 + (H + 1) * (2 + 4 * h), "hubs"
    # values: composition of exact child metrics equals the bag metric
    def split_dist(Gd):
        sp = split(Md, Gd)
        vc = cycles(sp.rot, Md.D)  # vertex of the split = rot cycle
        adj = {}
        for z in range(Md.D):
            adj.setdefault(vc[z], []).append((vc[sp.rev(z)], Md.length(z)))
        return sp, vc, adj

    def dij(adj, s):
        dist = {s: 0}
        pq = [(0, s)]
        while pq:
            dv, v = heapq.heappop(pq)
            if dv > dist[v]:
                continue
            for w, l in adj.get(v, []):
                if dv + l < dist.get(w, math.inf):
                    dist[w] = dv + l
                    heapq.heappush(pq, (dv + l, w))
        return dist

    for d in range(len(levels) - 1):
        Ga, Gb = levels[d], levels[d + 1]
        spa, vca, adja = split_dist(Ga)
        spb, vcb, adjb = split_dist(Gb)
        compa = components(spa)
        # child metric on the corners of Gb: exact distances in the split at Gb
        corners = sorted(Gb)
        lam = {p: dij(adjb, vcb[p]) for p in corners}
        # graph on the corners of Gb: child metric arcs, free moves between corners on one vertex of the split at Ga
        cadj = {p: [] for p in corners}
        for p in corners:
            for q in corners:
                if p != q and vcb[q] in lam[p]:
                    cadj[p].append((q, lam[p][vcb[q]]))
                if p != q and vca[p] == vca[q]:
                    cadj[p].append((q, 0))
        sample = corners if len(corners) <= 40 else rng.sample(corners, 40)
        for p in sample:
            dc = dij(cadj, p)
            da_ = dij(adja, vca[p])
            for q in corners:
                if compa[q] == compa[p]:
                    assert dc.get(q, math.inf) == da_.get(vca[q], math.inf), ("values", d)
                    st['vals'] = st.get('vals', 0) + 1
    # at the root: the values between the face vertices are the distances in G
    spb, vcb, adjb = split_dist(levels[1])
    Gd = nx.DiGraph()
    for dd in range(M.D):
        Gd.add_edge(M.vert[dd], M.head[dd], weight=M.len[dd])
    for x in path:
        dist = nx.single_source_dijkstra_path_length(Gd, x)
        # through the composed values at the root
        corners = sorted(levels[1])
        lam = {p: dij(adjb, vcb[p]) for p in corners}
        cadj = {p: [] for p in corners}
        for p in corners:
            for q in corners:
                if p != q and vcb[q] in lam[p]:
                    cadj[p].append((q, lam[p][vcb[q]]))
                if p != q and Md.vert(p) == Md.vert(q) and 'nofree' not in CTRL:
                    cadj[p].append((q, 0))
        px = next(p for p in corners if Md.vert(p) == x)
        dc = dij(cadj, px)
        for y in path:
            best = min(dc.get(q, math.inf) for q in corners if Md.vert(q) == y)
            if 'nofree' in CTRL and best != dist[y]:
                st['caught'] = st.get('caught', 0) + 1
                continue
            assert best == dist[y], "root value"
            st['root'] = st.get('root', 0) + 1
    st['inst'] = st.get('inst', 0) + 1
    st['maxS'] = max(st.get('maxS', 0), len(path))
    return H


# ---------- planar families ----------

def facial_walks(G, emb):
    seen, faces = set(), []
    for u, v in G.edges():
        for a, b in ((u, v), (v, u)):
            if (a, b) in seen:
                continue
            f = emb.traverse_face(a, b, mark_half_edges=seen)
            faces.append(f)
    return faces


def instance(rng):
    fam = rng.choice(['tri', 'grid', 'wheel', 'delaunay_sparse', 'outer', 'tree_plus'])
    n = rng.randint(5, 40)
    if fam == 'tri' or fam == 'delaunay_sparse':
        import scipy.spatial as ss
        pts = [(rng.random(), rng.random()) for _ in range(n)]
        tri = ss.Delaunay(pts)
        G = nx.Graph()
        G.add_nodes_from(range(n))
        for s in tri.simplices:
            for i in range(3):
                G.add_edge(int(s[i]), int(s[(i + 1) % 3]))
        if fam == 'delaunay_sparse':
            for e in list(G.edges()):
                if rng.random() < 0.4:
                    G.remove_edge(*e)
                    if not nx.is_connected(G):
                        G.add_edge(*e)
    elif fam == 'grid':
        a = rng.randint(2, 6)
        b = rng.randint(2, 6)
        G = nx.convert_node_labels_to_integers(nx.grid_2d_graph(a, b))
    elif fam == 'wheel':
        G = nx.wheel_graph(n)
    elif fam == 'outer':
        G = nx.cycle_graph(n)
        for _ in range(rng.randint(0, n)):
            i, j = sorted(rng.sample(range(n), 2))
            G.add_edge(i, j)
            ok, _ = nx.check_planarity(G)
            if not ok:
                G.remove_edge(i, j)
    else:
        G = nx.random_labeled_tree(n, seed=rng.randrange(10 ** 9)) if hasattr(nx, 'random_labeled_tree') \
            else nx.random_tree(n, seed=rng.randrange(10 ** 9))
        for _ in range(rng.randint(1, n)):
            i, j = rng.sample(range(n), 2)
            G.add_edge(i, j)
            ok, _ = nx.check_planarity(G)
            if not ok:
                G.remove_edge(i, j)
    G = nx.convert_node_labels_to_integers(G)
    ok, emb = nx.check_planarity(G)
    assert ok
    W = rng.choice([1, 3, 20, 1000])
    lens = {}
    for u, v in G.edges():
        lens[(u, v)] = rng.randint(1, W)
        lens[(v, u)] = rng.randint(1, W)
    # a face whose boundary is a simple cycle
    faces = [f for f in facial_walks(G, emb) if len(f) >= 3 and len(set(f)) == len(f)]
    if not faces:
        return None
    f = rng.choice(faces)
    i = rng.randrange(len(f))
    f = f[i:] + f[:i]
    M0 = Map(G, emb, lens)
    darts = [M0.idx[(f[j], f[(j + 1) % len(f)])] for j in range(len(f))]
    # rotate so the last dart is the edge a -> b off the tree: path f[0], ..., f[-1] stays in the tree
    return fam, G, emb, lens, darts


def main():
    seed, secs = int(sys.argv[1]), float(sys.argv[2])
    CTRL.update(sys.argv[3:])
    rng = random.Random(seed)
    st = {}
    t0 = time.time()
    fams = {}
    while time.time() - t0 < secs:
        I = instance(rng)
        if I is None:
            continue
        fam, G, emb, lens, darts = I
        # the facial walk: corner of the face at f[j] is the dart leaving f[j] along the face
        run_instance(G, emb, lens, darts, rng, st)
        fams[fam] = fams.get(fam, 0) + 1
    print(seed, st, fams)


if __name__ == '__main__':
    main()
