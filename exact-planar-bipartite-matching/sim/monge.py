"""Spot check of the compression behind (B5) on digraphs with absent arcs, as the child digraphs of notes/DIRECTED.md have.
Usage: python3 -I monge.py SEED SECS [control]. The control adds 3 random arcs, which are in general not planar, and must fire.

[2, Lemma 13]: for terminals on two faces, the terminals of f1 reached by u on f2 form one cyclic run of the active terminals.
[2, Lemma 10]: for a face cut into two arcs C1, C2, the terminals of C2 reached by u in C1 form one run of the active ones.
Same face, no cut: reported separately, since the literal definition of active gives no compression there.
"""
import collections, json, random, sys, time
import networkx as nx


def reach(D, srcs):
    seen, st = set(srcs), list(srcs)
    while st:
        x = st.pop()
        for y in D.get(x, ()):
            if y not in seen:
                seen.add(y)
                st.append(y)
    return seen


def faces_of(G):
    ok, emb = nx.check_planarity(G)
    assert ok
    seen, out = set(), []
    for u, v in emb.edges():
        if (u, v) in seen:
            continue
        w, a, b = [], u, v
        while True:
            seen.add((a, b))
            w.append(a)
            a, b = emb.next_face_half_edge(a, b)
            if (a, b) == (u, v):
                break
        out.append(w)
    return out


def rand_planar(rng):
    k = rng.randrange(3)
    if k == 0:
        G = nx.convert_node_labels_to_integers(nx.grid_2d_graph(rng.randrange(3, 9), rng.randrange(3, 9)))
    elif k == 1:
        G = nx.Graph()
        faces = [(0, 1, 2), (0, 1, 2)]
        G.add_edges_from([(0, 1), (1, 2), (0, 2)])
        for v in range(3, rng.randrange(8, 40)):
            i = rng.randrange(len(faces))
            a, b, c = faces[i]
            faces[i] = (a, b, v)
            faces += [(b, c, v), (a, c, v)]
            G.add_edges_from([(a, v), (b, v), (c, v)])
    else:
        G = nx.convert_node_labels_to_integers(nx.grid_2d_graph(rng.randrange(3, 7), rng.randrange(3, 7)))
        H = nx.Graph()
        nxt = G.number_of_nodes()
        for u, v in G.edges():
            H.add_edge(u, nxt)
            H.add_edge(nxt, v)
            H.add_edge(u, nxt + 1)
            H.add_edge(nxt + 1, v)
            nxt += 2
        G = H
    for e in list(G.edges()):
        if rng.random() < 0.25:
            G.remove_edge(*e)
            if not nx.is_connected(G):
                G.add_edge(*e)
    return G


def rand_dig(G, rng):
    D = collections.defaultdict(set)
    p = rng.choice([(1, 1, 1, 1), (2, 3, 3, 1), (4, 2, 2, 0), (0, 3, 3, 2)])
    for u, v in G.edges():
        s = rng.choices([0, 1, 2, 3], p)[0]
        if s & 1:
            D[u].add(v)
        if s & 2:
            D[v].add(u)
    return D


def runs_cyc(order, mask):
    k = len(order)
    if k == 0:
        return 0
    b = [x in mask for x in order]
    if all(b):
        return 1
    return sum(1 for i in range(k) if b[i] and not b[i - 1])


def runs_lin(order, mask):
    b = [x in mask for x in order]
    return sum(1 for i in range(len(b)) if b[i] and (i == 0 or not b[i - 1]))


def main(seed, secs, control=False):
    rng = random.Random(seed)
    t0 = time.time()
    c = collections.Counter()
    bad = None
    while time.time() - t0 < secs:
        G = rand_planar(rng)
        fs = [f for f in faces_of(G) if len(set(f)) == len(f) and len(f) >= 3]
        if len(fs) < 2:
            continue
        rng.shuffle(fs)
        D = rand_dig(G, rng)
        if control:
            vs = sorted(G.nodes())
            for _ in range(3):
                D[rng.choice(vs)].add(rng.choice(vs))
        for f1 in fs[:6]:
            for f2 in fs[:6]:
                if f1 is f2:
                    continue
                T1 = [x for x in f1 if rng.random() < 0.9]
                T2 = [x for x in f2 if rng.random() < 0.9]
                if not T1 or not T2:
                    continue
                reachs = {u: reach(D, [u]) for u in T2}
                active = set()
                for u in T2:
                    active |= reachs[u] & set(T1)
                order = [x for x in T1 if x in active]
                for u in T2:
                    c['two_faces.checks'] += 1
                    r = runs_cyc(order, reachs[u])
                    c['two_faces.maxruns'] = max(c['two_faces.maxruns'], r)
                    if r > 1 and bad is None and not (set(T1) & set(T2)):
                        bad = dict(kind='two_faces', edges=list(G.edges()), arcs={k: sorted(v) for k, v in D.items()}, f1=f1, f2=f2, u=u)
                    if r > 1 and (set(T1) & set(T2)):
                        c['two_faces.shared_vertices_runs_gt1'] += 1
                    if r > 1 and not (set(T1) & set(T2)):
                        c['FAIL.two_faces'] += 1
        for f in fs[:6]:
            k = len(f)
            if k < 4:
                continue
            for _ in range(4):
                i = rng.randrange(1, k)
                C1, C2 = f[:i], f[i:]
                reachs = {u: reach(D, [u]) for u in C1}
                active = set()
                for u in C1:
                    active |= reachs[u] & set(C2)
                order = [x for x in C2 if x in active]
                for u in C1:
                    c['cut_face.checks'] += 1
                    r = runs_lin(order, reachs[u])
                    c['cut_face.maxruns'] = max(c['cut_face.maxruns'], r)
                    if r > 1:
                        c['FAIL.cut_face'] += 1
                        if bad is None:
                            bad = dict(kind='cut', edges=list(G.edges()), arcs={k: sorted(v) for k, v in D.items()}, C1=C1, C2=C2, u=u)
            # same face, literal
            reachs = {u: reach(D, [u]) for u in f}
            for u in f:
                r = runs_cyc(f, reachs[u])
                c['same_face.maxruns_uncut'] = max(c['same_face.maxruns_uncut'], r)
                c['same_face.checks'] += 1
    return dict(sorted(c.items())), bad


if __name__ == '__main__':
    r, bad = main(int(sys.argv[1]), float(sys.argv[2]), len(sys.argv) > 3)
    print(json.dumps(r))
    if bad:
        print(json.dumps(bad)[:2000])
