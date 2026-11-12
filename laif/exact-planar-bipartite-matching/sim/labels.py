"""Exact labels on a decomposition and queries from a virtual source: centralized simulation of notes/EXACT_LABELS.md.

It runs the bottom-up rule of Lemma 1 and the query of Theorem 2. The truth is Dijkstra in the bag and in G. It counts words, not rounds.
  python3 -I labels.py <seed> <seconds> [big]
  python3 -I labels.py ctl <seed> <seconds>
"""
import collections, heapq, json, math, os, random, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode = True
sys.setrecursionlimit(100000)
import numpy as np
import networkx as nx
import gm, mm

INF = 1 << 58
CTL = ['seponly', 'noq', 'deepest', 'rootonly', 'swap', 'noqrev']


def lengths(V, E, rng):
    """Arcs on edges of the network, each direction present or not, lengths with zeros and a wide range."""
    W = rng.choice([1, 3, 20, 1000, 10 ** 6])
    zero = rng.choice([0.0, 0.3, 0.8])
    drop = rng.choice([0.0, 0.2, 0.5])
    w = {}
    for u, v in E:
        for a, b in ((u, v), (v, u)):
            if rng.random() >= drop:
                w[a, b] = 0 if rng.random() < zero else rng.randrange(1, W + 1)
    return w


def dijkstra(V, out, src):
    """src: vertex to offset. Distances from a virtual source, over the adjacency out."""
    d = dict.fromkeys(V, INF)
    h = []
    for v, x in src.items():
        d[v] = x
        h.append((x, v))
    heapq.heapify(h)
    while h:
        x, v = heapq.heappop(h)
        if x > d[v]:
            continue
        for y, c in out.get(v, ()):
            if x + c < d[y]:
                d[y] = x + c
                heapq.heappush(h, (x + c, y))
    return d


def bag_out(b, w, rev=False):
    out = collections.defaultdict(list)
    for x, y in b.eset:
        for p, q in ((x, y), (y, x)):
            if (p, q) in w:
                if rev:
                    out[q].append((p, w[p, q]))
                else:
                    out[p].append((q, w[p, q]))
    return out


class Lab:
    """Distances of one bag: fw[i, j] from B[i] to Vs[j], bw[i, j] from Vs[j] to B[i]."""
    __slots__ = ('B', 'Vs', 'bi', 'vi', 'fw', 'bw')


def floyd(D):
    for k in range(len(D)):
        D = np.minimum(D, D[:, k, None] + D[k, None, :])
    return np.minimum(D, INF)


def labels(root, w, st, mode=''):
    """Lemma 1, bottom up. A leaf knows its arcs. An inner bag forms the graph Q on B = sep+(X) in X, and each vertex combines."""
    L = {}

    def rec(X):
        for Y in X.kids:
            rec(Y)
        lab = Lab()
        S = X.sep if mode == 'seponly' else X.splus
        lab.B = sorted(set(S) & X.V)
        lab.Vs = sorted(X.V)
        lab.bi = {a: i for i, a in enumerate(lab.B)}
        lab.vi = {v: i for i, v in enumerate(lab.Vs)}
        nb, nv = len(lab.B), len(lab.Vs)
        if not X.kids:
            out, rin = bag_out(X, w), bag_out(X, w, True)
            lab.fw = np.full((nb, nv), INF, dtype=np.int64)
            lab.bw = np.full((nb, nv), INF, dtype=np.int64)
            for i, a in enumerate(lab.B):
                d = dijkstra(X.V, out, {a: 0})
                e = dijkstra(X.V, rin, {a: 0})
                for v, j in lab.vi.items():
                    lab.fw[i, j] = d[v]
                    lab.bw[i, j] = e[v]
            L[X.id] = lab
            return
        # Q on B: arcs from the distances in each child
        Q = np.full((nb, nb), INF, dtype=np.int64)
        np.fill_diagonal(Q, 0)
        words = 0
        for Y in X.kids:
            ly = L[Y.id]
            sh = [a for a in lab.B if a in ly.bi]
            if not sh:
                continue
            ia = [lab.bi[a] for a in sh]
            ib = [ly.bi[a] for a in sh]
            iv = [ly.vi[a] for a in sh]
            Q[np.ix_(ia, ia)] = np.minimum(Q[np.ix_(ia, ia)], ly.fw[np.ix_(ib, iv)])
            words += len(sh) ** 2
        st['max.words_in_bag'] = max(st['max.words_in_bag'], words)
        st['max.B'] = max(st['max.B'], nb)
        st['n.words'] += words
        dQ = Q if mode == 'noq' else floyd(Q)
        fw = np.full((nb, nv), INF, dtype=np.int64)
        bw = np.full((nb, nv), INF, dtype=np.int64)
        for a, i in lab.bi.items():
            if a in lab.vi:
                fw[:, lab.vi[a]] = dQ[:, i]
                bw[:, lab.vi[a]] = dQ[i, :]
        for Y in X.kids:
            ly = L[Y.id]
            sh = [a for a in lab.B if a in ly.bi]
            if not sh:
                continue
            ia = [lab.bi[a] for a in sh]
            ib = [ly.bi[a] for a in sh]
            jv = [lab.vi[v] for v in ly.Vs]
            # from a in B: to b in B and then in the child to v
            f = (dQ[np.ix_(range(nb), ia)][:, :, None] + ly.fw[ib, :][None, :, :]).min(axis=1)
            fw[np.ix_(range(nb), jv)] = np.minimum(fw[np.ix_(range(nb), jv)], f)
            if mode == 'noqrev':
                g = ly.bw[ib, :].min(axis=0, keepdims=True) + dQ[ia, :].min(axis=0, keepdims=True).T
            else:
                g = (ly.bw[ib, :][None, :, :] + dQ[np.ix_(ia, range(nb))].T[:, :, None]).min(axis=1)
            bw[np.ix_(range(nb), jv)] = np.minimum(bw[np.ix_(range(nb), jv)], g)
        lab.fw, lab.bw = np.minimum(fw, INF), np.minimum(bw, INF)
        L[X.id] = lab

    rec(root)
    return L


def check_labels(bags, L, w, st):
    bad = 0
    for X in bags:
        lab = L[X.id]
        out, rin = bag_out(X, w), bag_out(X, w, True)
        for i, a in enumerate(lab.B):
            d = dijkstra(X.V, out, {a: 0})
            e = dijkstra(X.V, rin, {a: 0})
            st['chk.label'] += 2 * len(lab.Vs)
            for v, j in lab.vi.items():
                if lab.fw[i, j] != d[v] or lab.bw[i, j] != e[v]:
                    bad += 1
    return bad


def chains(root, V):
    """The chain of each vertex: from the root to the first bag where it is on the separator."""
    ch = {}
    for v in V:
        X, c = root, []
        while True:
            c.append(X)
            if v in X.sep or not X.kids:
                break
            K = [Y for Y in X.kids if v in Y.V]
            assert len(K) == 1
            X = K[0]
        ch[v] = c
    return ch


def query(ch, L, phi, mode=''):
    """Theorem 2: the two minima of the Virtual Source Lemma, with H_X = sep(X) and d_X in place of the approximate values."""
    A = {}
    for u, c in ch.items():
        if phi[u] >= INF:
            continue
        for X in c:
            lab = L[X.id]
            j = lab.vi[u]
            for h in X.sep:
                i = lab.bi[h]
                x = phi[u] + lab.bw[i, j]
                if x < A.get((X.id, h), INF):
                    A[X.id, h] = x
    out = {}
    for v, c in ch.items():
        best = INF
        use = c[-1:] if mode == 'deepest' else c[:1] if mode == 'rootonly' else c
        for X in use:
            lab = L[X.id]
            j = lab.vi[v]
            for h in X.sep:
                i = lab.bi[h]
                dist = lab.bw[i, j] if mode == 'swap' else lab.fw[i, j]
                x = A.get((X.id, h), INF) + dist
                if x < best:
                    best = x
        out[v] = min(int(best), INF)
    return out


def offsets(V, rng):
    k = rng.choice(['one', 'few', 'all', 'set'])
    top = rng.choice([1, 50, 10 ** 7])
    if k == 'one':
        phi = dict.fromkeys(V, INF)
        phi[rng.choice(sorted(V))] = 0
    elif k == 'few':
        phi = dict.fromkeys(V, INF)
        for v in rng.sample(sorted(V), min(3, len(V))):
            phi[v] = rng.randrange(top + 1)
    elif k == 'all':
        phi = {v: rng.randrange(top + 1) for v in V}
    else:
        phi = {v: (0 if rng.random() < 0.5 else INF) for v in V}
    return phi


def run_one(rng, st, big, mode=''):
    name, (V, E) = gm.sample(rng, big)
    if len(V) < 2 or not E:
        return None
    st['chk.planar'] += 1
    if not nx.check_planarity(nx.Graph(list(E)))[0]:
        st['FAIL.planar'] += 1
    root, bags = mm.build(set(V), list(E), rng, leaf=rng.choice([3, 4, 6, 10]), closure=rng.choice([False, True, 'two']))
    w = lengths(V, E, rng)
    L = labels(root, w, st, mode)
    st['runs'] += 1
    st['fam.' + name] += 1
    st['max.n'] = max(st['max.n'], len(V))
    st['n.bags'] += len(bags)
    bad = 0 if mode in ('deepest', 'rootonly', 'swap') else check_labels(bags, L, w, st)
    ch = chains(root, V)
    out = collections.defaultdict(list)
    for (a, b), c in w.items():
        out[a].append((b, c))
    wrong = 0
    for _ in range(3):
        phi = offsets(V, rng)
        try:
            got = query(ch, L, phi, mode)
        except KeyError:
            return bad, 1
        src = {v: x for v, x in phi.items() if x < INF}
        true = dijkstra(V, out, src)
        st['chk.query'] += len(V)
        wrong += sum(1 for v in V if got[v] != true[v])
    return bad, wrong


def lane(seed, secs, big):
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    while time.time() - t0 < secs:
        r = run_one(rng, st, big)
        if r is None:
            continue
        if r[0]:
            st['FAIL.label'] += r[0]
        if r[1]:
            st['FAIL.query'] += r[1]
    print(json.dumps(dict(sorted(st.items()))))


def controls(seed, secs):
    res = {}
    for mode in [''] + CTL:
        rng = random.Random(seed)
        st = collections.Counter()
        t0 = time.time()
        badl = badq = runs = 0
        while time.time() - t0 < secs:
            r = run_one(rng, st, False, mode)
            if r is None:
                continue
            runs += 1
            badl += bool(r[0])
            badq += bool(r[1])
        res[mode or 'clean'] = {'runs': runs, 'runs_wrong_label': badl, 'runs_wrong_query': badq}
    print(json.dumps(res))
    assert all(v['runs_wrong_label'] == 0 and v['runs_wrong_query'] == 0 for k, v in res.items() if k == 'clean')
    assert all(v['runs_wrong_label'] + v['runs_wrong_query'] > 0 for k, v in res.items() if k != 'clean')


if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == 'ctl':
        controls(int(a[1]), float(a[2]))
    else:
        lane(int(a[0]), float(a[1]), len(a) > 2)
