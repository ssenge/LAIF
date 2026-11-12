"""Tightness of the constants of the note, on explicit planar digraphs. Own code, no repo imports."""
import sys, collections, json
import networkx as nx


def reach(a, s, allow):
    seen = {s}
    st = [s]
    while st:
        u = st.pop()
        for v in a.get(u, ()):
            if v in allow and v not in seen:
                seen.add(v)
                st.append(v)
    return seen


def add(a, u, v):
    a.setdefault(u, set()).add(v)


def inst(W):
    """z -> c, c -> y, c -> n1, c -> n2, y -> n1, y -> n2. y carries 3W/4 - 1 leaves, n1, n2 carry b - 1 leaves with b = ceil(W/16) - 1. c carries the rest."""
    a = {}
    b = (W + 15) // 16 - 1
    x = 100
    for u, v in [('z', 'c'), ('c', 'y'), ('c', 'n1'), ('c', 'n2'), ('y', 'n1'), ('y', 'n2')]:
        add(a, u, v)
    for _ in range(3 * W // 4 - 1):
        add(a, 'y', x)
        x += 1
    for n_ in ('n1', 'n2'):
        for _ in range(b - 1):
            add(a, n_, x)
            x += 1
    V = set(a) | {v for vs in a.values() for v in vs}
    while len(V) < W:
        add(a, 'c', x)
        V.add(x)
        x += 1
    F = {'c': 'z', 'y': 'c', 'n1': 'c', 'n2': 'c'}
    G = nx.Graph()
    for u in a:
        for v in a[u]:
            G.add_edge(u, v)
    planar = nx.check_planarity(G)[0]
    Q = set(V)
    f = {v: len(reach(a, v, Q)) for v in Q}
    paths = {'z', 'c', 'n1', 'n2'}
    H = G.subgraph(Q - paths)
    big = max(len(c) for c in nx.connected_components(H))
    return dict(W=W, planar=planar, size=len(Q), side_ok=4 * big <= 3 * W, big=big, f_z=f['z'], f_c=f['c'], f_y=f['y'], y_frac=round(f['y'] / W, 4), f_n1=f['n1'], low_n1=16 * f['n1'] < W,
                high_y_at_7_8=8 * f['y'] > 7 * W, high_y_at_13_16=16 * f['y'] > 13 * W, y_reaches_c='c' in reach(a, 'y', Q))


for W in (32, 64, 160, 320, 1600, 16000):
    print(json.dumps(inst(W)))
print('constraints: a >= 3/4 + 2b; bad = 1 - b; a <= bad, so b <= 1/12. The note has b = 1/16, a = 7/8, bad = 15/16: a is exactly 3/4 + 2b, bad is exactly 1 - b, and a < bad leaves room.')
