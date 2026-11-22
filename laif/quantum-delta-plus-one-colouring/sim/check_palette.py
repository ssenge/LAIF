"""Palette sparsification with quantum search: classical check of the combinatorial steps.

For random graphs with maximum degree Delta, every vertex samples a list of l = ceil(c ln n) colours (c = 2) from
[Delta + 1]. The script checks that
  * the conflict degrees t_v (neighbours u with L(u) and L(v) intersecting) and the candidate sets
    C_v = {u : L(u) and L(v) intersect} have the sizes used in the query count;
  * a proper colouring from the lists exists (found by a search on the conflict graph) and is proper on G;
  * the query counts sum_v (sqrt(N_v (t_v + 1)) + sqrt(N_v) ln n), with N_v = deg(v) or |C_v|, stay within
    2 n sqrt(Delta) l and 2 n sqrt(n/Delta) l^2.
"""
import math, random
import numpy as np

def random_graph(n, Delta, rng):
    adj = [set() for _ in range(n)]
    for _ in range(n * Delta):
        u, v = rng.randrange(n), rng.randrange(n)
        if u != v and len(adj[u]) < Delta and len(adj[v]) < Delta:
            adj[u].add(v); adj[v].add(u)
    return adj

def list_colour(adj_h, lists, rng, steps=400000):
    """Min-conflicts local search for a colouring from the lists on the conflict graph."""
    n = len(lists); L = [sorted(x) for x in lists]
    col = [rng.choice(L[v]) for v in range(n)]
    bad = {v for v in range(n) if any(col[u] == col[v] for u in adj_h[v])}
    for _ in range(steps):
        if not bad: return col
        v = rng.choice(tuple(bad))
        cnt = {c: sum(1 for u in adj_h[v] if col[u] == c) for c in L[v]}
        m = min(cnt.values()); col[v] = rng.choice([c for c in L[v] if cnt[c] == m])
        for w in [v] + list(adj_h[v]):
            if any(col[u] == col[w] for u in adj_h[w]): bad.add(w)
            else: bad.discard(w)
    return None

def random_graph_np(n, Delta, rng):
    # union of Delta random perfect matchings, so every degree is at most Delta
    adj = [set() for _ in range(n)]
    for _ in range(Delta):
        perm = list(range(n)); rng.shuffle(perm)
        for a in range(0, n - 1, 2):
            u, v = perm[a], perm[a + 1]
            adj[u].add(v); adj[v].add(u)
    return adj

rng = random.Random(11)
def cliques(n, Delta):
    # disjoint copies of K_{Delta+1}: a colouring from the lists needs every colour in every clique's lists
    adj = [set() for _ in range(n)]
    for start in range(0, n - Delta, Delta + 1):
        block = range(start, start + Delta + 1)
        for u in block:
            adj[u] = set(block) - {u}
    return adj

for n, Delta, cl, fam in [(3000, 200, 2.0, "matchings"), (4000, 600, 2.0, "matchings"), (4000, 199, 2.0, "cliques"), (4000, 63, 2.0, "cliques")]:
    adj = random_graph_np(n, Delta, rng) if fam == "matchings" else cliques(n, Delta)
    D = max(len(a) for a in adj)
    l = math.ceil(cl * math.log(n))
    M = np.zeros((n, D + 1), dtype=np.int16)
    lists = []
    for v in range(n):
        L = rng.sample(range(D + 1), min(l, D + 1)); lists.append(set(L)); M[v, L] = 1
    inter = (M.astype(np.int32) @ M.T.astype(np.int32)) > 0
    np.fill_diagonal(inter, False)
    C = inter.sum(axis=1)
    adj_h = [{u for u in adj[v] if inter[v, u]} for v in range(n)]
    t = [len(a) for a in adj_h]
    col = list_colour(adj_h, lists, rng)
    assert col is not None and all(c in lists[v] for v, c in enumerate(col))
    assert all(col[u] != col[v] for v in range(n) for u in adj[v])
    lg = math.log(n)
    qn = sum(math.sqrt(len(adj[v]) * (t[v] + 1)) + math.sqrt(len(adj[v])) * lg for v in range(n))
    qa = sum(math.sqrt(C[v] * (t[v] + 1)) + math.sqrt(C[v]) * lg for v in range(n))
    assert max(t) <= 4 * l * l * D / (D + 1) + 4 * l and max(C) <= 2 * n * l * l / (D + 1) + 4 * l
    assert qn <= 2 * n * math.sqrt(D) * l and qa <= 2 * n * math.sqrt(n / D) * l * l
    print(f"{fam}: n={n} Delta={D} l={l}: max t_v={max(t)} (l^2={l*l}), max |C_v|={max(C)} (n l^2/(Delta+1)={n*l*l/(D+1):.0f}), "
          f"proper list colouring found; neighbour cost {qn:.0f} (2 n sqrt(Delta) l = {2*n*math.sqrt(D)*l:.0f}), "
          f"adjacency cost {qa:.0f} (2 n sqrt(n/Delta) l^2 = {2*n*math.sqrt(n/D)*l*l:.0f})")
