"""Edmonds' contraction (path-growing form) for minimum arborescences, with a query charge per step.

Each step finds the cheapest reduced in-arc of the current head supernode X over the |X| (n - |X|)
pairs from outside X. Grover minimum finding over that rectangle costs sqrt(|X| (n - |X|)); the
script sums these charges and compares them with n^{3/2} and n^2. Asserts: the arborescence weight
equals the networkx optimum on every instance.
"""
import math, random, sys
import networkx as nx

def edmonds_path(W, r=0, order=None):
    n = len(W)
    parent = list(range(n)); members = {v: [v] for v in range(n)}
    off = [0.0] * n
    def find(v):
        while parent[v] != v: parent[v] = parent[parent[v]]; v = parent[v]
        return v
    done = {r}; total = 0.0; cost = 0.0; steps = 0; contractions = []
    order = order or list(range(n))
    for start in order:
        if find(start) in done: continue
        path = [find(start)]
        while True:
            X = path[-1]; M = members[X]; inX = set(M)
            best = None
            for v in M:
                for u in range(n):
                    if u in inX or u == v: continue
                    c = W[u][v] - off[v]
                    if best is None or c < best[0]: best = (c, u, v)
            cost += math.sqrt(len(M) * (n - len(M))); steps += 1
            c, u, v = best; total += c
            for x in M: off[x] += c
            Y = find(u)
            if Y in done:
                for Z in path: done.add(Z)
                break
            if Y in path:
                i = path.index(Y); cyc = path[i:]; del path[i:]
                root = cyc[0]
                for Z in cyc[1:]:
                    parent[Z] = root; members[root] += members.pop(Z)
                contractions.append(len(members[root]))
                path.append(root)
            else:
                path.append(Y)
    return total, cost, steps, contractions

def nx_opt(W, r=0):
    n = len(W); G = nx.DiGraph()
    for u in range(n):
        for v in range(n):
            if u != v and v != r: G.add_edge(u, v, weight=W[u][v])
    T = nx.minimum_spanning_arborescence(G, preserve_attrs=True)
    return sum(d["weight"] for _, _, d in T.edges(data=True))

def random_family(n, rng):
    return [[rng.random() for _ in range(n)] for _ in range(n)]

def chain_family(n, rng):
    """Vertex k's cheapest in-arc comes from the block {1..k-1}, and the block's from k: nested cycles."""
    BIG = 10.0 * n
    W = [[BIG] * n for _ in range(n)]
    for k in range(1, n):
        for j in range(1, n):
            if j < k: W[j][k] = 1.0                     # forward arcs, cheap
            elif j > k: W[j][k] = 2.0 + j / n + 1e-3 * rng.random()   # backward arcs, increasing in j
    return W

if __name__ == "__main__":
    rng = random.Random(5)
    for name, fam in (("random", random_family), ("chain", chain_family)):
        for n in (40, 80, 160):
            W = fam(n, rng)
            tot, cost, steps, con = edmonds_path(W)
            opt = nx_opt(W)
            assert abs(tot - opt) < 1e-6 * max(1, abs(opt)), (name, n, tot, opt)
            print(f"{name:7s} n={n:4d} steps={steps:4d} contractions={len(con):4d} max|X|={max(con, default=1):4d} "
                  f"cost/n^1.5={cost / n ** 1.5:6.2f} cost/n^2={cost / n ** 2:5.3f}")
