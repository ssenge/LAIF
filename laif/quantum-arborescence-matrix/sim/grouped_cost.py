"""Edmonds' contraction with grouped lazy extraction: a query-cost model for minimum arborescences.

Each supernode X keeps its columns in groups (sizes powers of two, merged like a binomial heap when
supernodes merge). Inside a group G with column set C, the key of row u is
key_G(u) = min_{v in C} (W[u][v] - off_G[v]) with offsets frozen when G was formed; later offset
increases are uniform on X, so the order of rows by key never changes. G hands out its rows in key
order, skipping rows inside X, in batches of doubling size; a batch of b rows costs
sqrt(n * |C| * b) (threshold search plus Grover enumeration over rows, with an inner OR over |C|).
The pick of X is the least current head over its groups. The script sums the charges and asserts
that the arborescence weight equals the networkx optimum.
"""
import math, random, sys
from contraction_cost import edmonds_path, nx_opt, random_family, chain_family

class Group:
    def __init__(self, cols, W, off, n):
        self.cols = list(cols); self.delta = 0.0
        self.key = [min(W[u][v] - off[v] for v in self.cols if v != u) if any(v != u for v in self.cols) else math.inf
                    for u in range(n)]
        self.order = sorted(range(n), key=lambda u: self.key[u])
        self.pos = 0; self.batch = []; self.next_b = 1

def grouped(W, r=0):
    n = len(W); off = [0.0] * n
    parent = list(range(n)); members = {v: [v] for v in range(n)}
    groups = {v: [Group([v], W, off, n)] for v in range(n)}
    cost = [0.0]
    def find(v):
        while parent[v] != v: parent[v] = parent[parent[v]]; v = parent[v]
        return v
    def head(G, X):
        inX = lambda u: find(u) == X
        while True:
            while G.batch and inX(G.batch[0]): G.batch.pop(0)
            if G.batch: return G.batch[0]
            b = G.next_b; got = []
            while G.pos < n and len(got) < b:
                u = G.order[G.pos]; G.pos += 1
                if not inX(u) and G.key[u] < math.inf: got.append(u)
            if not got: return None
            cost[0] += math.sqrt(n * len(G.cols) * b) * (1 + math.log2(n))
            G.batch = got; G.next_b = 2 * b
    def pick(X):
        best = None
        for G in groups[X]:
            u = head(G, X)
            if u is None: continue
            val = G.key[u] - G.delta
            if best is None or val < best[0]: best = (val, u, G)
        c, u, G = best
        for H in groups[X]: H.delta += c
        for x in members[X]: off[x] += c
        return c, u
    def merge(parts):
        root = parts[0]
        for Z in parts[1:]:
            parent[Z] = root; members[root] += members.pop(Z); groups[root] += groups.pop(Z)
        by = {}
        for G in groups[root]: by.setdefault(len(G.cols), []).append(G)
        changed = True
        while changed:
            changed = False
            for s in sorted(by):
                if len(by[s]) >= 2:
                    A, B = by[s].pop(), by[s].pop()
                    by.setdefault(2 * s, []).append(Group(A.cols + B.cols, W, off, n)); changed = True
                    break
        groups[root] = [G for L in by.values() for G in L]
        return root
    done = {r}; total = 0.0
    for start in range(n):
        if find(start) in done: continue
        path = [find(start)]
        while True:
            X = path[-1]; c, u = pick(X); total += c; Y = find(u)
            if Y in done:
                done.update(path); break
            if Y in path:
                i = path.index(Y); cyc = path[i:]; del path[i:]; path.append(merge(cyc))
            else:
                path.append(Y)
    return total, cost[0]

def hier_family(n, rng):
    """Symmetric weights by the highest differing bit, with noise: merges form a balanced tree."""
    return [[(1 + (u ^ v).bit_length()) + 0.01 * rng.random() if u != v else 0.0 for v in range(n)] for u in range(n)]

def sym_random(n, rng):
    A = [[0.0] * n for _ in range(n)]
    for u in range(n):
        for v in range(u + 1, n): A[u][v] = A[v][u] = rng.random()
    return A

if __name__ == "__main__":
    rng = random.Random(9)
    for name, fam in (("random", random_family), ("chain", chain_family), ("hier", hier_family), ("symrand", sym_random)):
        for n in (32, 64, 128, 256):
            W = fam(n, rng)
            if name == "hier":
                for v in range(n): W[0][v] = 50.0 * n   # root far away
            tot, cost = grouped(W)
            if n <= 128:
                opt = nx_opt(W); assert abs(tot - opt) < 1e-6 * max(1, abs(opt)), (name, n, tot, opt)
            _, plain, _, _ = edmonds_path(W)
            L = 1 + math.log2(n)
            print(f"{name:8s} n={n:4d} grouped/(n^1.5 log^2 n)={cost / (n ** 1.5 * L * L):6.3f} "
                  f"grouped/n^2={cost / n ** 2:6.2f} plain/n^1.5={plain / n ** 1.5:6.2f}")
