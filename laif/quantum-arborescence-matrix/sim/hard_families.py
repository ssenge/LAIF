"""Hard families for the grouped extraction of grouped_cost.py: chains of blocks.

Blocks of size b are directed cycles of cheap arcs (they contract first); block i is cheapest
reached from block i+1 by backward arcs of weight 2 + i/n, forward arcs between blocks cost 1, so
the supernode grows block by block. With even b the size-1 group of the first vertex never merges.
Nested: blocks are themselves chains of sub-blocks. Asserts the optimum against networkx (n <= 128).
"""
import math, random
from grouped_cost import grouped
from contraction_cost import edmonds_path, nx_opt

def block_chain(n, b, rng, nested=False):
    BIG = 50.0 * n
    W = [[BIG] * n for _ in range(n)]
    V = list(range(1, n)); rng.shuffle(V)
    blocks = [V[i:i + b] for i in range(0, len(V), b)]
    rank = {}
    for i, B in enumerate(blocks):
        for v in B: rank[v] = i
        for j, v in enumerate(B):            # cheap directed cycle inside the block
            W[B[j - 1]][v] = 0.5 if not nested else 0.3 + 0.1 * (j % 2)
    for u in V:
        for v in V:
            if u == v or rank[u] == rank[v]: continue
            if rank[u] < rank[v]: W[u][v] = 1.0 + 1e-3 * rng.random()
            else: W[u][v] = 2.0 + rank[u] / n + 1e-3 * rng.random()
    return W

if __name__ == "__main__":
    rng = random.Random(13)
    for b in (2, 3, 4, 8):
        for n in (65, 129, 257):
            W = block_chain(n, b, rng)
            tot, cost = grouped(W)
            if n <= 129:
                opt = nx_opt(W); assert abs(tot - opt) < 1e-6 * max(1, opt), (b, n)
            _, plain, _, _ = edmonds_path(W)
            L = 1 + math.log2(n)
            print(f"blocks b={b} n={n:4d} grouped/(n^1.5 L^2)={cost / (n ** 1.5 * L * L):6.3f} plain/n^1.5={plain / n ** 1.5:6.2f}")
