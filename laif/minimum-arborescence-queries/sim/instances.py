"""Instance families for arb.py. Root is vertex 0. Each function returns an n x n int64 matrix."""
import numpy as np
from arb import INF


def _clean(W):
    np.fill_diagonal(W, INF)
    return W


def random_dense(n, seed=0, top=10**6):
    return _clean(np.random.default_rng(seed).integers(1, top, (n, n), dtype=np.int64))


def random_sparse(n, deg, seed=0, top=10**6):
    r = np.random.default_rng(seed)
    W = r.integers(1, top, (n, n), dtype=np.int64)
    W[r.random((n, n)) > deg / n] = INF
    W[0, 1:] = np.where(W[0, 1:] >= INF, top * 10, W[0, 1:])  # keeps an arborescence
    return _clean(W)


def chain(n):
    """One vertex absorbed at a time, n-2 contractions into one growing node, with lists running out."""
    W = np.arange(1, n + 1, dtype=np.int64)[:, None].repeat(n, axis=1)
    W[0, :] = 10 * n
    return _clean(W)


def blocks(n, b):
    """Blocks of size b contract first, then each is absorbed by the growing node."""
    W = np.empty((n, n), dtype=np.int64)
    bl = (np.arange(n) - 1) // b
    for u in range(1, n):
        W[u, :] = 1 + (bl[u] + 2) * 10
        W[u, bl == bl[u]] = 1 + (u % b)
    W[0, :] = 10 * (n + 5)
    return _clean(W)


def hierarchy(n):
    """Balanced merges: the weight of u->v grows with the level of their common dyadic block."""
    W = np.empty((n, n), dtype=np.int64)
    for u in range(n):
        for v in range(n):
            W[u, v] = 1 + int((u ^ v)).bit_length() * 1000 + (u % 7)
    W[0, :] = 10**7
    return _clean(W)


def bidirected(n, seed=0, top=10**6):
    """Symmetric weights, where the answer is the minimum spanning tree weight."""
    W = random_dense(n, seed, top)
    return _clean(np.minimum(W, W.T))


def hub(n, seed=0):
    """List-model stress: one vertex of in-degree n-1, a chain elsewhere, about 3n edges."""
    W = np.full((n, n), INF, dtype=np.int64)
    W[np.arange(1, n), 1] = np.arange(1, n)  # vertex 1 prefers earlier-absorbed sources
    for v in range(2, n):
        W[v, v - 1] = 1
        W[v - 1, v] = 1
        W[0, v] = 10 * n
    W[0, 1] = 10 * n
    return _clean(W)


def unreachable(n, seed=0):
    W = random_dense(n, seed)
    W[:, n - 1] = INF  # the last vertex has no entering edge
    return _clean(W)


FAMILIES = {
    "random": random_dense,
    "chain": chain,
    "blocks2": lambda n: blocks(n, 2),
    "blocks8": lambda n: blocks(n, 8),
    "blocks√n": lambda n: blocks(n, max(2, int(n ** 0.5))),
    "hierarchy": hierarchy,
    "bidirected": bidirected,
}
