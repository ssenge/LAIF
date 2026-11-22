"""Enumerate types for the rank-2 reduction: N F-bases and N H-bases (pairs of resources from different classes),
every resource used, classes coarsest (every two classes joined by a basis of F or H). Vertices and colours are
introduced in order of first appearance; F and H are generated as sorted multisets of edges. Duplicates up to
isomorphism remain, which costs time but not completeness."""
import itertools, sys


def gen(N, kmax=4):
    """Yields (edges, colours); edges[:N] = F, edges[N:] = H."""

    def endpoints(col, k):
        """Choices for one endpoint: an existing vertex, or a new vertex with an existing or the next colour."""
        for x in range(len(col)): yield x, col, k
        for c in range(min(k + 1, kmax)): yield len(col), col + [c], max(k, c + 1)

    def rec(edges, col, k):
        if len(edges) == 2 * N:
            pairs = {frozenset((col[u], col[v])) for u, v in edges}
            if len(pairs) == k * (k - 1) // 2: yield tuple(edges), tuple(col)
            return
        for u, c1, k1 in endpoints(col, k):
            for v, c2, k2 in endpoints(c1, k1):
                if v == u or c2[u] == c2[v]: continue
                e = (min(u, v), max(u, v)); i = len(edges)
                if i % N and e < edges[-1]: continue                 # sorted within F and within H
                yield from rec(edges + [e], c2, k2)
    yield from rec([], [], 0)


if __name__ == "__main__":
    N = int(sys.argv[1]); T = list(gen(N))
    print("raw types", len(T), "by #vertices", {m: sum(1 for e, c in T if len(c) == m) for m in range(2, 4 * N + 1)})
