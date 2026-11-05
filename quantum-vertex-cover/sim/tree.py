"""Branching for Vertex Cover with budget k, as an explicit search tree, and the operators of the quantum walk on that tree.

The rule here is plain: remove isolated vertices, take the neighbour of a degree-1 vertex, and otherwise branch on a vertex v
of largest degree, into v in the cover or N(v) in the cover. On maximum degree at most 2 the graph is a union of paths and
cycles and could be solved directly; it is branched on here, so that the tree stays one rule. This is a small stand-in used
to test the walk, not the branching of the best classical bound."""
import random
import numpy as np


def reduce_graph(adj, k):
    """Applies the degree rules in a fixed order. Returns (adj, k), with k < 0 if the budget is spent."""
    adj = {v: set(n) for v, n in adj.items()}
    changed = True
    while changed:
        changed = False
        for v in sorted(adj):
            if v not in adj:
                continue
            if not adj[v]:
                del adj[v]
                changed = True
            elif len(adj[v]) == 1:
                u = next(iter(adj[v]))
                adj = remove(adj, [u])
                k -= 1
                changed = True
    return adj, k


def remove(adj, vs):
    vs = set(vs)
    return {v: n - vs for v, n in adj.items() if v not in vs}


def children(adj, k):
    """The two subproblems of a reduced graph with an edge."""
    v = max(sorted(adj), key=lambda u: len(adj[u]))
    N = sorted(adj[v])
    return [(remove(adj, [v]), k - 1), (remove(adj, N), k - len(N))]


class TooLarge(Exception):
    """The tree has more nodes than the limit of the test."""


class Tree:
    """Nodes in depth-first order, with parent, children and the marked flag. Infeasible nodes are leaves."""

    def __init__(self, adj, k, limit=20000):
        self.limit = limit
        self.parent, self.kids, self.marked, self.depth, self.budget = [], [], [], [], []
        self.build(adj, k, None, 0)
        self.T = len(self.parent)
        self.n = max(self.depth) + 1

    def build(self, adj, k, parent, depth):
        i = len(self.parent)
        if i >= self.limit:
            raise TooLarge
        self.parent.append(parent)
        self.kids.append([])
        self.depth.append(depth)
        self.marked.append(False)
        if parent is not None:
            self.kids[parent].append(i)
        adj, k = reduce_graph(adj, k)
        self.budget.append(k)
        if k < 0:
            return
        if not adj:
            self.marked[i] = True
            return
        if k == 0 or sum(len(n) for n in adj.values())/2 > k*max(len(n) for n in adj.values()):
            return
        for a, b in children(adj, k):
            self.build(a, b, i, depth + 1)

    def has_marked(self):
        return any(self.marked)


def diffusion(t, x, root_weight):
    """The projector part of D_x: |psi_x> is the normalised sum of |x> and its children, with weight on the children at the
    root. A marked vertex has D_x = I."""
    v = np.zeros(t.T, complex)
    if x == 0:
        v[0] = 1
        for y in t.kids[x]:
            v[y] = root_weight
    else:
        v[x] = 1
        for y in t.kids[x]:
            v[y] = 1
    return v/np.linalg.norm(v)


def reflections(t):
    """R_A over the vertices at even depth, and R_B over those at odd depth, with the root's term |r><r| in R_B."""
    RA, RB = np.eye(t.T, dtype=complex), np.eye(t.T, dtype=complex)
    alpha = np.sqrt(t.n)
    for x in range(t.T):
        if t.marked[x]:
            continue
        v = diffusion(t, x, alpha)
        if t.depth[x] % 2 == 0:
            RA -= 2*np.outer(v, v.conj())
        else:
            RB -= 2*np.outer(v, v.conj())
    return RA, RB


def random_regular(n, d, rng):
    """A simple d-regular graph: a circulant graph, then random double edge swaps."""
    assert n*d % 2 == 0 and d < n
    edges = {tuple(sorted((v, (v + j) % n))) for v in range(n) for j in range(1, d//2 + 1)}
    if d % 2:
        edges |= {(v, v + n//2) for v in range(n//2)}
    edges = list(edges)
    have = set(edges)
    for _ in range(20*len(edges)):
        i, j = rng.randrange(len(edges)), rng.randrange(len(edges))
        (a, b), (c, e) = edges[i], edges[j]
        if len({a, b, c, e}) < 4:
            continue
        p, q = tuple(sorted((a, c))), tuple(sorted((b, e)))
        if p in have or q in have:
            continue
        have -= {edges[i], edges[j]}
        have |= {p, q}
        edges[i], edges[j] = p, q
    adj = {v: set() for v in range(n)}
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    return adj


def minimum_cover(adj):
    k = 0
    while not Tree(adj, k).has_marked():
        k += 1
    return k
