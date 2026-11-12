"""Checks of the combinatorics behind the quantum recognition of cluster graphs (disjoint unions of cliques).

For random graphs near cluster graphs (random clique sizes, then edges added, removed or 2-switched) it checks:
  Fact 1   G is a cluster graph  <=>  no induced P3  <=>  N[x] = N[z] for every edge xz.
  Fact 2   an edge xz and a vertex w with A(x,w) != A(z,w) give an induced P3 (built explicitly).
  Lemma 3  for every edge xz with N[x] != N[z], x or z has at least half of its neighbours with a different closed
           neighbourhood (the other end among them).
  Detection: the base procedure (x uniform, z a uniform neighbour, success if N[x] != N[z]) succeeds with probability
           at least 1/(2n) on every graph that is not a cluster graph.
"""
import itertools
import random

rng = random.Random(7)


def cluster_graph(n):
    sizes, left = [], n
    while left:
        s = min(left, rng.choice([1, 1, 2, 3, 4, 6, 9, 15, 25, 40]))
        sizes.append(s)
        left -= s
    rng.shuffle(sizes)
    adj = [set() for _ in range(n)]
    perm = list(range(n))
    rng.shuffle(perm)
    pos = 0
    for s in sizes:
        cl = perm[pos:pos + s]
        pos += s
        for a, b in itertools.combinations(cl, 2):
            adj[a].add(b)
            adj[b].add(a)
    return adj


def perturb(adj, n):
    for _ in range(rng.choice([1, 1, 1, 2, 3])):
        kind = rng.choice(["add", "remove", "switch"])
        if kind == "add":
            a, b = rng.sample(range(n), 2)
            adj[a].add(b); adj[b].add(a)
        elif kind == "remove":
            edges = [(a, b) for a in range(n) for b in adj[a] if a < b]
            if edges:
                a, b = rng.choice(edges)
                adj[a].discard(b); adj[b].discard(a)
        else:
            edges = [(a, b) for a in range(n) for b in adj[a] if a < b]
            if len(edges) >= 2:
                (a, b), (c, d) = rng.sample(edges, 2)
                if len({a, b, c, d}) == 4 and d not in adj[a] and b not in adj[c]:
                    adj[a].discard(b); adj[b].discard(a); adj[c].discard(d); adj[d].discard(c)
                    adj[a].add(d); adj[d].add(a); adj[c].add(b); adj[b].add(c)


def closed(adj, x):
    return adj[x] | {x}


def p3s(adj, n):
    return [(a, b, c) for b in range(n) for a in adj[b] for c in adj[b] if a < c and c not in adj[a]]


def is_cluster(adj, n):
    """Components are cliques."""
    seen = [False] * n
    for v in range(n):
        if not seen[v]:
            comp, stack = set(), [v]
            while stack:
                u = stack.pop()
                if u not in comp:
                    comp.add(u)
                    stack.extend(adj[u] - comp)
            for u in comp:
                seen[u] = True
                if adj[u] != comp - {u}:
                    return False
    return True


def check(adj, n):
    P = p3s(adj, n)
    cl = is_cluster(adj, n)
    edges_ok = all(closed(adj, x) == closed(adj, z) for x in range(n) for z in adj[x])
    assert cl == (not P) == edges_ok, "Fact 1"
    # Fact 2
    for x in range(n):
        for z in adj[x]:
            for w in range(n):
                if w not in (x, z) and ((w in adj[x]) != (w in adj[z])):
                    t = (z, x, w) if w in adj[x] else (x, z, w)
                    a, b, c = t
                    assert a in adj[b] and c in adj[b] and c not in adj[a] and len({a, b, c}) == 3, "Fact 2"
    # Lemma 3 and detection
    deg = [len(adj[v]) for v in range(n)]
    bad = [sum(closed(adj, z) != closed(adj, x) for z in adj[x]) for x in range(n)]
    for x in range(n):
        for z in adj[x]:
            if closed(adj, x) != closed(adj, z):
                assert 2 * bad[x] >= deg[x] or 2 * bad[z] >= deg[z], "good end"
    pE = sum(bad[x] / deg[x] for x in range(n) if deg[x]) / n
    assert bool(P) == (pE > 0)
    if P:
        assert pE >= 1 / (2 * n), ("detection", pE)
    return bool(P)


def main():
    bad = good = 0
    for trial in range(3000):
        n = rng.randint(3, 60)
        adj = cluster_graph(n)
        assert is_cluster(adj, n) and not p3s(adj, n)
        if rng.random() < 0.8:
            perturb(adj, n)
        if check(adj, n):
            bad += 1
        else:
            good += 1
    for trial in range(300):                      # dense random graphs
        n = rng.randint(3, 30)
        p = rng.random()
        adj = [set() for _ in range(n)]
        for a, b in itertools.combinations(range(n), 2):
            if rng.random() < p:
                adj[a].add(b); adj[b].add(a)
        bad += check(adj, n)
    print(f"near-cluster graphs: {good} cluster, {bad} non-cluster (incl. 300 G(n,p)); all checks passed")


if __name__ == "__main__":
    main()
