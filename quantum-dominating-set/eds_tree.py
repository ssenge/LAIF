"""Decision version of the edge domination algorithms of van Rooij and Bodlaender (Algorithmica 2012; tech. report
UU-CS-2007-051), in the form of their Algorithm 3: the clique rule as one tail call with budget k + 1, branching on
an undecided vertex of degree at least three or on a cycle as an OR of two children, and two children on paths with at
least three vertices. A leaf turns the vertex cover C into the smallest edge dominating set whose endpoints include C,
by a matching. Algorithm 4 of the paper refines the branching on small subgraphs and keeps these kinds of steps.
Compared with brute force on random graphs."""
import itertools
import random
import networkx as nx

random.seed(13)


def candidate(G, C):
    """Size of the smallest edge dominating set whose endpoints include the vertex cover C."""
    H = G.subgraph(C)
    rest = H.subgraph([v for v in C if H.degree(v) > 0])
    return len(C) - rest.number_of_nodes() + rest.number_of_nodes() - len(nx.max_weight_matching(rest, maxcardinality=True))


def decide(G, C, I, U, k, fresh):
    if not U:
        return candidate(G, C) <= k
    GU = G.subgraph(U)
    comps = [set(c) for c in nx.connected_components(GU)]
    for H in comps:
        if GU.subgraph(H).number_of_edges() == len(H) * (len(H) - 1) // 2:     # clique rule, one call
            v = ("new", next(fresh))
            G2 = G.copy()
            G2.add_edges_from((v, u) for u in H)
            return decide(G2, C | H | {v}, I, U - H, k + 1, fresh)

    def two(a, b):
        return decide(G, *a, k, fresh) or decide(G, *b, k, fresh)

    v = max(sorted(U, key=str), key=GU.degree)
    cycle = next((H for H in comps if all(GU.degree(x) == 2 for x in H)), None)
    if GU.degree(v) >= 3 or cycle:
        if GU.degree(v) < 3:
            v = sorted(cycle, key=str)[0]
        Nv = set(GU.neighbors(v))
        return two((C | Nv, I | {v}, U - Nv - {v}), (C | {v}, I, U - {v}))
    for H in comps:                                                             # only paths are left
        if len(H) >= 4:
            p = [sorted((x for x in H if GU.degree(x) == 1), key=str)[0]]
            while len(p) < 4:
                p.append(next(y for y in GU.neighbors(p[-1]) if y not in p))
            v1, v2, v3, v4 = p
            return two((C | {v2, v4}, I | {v1, v3}, U - {v1, v2, v3, v4}), (C | {v3}, I, U - {v3}))
    H = next(H for H in comps if len(H) == 3)
    m = next(x for x in H if GU.degree(x) == 2)
    Nm = set(GU.neighbors(m))
    return two((C | Nm, I | {m}, U - H), (C | {m}, I | Nm, U - H))


def brute(G):
    E = list(G.edges())
    for r in range(len(E) + 1):
        for D in itertools.combinations(E, r):
            ends = {x for e in D for x in e}
            if all(a in ends or b in ends for a, b in E):
                return r


if __name__ == "__main__":
    done = 0
    while done < 300:
        n = random.randint(3, 10)
        G = nx.gnp_random_graph(n, random.choice([0.15, 0.25, 0.35, 0.5, 0.7]), seed=random.randint(0, 10**9))
        if G.number_of_edges() > 18:
            continue
        g, k = brute(G), 0
        while not decide(G, set(), set(), set(G.nodes()), k, itertools.count()):
            k += 1
        assert k == g, (n, list(G.edges()), k, g)
        done += 1
    print("300 random graphs, n = 3..10, at most 18 edges: smallest accepted budget = edge domination number in every case")
