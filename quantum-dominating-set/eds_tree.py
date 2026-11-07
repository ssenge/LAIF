"""Decision version of the edge domination algorithms of van Rooij and Bodlaender (Algorithmica 2012; tech. report
UU-CS-2007-051), in the form of their Algorithm 2: the clique rule as one tail call with budget k + 1, branching on
an undecided vertex of degree at least three as an OR of two children, and minimal vertex covers of the remaining
paths and cycles as further OR children. A leaf turns the vertex cover C into the smallest edge dominating set
whose endpoints include C, by an edge cover. Algorithm 4 of the paper refines the branching on small subgraphs and
keeps these three kinds of steps. Compared with brute force on random graphs."""
import itertools
import random
import networkx as nx

random.seed(5)


def candidate(G, C):
    """Size of the smallest edge dominating set whose endpoints include the vertex cover C."""
    H = G.subgraph(C)
    iso = [v for v in C if H.degree(v) == 0]
    rest = H.subgraph([v for v in C if H.degree(v) > 0])
    return len(iso) + rest.number_of_nodes() - len(nx.max_weight_matching(rest, maxcardinality=True))


def decide(G, C, I, U, k, cnt):
    cnt[0] += 1
    if not U:
        return candidate(G, C) <= k
    GU = G.subgraph(U)
    for comp in nx.connected_components(GU):                       # clique rule: one tail call
        n = len(comp)
        if GU.subgraph(comp).number_of_edges() == n * (n - 1) // 2:
            G2, v = G.copy(), ("new", cnt[0])
            G2.add_edges_from((v, u) for u in comp)
            return decide(G2, C | comp | {v}, I, U - comp, k + 1, cnt)
    v = max(U, key=GU.degree)
    if GU.degree(v) >= 3:                                          # OR: v in I, or v in C
        Nv = set(GU.neighbors(v))
        return (decide(G, C | Nv, I | {v}, U - Nv - {v}, k, cnt)
                or decide(G, C | {v}, I, U - {v}, k, cnt))
    for r in range(len(U) + 1):                                    # paths and cycles: minimal vertex covers
        for J in itertools.combinations(sorted(U, key=str), r):
            J = set(J)
            if all(not GU.has_edge(a, b) for a, b in itertools.combinations(J, 2)) and \
               all(any(GU.has_edge(u, j) for j in J) for u in U - J):
                cnt[0] += 1
                if candidate(G, C | (U - J)) <= k:
                    return True
    return False


def brute(G):
    E = list(G.edges())
    for r in range(len(E) + 1):
        for D in itertools.combinations(E, r):
            ends = {x for e in D for x in e}
            if all(a in ends or b in ends for a, b in E):
                return r


if __name__ == "__main__":
    for trial in range(300):
        n = random.randint(3, 10)
        G = nx.gnp_random_graph(n, random.choice([0.25, 0.4, 0.6]), seed=random.randint(0, 10**9))
        g, k, cnt = brute(G), 0, [0]
        while not decide(G, set(), set(), set(G.nodes()), k, cnt):
            k += 1
        assert k == g, (n, list(G.edges()), k, g)
    print("300 random graphs, n = 3..10: smallest accepted budget = edge domination number in every case")
