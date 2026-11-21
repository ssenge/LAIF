"""Check of the scan-first forest certificate with labels capped at k (classical simulation).

Scan vertices in an order where the next vertex is an unscanned vertex of largest label
c(w) = min(k, r(w)), ties broken at random. Scanning v assigns every edge vw with w unscanned and
r(w) < k to forest F_{r(w)+1} and increments r(w); edges vw with r(w) >= k are ignored. Only these
marked entries have to be found in the list of v.
Asserts, for each i <= k: F_i is a forest, and every edge of G outside F_1..F_{i-1} joins two
vertices connected in F_i (the hypothesis of the certificate lemma). Also reports the quantum cost
sum_v sqrt(deg(v) (t_v + 1)) against sqrt(2 m n k) + sqrt(2 m n), where t_v is the number of marked entries of v.
"""
import math
import random
import networkx as nx


def scan(G, k, rng):
    r = {v: 0 for v in G}
    scanned = set()
    F = [[] for _ in range(k)]
    cost = 0.0
    order = []
    while len(scanned) < len(G):
        best = max(min(k, r[w]) for w in G if w not in scanned)
        cand = [w for w in G if w not in scanned and min(k, r[w]) == best]
        v = rng.choice(cand)
        scanned.add(v)
        order.append(v)
        t = 0
        for w in G[v]:
            if w not in scanned and r[w] < k:
                F[r[w]].append((v, w))
                r[w] += 1
                t += 1
        cost += math.sqrt(G.degree(v) * (t + 1))
    return F, cost


def check(G, F, k):
    used = set()
    for i in range(k):
        T = nx.Graph()
        T.add_nodes_from(G)
        T.add_edges_from(F[i])
        assert nx.is_forest(T), "forest"
        for (a, b) in G.edges():
            e = frozenset((a, b))
            if e not in used:
                assert nx.has_path(T, a, b), ("maximality", i)
        used |= {frozenset(e) for e in F[i]}


def graphs(rng):
    for _ in range(60):
        n = rng.randint(5, 16)
        yield nx.gnp_random_graph(n, rng.choice([0.15, 0.3, 0.5, 0.8]), seed=rng.randrange(10**9))
    for _ in range(20):
        a, b = rng.randint(3, 8), rng.randint(3, 8)
        G = nx.disjoint_union(nx.complete_graph(a), nx.complete_graph(b))
        for i in range(rng.randint(0, min(a, b))):
            G.add_edge(i, a + i)
        yield G
    for _ in range(20):
        n = rng.randint(8, 16)
        G = nx.gnp_random_graph(n, 0.15, seed=rng.randrange(10**9))
        for h in range(rng.randint(1, 3)):
            for v in range(n):
                if v != h:
                    G.add_edge(h, v)
        yield G


def main():
    rng = random.Random(7)
    cnt = 0
    for G in graphs(rng):
        for k in (1, 2, 3, 5):
            for _ in range(3):
                F, _ = scan(G, k, rng)
                check(G, F, k)
                H = nx.Graph()
                H.add_nodes_from(G)
                for Fi in F:
                    H.add_edges_from(Fi)
                for s in G:
                    for t in G:
                        if s < t:
                            lg = nx.edge_connectivity(G, s, t) if nx.has_path(G, s, t) else 0
                            lh = nx.edge_connectivity(H, s, t) if nx.has_path(H, s, t) else 0
                            assert lh >= min(k, lg)
                cnt += 1
    print(f"{cnt} capped scans checked")
    for n, p in ((300, 0.5), (300, 0.1)):
        G = nx.gnp_random_graph(n, p, seed=1)
        m = G.number_of_edges()
        for k in (1, 4, 16):
            F, cost = scan(G, k, random.Random(k))
            print(f"n={n} m={m} k={k}: cost={cost:8.0f}  /(sqrt(2mnk)+sqrt(2mn))="
                  f"{cost / (math.sqrt(2*m*n*k) + math.sqrt(2*m*n)):.2f}")


if __name__ == "__main__":
    main()
