"""Quantum monotone local search, simulated on small instances.

Extension trees (decision form, each node answers, makes one call or branches into an OR):
  * 3-Hitting Set: branch on the elements of an unhit set (base 3).
  * Feedback Vertex Set: the highest-degree branching of Iwata and Kobayashi (arXiv:1905.12233) with its
    reductions 1-5 and pruning rule; reduction 6 (matroid matching when D <= 3) is replaced by further
    branching, which keeps the tree an OR tree.
  * Cluster Vertex Deletion: branching on the three vertices of an induced P3 (base 3), the basic version.
For every budget k' and the t chosen as in Fomin, Gaspers, Lokshtanov, Saurabh, the samples Y of size t
form the search space of amplitude amplification, and Y is marked when the tree accepts (X = Y, k' - t).
Checks: the smallest accepted budget equals the optimum (brute force); at k' = OPT at least C(k', t) samples
are marked; the averaged success probability of amplitude amplification with m = ceil(1/sqrt p0)
rounds, p0 = C(k',t)/C(n,t), is at least 1/4 (closed form, and a state-vector run on some instances);
and with no solution nothing is marked."""
import itertools
import math
import random
import numpy as np
import networkx as nx

random.seed(11)


# ---------- extension trees ----------
def hs_tree(sets, k, cnt):
    cnt[0] += 1
    if any(len(s) == 0 for s in sets):
        return False
    if not sets:
        return k >= 0
    if k <= 0:
        return False
    e = min(sets, key=lambda s: (len(s), sorted(s)))
    for x in sorted(e):                               # OR over the element that hits e
        if hs_tree([s for s in sets if x not in s], k - 1, cnt):
            return True
    return False


def fvs_tree(G, F, k, cnt):
    """G: nx.MultiGraph, F: undeletable vertices (G[F] a forest). Iwata-Kobayashi branching."""
    cnt[0] += 1
    G = G.copy(); F = set(F)
    while True:                                       # reductions 1-5, in order
        if k < 0 or has_cycle(G.subgraph(F)):
            return False
        u = next((v for v in G if G.degree(v) <= 1), None)
        if u is not None:
            G.remove_node(u); F.discard(u); continue
        u = next((v for v in G if v not in F and has_cycle(G.subgraph(F | {v}))), None)
        if u is not None:
            G.remove_node(u); k -= 1; continue
        u = next((v for v in G if G.degree(v) == 2 and G.number_of_edges(v, v) == 0), None)
        if u is not None:
            a, b = [w for _, w in G.edges(u)]
            G.remove_node(u); G.add_edge(a, b); F.discard(u)
            continue
        e = next(((a, b) for a, b in G.edges() if G.number_of_edges(a, b) > 2), None)
        if e is not None:
            while G.number_of_edges(*e) > 2:
                G.remove_edge(*e)
            continue
        u = next((v for v in G if v not in F and any(G.number_of_edges(v, w) == 2 and G.degree(w) <= 3
                                                     for w in set(G.neighbors(v)) if w != v)), None)
        if u is not None:
            G.remove_node(u); k -= 1; continue
        break
    if G.number_of_nodes() == 0 or not has_cycle(G):
        return True
    free = [v for v in G if v not in F]
    if not free:
        return False
    D = max(G.degree(v) for v in free)
    if k * D - sum(G.degree(v) - 2 for v in F) < 0:   # pruning rule
        return False
    u = max(free, key=lambda v: (G.degree(v), str(v)))
    G1 = G.copy(); G1.remove_node(u)
    if fvs_tree(G1, F, k - 1, cnt):                    # OR: u deleted
        return True
    U = {w for w in G.neighbors(u) if w in F}          # OR: u kept, contracted with U into F
    G2 = G.copy(); new = ("c", u, cnt[0])
    G2.add_node(new)
    for a, b in G.edges():
        ia, ib = a in U or a == u, b in U or b == u
        if ia and ib:
            continue
        G2.add_edge(new if ia else a, new if ib else b)
    G2.remove_nodes_from(U | {u})
    return fvs_tree(G2, (F - U) | {new}, k, cnt)


def greedy(G, k):
    if not has_cycle(G):
        return k >= 0
    if k <= 0:
        return False
    u = max(G, key=lambda v: (G.degree(v), str(v))); G = G.copy(); G.remove_node(u)
    return greedy(G, k - 1)


def has_cycle(H):
    """Cyclomatic number > 0; counts loops and parallel edges."""
    return H.number_of_nodes() > 0 and H.number_of_edges() > H.number_of_nodes() - nx.number_connected_components(H)


def cvd_tree(G, k, cnt):
    cnt[0] += 1
    for b in G:
        N = list(G.neighbors(b))
        for a, c in itertools.combinations(N, 2):
            if not G.has_edge(a, c):                    # induced P3 a-b-c
                if k <= 0:
                    return False
                return any(cvd_tree(G.subgraph(set(G) - {x}).copy(), k - 1, cnt) for x in (a, b, c))
    return k >= 0


# ---------- problems as implicit set systems ----------
class HS:
    c = 3.0
    def __init__(self, n):
        self.U = list(range(n))
        self.sets = [frozenset(random.sample(self.U, random.choice([2, 3]))) for _ in range(random.randint(n, 2 * n))]
    def ext(self, X, k, cnt):
        return hs_tree([s for s in self.sets if not (s & set(X))], k, cnt)
    def ok(self, S):
        return all(s & set(S) for s in self.sets)


class FVS:
    c = 3.460
    def __init__(self, n):
        self.G = nx.gnp_random_graph(n, random.choice([0.3, 0.45, 0.6]), seed=random.randint(0, 10**9))
        self.U = list(self.G)
    def ext(self, X, k, cnt):
        H = nx.MultiGraph(self.G.subgraph(set(self.U) - set(X)))
        return fvs_tree(H, set(), k, cnt)
    def ok(self, S):
        return nx.is_forest(self.G.subgraph(set(self.U) - set(S)))


class CVD:
    c = 3.0
    def __init__(self, n):
        self.G = nx.gnp_random_graph(n, random.choice([0.3, 0.5]), seed=random.randint(0, 10**9))
        self.U = list(self.G)
    def ext(self, X, k, cnt):
        return cvd_tree(self.G.subgraph(set(self.U) - set(X)).copy(), k, cnt)
    def ok(self, S):
        H = self.G.subgraph(set(self.U) - set(S))
        return all(H.subgraph(C).number_of_edges() == len(C) * (len(C) - 1) // 2 for C in nx.connected_components(H))


def opt(P):
    for r in range(len(P.U) + 1):
        if any(P.ok(S) for S in itertools.combinations(P.U, r)):
            return r


def best_t(n, k, c):
    return min(range(k + 1), key=lambda t: math.comb(n, t) / math.comb(k, t) * c ** (k - t))


def amplify(marked, m):
    """State-vector amplitude amplification over the samples; mean success over j = 0..m-1 rounds."""
    N = len(marked); psi0 = np.full(N, 1 / math.sqrt(N)); s = 0.0
    psi = psi0.copy()
    for j in range(m):
        s += float(np.sum(psi[marked] ** 2))
        psi[marked] *= -1                               # oracle
        psi = 2 * psi0 * (psi0 @ psi) - psi             # reflection about the start state
    return s / m


if __name__ == "__main__":
    stats = {}
    for P_cls, trials, nmax in ((HS, 120, 10), (FVS, 120, 9), (CVD, 120, 9)):
        worst_succ, sv = 1.0, 0
        for trial in range(trials):
            n = random.randint(4, nmax)
            P = P_cls(n); g = opt(P)
            accepted = None
            for k in range(n + 1):                      # smallest budget accepted by quantum MLS
                found = False
                for kp in range(k + 1):
                    t = best_t(n, kp, P.c)
                    Ys = list(itertools.combinations(P.U, t))
                    marked = np.array([P.ext(Y, kp - t, [0]) for Y in Ys])
                    M, N = int(marked.sum()), len(Ys)
                    if kp < g:
                        assert M == 0
                        continue
                    if kp == g:
                        assert M >= math.comb(kp, t), (P_cls.__name__, n, kp, t, M)
                    p0 = math.comb(kp, t) / N
                    m = math.ceil(1 / math.sqrt(p0))
                    th = math.asin(math.sqrt(M / N))
                    succ = max(M / N, sum(math.sin((2 * j + 1) * th) ** 2 for j in range(m)) / m)
                    if N <= 3000 and sv < 40:
                        a = max(M / N, amplify(marked, m)); assert abs(a - succ) < 1e-9; sv += 1
                    assert succ >= 0.25, (P_cls.__name__, n, kp, t, M, N, succ)
                    worst_succ = min(worst_succ, succ); found = True
                if found:
                    accepted = k; break
            assert accepted == g, (P_cls.__name__, n, accepted, g)
        stats[P_cls.__name__] = (trials, worst_succ, sv)
    wrong = 0                                           # control: a greedy tree without the second branch fails
    for _ in range(100):
        P = FVS(random.randint(5, 9)); k = 0
        while not greedy(nx.MultiGraph(P.G), k):
            k += 1
        wrong += k != opt(P)
    assert wrong > 0
    print(f"control: greedy deletion of a highest-degree vertex misses the optimum on {wrong} of 100 graphs")
    for name, (tr, w, sv) in stats.items():
        print(f"{name}: {tr} random instances, smallest accepted budget = optimum; marked samples >= C(k,t); "
              f"min averaged success {w:.3f} >= 1/4; {sv} state-vector runs agree with the closed form")
