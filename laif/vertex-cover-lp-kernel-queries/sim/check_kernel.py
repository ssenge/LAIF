"""Brute-force checks of the classical steps behind the O(n^{3/2} log^2 n + k^2) vertex cover algorithm.

For random graphs with at most 10 vertices: the bipartite double cover H, a maximum matching of H,
the alternating-path cover C of H (size |M|), the half-integral point x_v = (|C ∩ {v_L, v_R}|)/2,
its optimality for the vertex cover LP (scipy), and the kernel equivalence
tau(G) <= k  <=>  tau(G[V_half]) <= k - |V_1|, with |V_half| <= 2(k - |V_1|) on yes-instances.
Also checks the search-cost bound sum_u sqrt(n (t_u + 1)) <= sqrt(2) n^{3/2} of the alternating search.
"""
import itertools, math, random
import networkx as nx
from scipy.optimize import linprog

def tau(n, E, V=None):
    V = list(range(n)) if V is None else list(V)
    Es = [e for e in E if e[0] in V and e[1] in V]
    for s in range(len(V) + 1):
        for S in itertools.combinations(V, s):
            S = set(S)
            if all(a in S or b in S for a, b in Es):
                return s
    return len(V)

def lp_value(n, E):
    if not E:
        return 0.0
    A = [[-(v in e) for v in range(n)] for e in E]
    return linprog([1] * n, A_ub=A, b_ub=[-1] * len(E), bounds=[(0, 1)] * n, method="highs").fun

def half_integral(n, E):
    H = nx.Graph(); L = [("L", v) for v in range(n)]; R = [("R", v) for v in range(n)]
    H.add_nodes_from(L + R)
    for a, b in E:
        H.add_edge(("L", a), ("R", b)); H.add_edge(("L", b), ("R", a))
    M = nx.bipartite.hopcroft_karp_matching(H, top_nodes=L)
    # alternating search from unmatched left vertices; t_u = right vertices first reached from u
    Z = {u for u in L if u not in M}; queue = list(Z); seenR = set(); cost = 0.0
    while queue:
        u = queue.pop()
        new = [w for w in H[u] if w not in seenR and M.get(u) != w]
        cost += math.sqrt(n * (len(new) + 1))
        for w in new:
            seenR.add(w); Z.add(w)
            m = M.get(w)
            assert m is not None  # else an augmenting path exists
            if m not in Z:
                Z.add(m); queue.append(m)
    C = {u for u in L if u not in Z} | {w for w in R if w in Z}
    assert len(C) == len(M) // 2 and all(a in C or b in C for a, b in H.edges())
    assert cost <= math.sqrt(2) * n ** 1.5 + 1e-9
    return [((("L", v) in C) + (("R", v) in C)) / 2 for v in range(n)]

random.seed(1)
trials = 0
for _ in range(400):
    n = random.randint(1, 10); p = random.choice([0.15, 0.3, 0.5, 0.8])
    E = [e for e in itertools.combinations(range(n), 2) if random.random() < p]
    x = half_integral(n, E)
    assert all(x[a] + x[b] >= 1 for a, b in E)
    assert abs(sum(x) - lp_value(n, E)) < 1e-7
    V1 = {v for v in range(n) if x[v] == 1}; Vh = {v for v in range(n) if x[v] == 0.5}
    t = tau(n, E)
    for k in range(n + 1):
        kk = k - len(V1)
        yes_kernel = kk >= 0 and len(Vh) <= 2 * kk and tau(n, E, Vh) <= kk
        assert (t <= k) == yes_kernel, (n, E, k)
    trials += 1
print(f"double cover LP, alternating cover and kernel equivalence checked on {trials} random graphs, n <= 10")
