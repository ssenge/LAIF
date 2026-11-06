# Checks the two lower-bound networks by Dijkstra's algorithm.
# Diameter network: M = 4, bits alpha = A[i], beta = B[j]. Claim: diameter 4(k+2)+2 if A, B
#   intersect, at most 4(k+2)+1 otherwise.
# Radius network: M = 5, bits alpha = 1 - A[i], beta = 1 - B[j], a leaf of weight 3 at each hub.
#   Claim: radius 5(k+2) if A, B intersect, at least 5(k+2)+1 otherwise.
# With networkx installed, also checks planarity, the hop-diameter and the two cut edges.
import heapq, itertools, random

HUBS = ["l", "r", "l'", "r'"]

def network(A, B, radius):
    k, M = len(A), 5 if radius else 4
    E = []
    for i in range(1, k + 1):
        al = 1 - A[i-1] if radius else A[i-1]
        be = 1 - B[i-1] if radius else B[i-1]
        E += [(f"a{i}", "l", i*M + al), (f"a{i}", "r", (k+1-i)*M + al),
              (f"b{i}", "l'", (k+1-i)*M + be), (f"b{i}", "r'", i*M + be)]
    E += [("l", "l'", M), ("r", "r'", M)]
    if radius:
        E += [(h, "q" + h, 3) for h in HUBS]
    return E

def eccentricities(E):
    adj = {}
    for u, v, w in E:
        adj.setdefault(u, []).append((v, w)); adj.setdefault(v, []).append((u, w))
    ecc = {}
    for s in adj:
        d = {s: 0}; pq = [(0, s)]
        while pq:
            du, u = heapq.heappop(pq)
            if du > d[u]: continue
            for v, w in adj[u]:
                if du + w < d.get(v, 1 << 60): d[v] = du + w; heapq.heappush(pq, (d[v], v))
        ecc[s] = max(d.values())
    return ecc

def check(A, B):
    k = len(A); inter = any(a and b for a, b in zip(A, B))
    diam = max(eccentricities(network(A, B, False)).values())
    assert diam == 4*(k+2) + 2 if inter else diam <= 4*(k+2) + 1, (A, B, diam)
    ecc = eccentricities(network(A, B, True)); rad = min(ecc.values())
    assert rad == 5*(k+2) if inter else rad >= 5*(k+2) + 1, (A, B, rad)
    for i in range(1, k + 1):
        assert ecc[f"a{i}"] == ecc[f"b{i}"] == 5*(k+2) + (1 - A[i-1]) + (1 - B[i-1])
    assert all(ecc[h] >= 5*(k+2) + 3 for h in HUBS)

def structure(k):
    import networkx as nx
    for radius, hop in [(False, 3), (True, 5)]:
        G = nx.Graph([(u, v) for u, v, _ in network([0]*k, [0]*k, radius)])
        alice = {u for u in G if "'" not in u and u[0] != "b"}
        cut = [(u, v) for u, v in G.edges if (u in alice) != (v in alice)]
        assert nx.check_planarity(G)[0] and nx.diameter(G) == hop and len(cut) == 2, (k, radius)

for k in range(1, 7):
    for A in itertools.product([0, 1], repeat=k):
        for B in itertools.product([0, 1], repeat=k):
            check(A, B)
random.seed(1)
for _ in range(200):
    k = random.randint(7, 40)
    check([random.randint(0, 1) for _ in range(k)], [random.randint(0, 1) for _ in range(k)])
try:
    for k in range(2, 41):
        structure(k)
    print("ok, with planarity, hop-diameter and cut checks")
except ImportError:
    print("ok (networkx not installed: planarity, hop-diameter and cut not checked)")
