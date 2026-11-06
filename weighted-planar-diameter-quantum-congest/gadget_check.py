# Checks the two lower-bound networks by Dijkstra's algorithm.
# Diameter network: M = 4, bits alpha = A[i], beta = B[j]. Claim: diameter 4(k+2)+2 if A, B
#   intersect, at most 4(k+2)+1 otherwise.
# Radius network: M = 5, bits alpha = 1 - A[i], beta = 1 - B[j], a leaf of weight 3 at each hub.
#   Claim: radius 5(k+2) if A, B intersect, at least 5(k+2)+1 otherwise.
# Padding: a path of t >= 0 extra nodes with weight-0 edges at hub l, and optionally one more node
#   (a twin of p_t for t >= 1; for t = 0 a node z with w(z,l) = 0, w(z,r) = (k+1)M+2), leaves the
#   diameter and the radius unchanged and gives hop-diameter t + 3 and max(5, t + 4).
# With networkx installed, also checks planarity, the hop-diameter and the two cut edges.
import heapq, itertools, random

HUBS = ["l", "r", "l'", "r'"]

def network(A, B, radius, t=0, extra=False):
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
    E += [("l" if s == 1 else f"p{s-1}", f"p{s}", 0) for s in range(1, t + 1)]
    if extra and t >= 1:
        E += [("l" if t == 1 else f"p{t-1}", "pz", 0)]
    elif extra:
        E += [("l", "pz", 0), ("r", "pz", (k + 1) * M + 2)]
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

def check(A, B, t=0, extra=False):
    k = len(A); inter = any(a and b for a, b in zip(A, B))
    diam = max(eccentricities(network(A, B, False, t, extra)).values())
    assert diam == 4*(k+2) + 2 if inter else diam <= 4*(k+2) + 1, (A, B, diam)
    ecc = eccentricities(network(A, B, True, t, extra)); rad = min(ecc.values())
    assert rad == 5*(k+2) + min((1 - a) + (1 - b) for a, b in zip(A, B)), (A, B, rad)
    for i in range(1, k + 1):
        assert ecc[f"a{i}"] == ecc[f"b{i}"] == 5*(k+2) + (1 - A[i-1]) + (1 - B[i-1])
    assert all(ecc[h] >= 5*(k+2) + 3 for h in HUBS)

def structure(k, t=0, extra=False):
    import networkx as nx
    for radius, hop in [(False, t + 3), (True, max(5, t + 4))]:
        G = nx.Graph([(u, v) for u, v, _ in network([0]*k, [0]*k, radius, t, extra)])
        alice = {u for u in G if "'" not in u and u[0] != "b"}
        cut = [(u, v) for u, v in G.edges if (u in alice) != (v in alice)]
        assert nx.check_planarity(G)[0] and nx.diameter(G) == hop and len(cut) == 2, (k, radius)

for k in range(1, 7):
    for A in itertools.product([0, 1], repeat=k):
        for B in itertools.product([0, 1], repeat=k):
            check(A, B)
for k in range(1, 5):
    for t in range(0, 8):
        for A in itertools.product([0, 1], repeat=k):
            for B in itertools.product([0, 1], repeat=k):
                check(A, B, t)
                check(A, B, t, True)
random.seed(1)
for _ in range(200):
    k = random.randint(7, 40)
    check([random.randint(0, 1) for _ in range(k)], [random.randint(0, 1) for _ in range(k)])
try:
    for k in range(1, 41):
        structure(k)
    for k in range(1, 6):
        for t in range(0, 8):
            structure(k, t)
            structure(k, t, True)
    print("ok, with planarity, hop-diameter and cut checks")
except ImportError:
    print("ok (networkx not installed: planarity, hop-diameter and cut not checked)")
