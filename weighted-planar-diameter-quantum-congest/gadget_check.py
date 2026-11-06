# Check of the planar diameter gadget (Abboud, Cohen-Addad, Klein, Thm 9): Dijkstra on random inputs.
import heapq, itertools, random

def diameter(A, B, M=4):
    n = len(A); adj = {}
    def e(u, v, w): adj.setdefault(u, []).append((v, w)); adj.setdefault(v, []).append((u, w))
    for i in range(1, n + 1):
        e(f"a{i}", "l", i * M + A[i-1]); e(f"a{i}", "r", (n + 1 - i) * M + A[i-1])
        e(f"b{i}", "l'", (n + 1 - i) * M + B[i-1]); e(f"b{i}", "r'", i * M + B[i-1])
    e("l", "l'", M); e("r", "r'", M)
    best = 0
    for s in adj:
        d = {s: 0}; h = [(0, s)]
        while h:
            du, u = heapq.heappop(h)
            if du > d[u]: continue
            for v, w in adj[u]:
                if du + w < d.get(v, 1 << 60): d[v] = du + w; heapq.heappush(h, (d[v], v))
        best = max(best, max(d.values()))
    return best

for n in range(1, 7):
    for A in itertools.product([0, 1], repeat=n):
        for B in itertools.product([0, 1], repeat=n):
            inter = any(a and b for a, b in zip(A, B))
            D = diameter(A, B)
            assert D == ((n + 2) * 4 + 2 if inter else D) and (inter or D <= (n + 2) * 4 + 1), (A, B, D)
for _ in range(200):
    n = random.randint(7, 40); A = [random.randint(0, 1) for _ in range(n)]; B = [random.randint(0, 1) for _ in range(n)]
    inter = any(a and b for a, b in zip(A, B)); D = diameter(A, B)
    assert (D == (n + 2) * 4 + 2) if inter else (D <= (n + 2) * 4 + 1)
print("ok")
