"""Checks for Theorem 2 (Distortion).

The state graph of the polynomial-space algorithm of [5, Section 4] for a connected graph G, a distortion bound d and
r segments of d + 1 positions: positions are filled in color order (color, then segment); a state is (t, A, f, H) with
the first t positions of the color order processed, A the placed vertices with their segments f, and H the last vertex
placed in each segment with its position; a step leaves position t + 1 empty or places a vertex there [5, Definitions
4.5 to 4.7], with the guessed first vertex v_i and position p_i of every segment.
1. A path from the empty state to a final state exists for some r and guesses iff G has a pushing embedding of
   distortion at most d [5, Lemmas 4.8, 4.9]; compared with brute force over vertex orders (a pushing embedding is
   fixed by its order, and its distortion is the longest edge) on random connected graphs.
2. The count of the top-level search space [5, Lemma 2.5]: at most 2N * 5^(n-1) triples (A, f, fbar) with fbar a bucket
   extension of the partial bucket function (A, f) with values in 1..N, by brute force on random connected graphs.
3. The algorithm of Theorem 2: a search over states S with |A| = floor(n/2), together with a final state whose
   segments extend those of S, and the halving recursion of [5, Lemma 4.10] on both sides, gives the same answer.
"""
import itertools, random
from functools import lru_cache

def bfs(n, adj):
    D = [[None] * n for _ in range(n)]
    for s in range(n):
        D[s][s] = 0; q = [s]
        for x in q:
            for y in adj[x]:
                if D[s][y] is None:
                    D[s][y] = D[s][x] + 1; q.append(y)
    return D

def brute(n, E, D):
    best = None
    for order in itertools.permutations(range(n)):
        pos = {order[0]: 0}
        for a, b in zip(order, order[1:]):
            pos[b] = pos[a] + D[a][b]
        dist = max(abs(pos[u] - pos[v]) for u, v in E)
        best = dist if best is None else min(best, dist)
    return best

def make(n, adj, E, D, d, r, guess):
    P = r * (d + 1)
    seg = lambda q: (q - 1) // (d + 1) + 1
    col = lambda q: (q - 1) % (d + 1) + 1
    CO = sorted(range(1, P + 1), key=lambda q: (col(q), seg(q)))
    idx = {q: t + 1 for t, q in enumerate(CO)}
    vs, ps = {i: guess[i - 1][0] for i in range(1, r + 1)}, {i: guess[i - 1][1] for i in range(1, r + 1)}

    @lru_cache(maxsize=None)
    def partial(A, f):                       # [5, Definition 2.1] with values in 1..r
        fd = dict(zip(A, f)); rest = [v for v in range(n) if v not in fd]
        for vals in itertools.product(range(1, r + 1), repeat=len(rest)):
            g = dict(fd); g.update(zip(rest, vals))
            if all(abs(g[u] - g[v]) <= 1 for u, v in E) and \
               all(not ((u in fd) != (v in fd)) or (g[u] >= g[v] if u in fd else g[v] >= g[u]) for u, v in E):
                return True
        return False

    def step(S, v):
        """Successor of S = (t, A, f, H) at position CO[t], empty (v None) or with vertex v; None if not allowed."""
        t, A, f, H = S
        q = CO[t]; i = seg(q)
        fd = dict(zip(A, f)); Hd = dict(H)
        if v is None:
            if any(ps[j] == q for j in vs):  # a guessed first position must be filled
                return None
            return (t + 1, A, f, H)
        if v in fd:
            return None
        if any(vs[j] == v and ps[j] != q for j in vs) or (ps[i] == q and vs[i] != v):
            return None
        if col(q) < col(ps[i]):              # v_i is the first vertex of segment i
            return None
        if any(u in fd and fd[u] < i for u in adj[v]):
            return None                      # successor of a partial bucket function
        if i in Hd and D[v][Hd[i][0]] != q - Hd[i][1]:
            return None                      # pushing inside a segment
        fd[v] = i; Hd[i] = (v, q)
        A2 = tuple(sorted(fd)); f2 = tuple(fd[x] for x in A2)
        if not partial(A2, f2):
            return None
        return (t + 1, A2, f2, tuple(sorted(Hd.items())))

    def final(S):
        t, A, f, H = S; Hd = dict(H)
        if t != P or len(A) != n or set(Hd) != set(range(1, r + 1)):
            return False
        return all(D[Hd[i][0]][vs[i + 1]] == ps[i + 1] - Hd[i][1] for i in range(1, r))

    return P, CO, step, final, partial, seg

def dfs_answer(n, adj, E, D, d, r, guess):
    P, CO, step, final, _, _ = make(n, adj, E, D, d, r, guess)
    seen = set()
    def go(S):
        if S in seen:
            return False
        seen.add(S)
        if S[0] == P:
            return final(S)
        return any(go(T) for T in (step(S, v) for v in [None] + list(range(n))) if T is not None)
    return go((0, (), (), ()))

def halving_answer(n, adj, E, D, d, r, guess):
    """Top-level search over middle states with |A| = floor(n/2) and final states, then halving on both sides."""
    P, CO, step, final, partial, seg = make(n, adj, E, D, d, r, guess)
    def direct(S, T):                        # |A_T \\ A_S| <= 1: the vertex goes in at one guessed index
        t0, A0, f0, H0 = S; t1, A1, f1, H1 = T
        new = [v for v in A1 if v not in A0]
        if len(new) > 1 or t1 < t0:
            return False
        for k in ([None] if not new else range(t0, t1)):
            cur = S; ok = True
            for t in range(t0, t1):
                cur = step(cur, new[0] if new and t == k else None)
                if cur is None:
                    ok = False; break
            if ok and cur == T:
                return True
        return False
    def mids(S, T, size):                    # all candidate states between S and T with |A| = size
        t0, A0, f0, H0 = S; t1, A1, f1, H1 = T
        fT = dict(zip(A1, f1)); rest = [v for v in A1 if v not in A0]
        for C in itertools.combinations(rest, size - len(A0)):
            A = tuple(sorted(set(A0) | set(C))); f = tuple(fT[x] for x in A)
            segs = sorted(set(f))
            for t in range(t0, t1 + 1):
                Pos = CO[:t]
                choices = [[(i, (w, q)) for w in A if fT[w] == i for q in Pos if seg(q) == i] for i in segs]
                for Hc in itertools.product(*choices):
                    yield (t, A, f, tuple(sorted(Hc)))
    def path(S, T):
        m = len(T[1]) - len(S[1])
        if m <= 1:
            return direct(S, T)
        return any(path(S, M) and path(M, T) for M in mids(S, T, len(S[1]) + m // 2))
    S0 = (0, (), (), ())
    for fbar in itertools.product(range(1, r + 1), repeat=n):
        if not partial(tuple(range(n)), fbar):
            continue
        choices = [[(i, (w, q)) for w in range(n) if fbar[w] == i for q in CO if seg(q) == i] for i in range(1, r + 1)]
        for Hc in itertools.product(*choices):
            F = (P, tuple(range(n)), fbar, tuple(sorted(Hc)))
            if not final(F):
                continue
            if any(path(S0, M) and path(M, F) for M in mids(S0, F, n // 2)):
                return True
    return False

def decide(n, adj, E, D, d, answer):
    for r in range(1, n + 1):
        P = r * (d + 1)
        for vs in itertools.permutations(range(n), r):
            for ps in itertools.product(*[range((i - 1) * (d + 1) + 1, i * (d + 1) + 1) for i in range(1, r + 1)]):
                if ps[0] != 1:               # the embedding starts at position 1 (shift)
                    continue
                if answer(n, adj, E, D, d, r, list(zip(vs, ps))):
                    return True
    return False

def triples(n, E, N):
    """Brute-force count of (A, f, fbar): fbar: V -> 1..N with |fbar(u) - fbar(v)| <= 1 on edges, A a set with fbar(u) >=
    fbar(v) for every edge uv with u in A and v not in A [5, Definition 2.1]; f = fbar on A."""
    seen = set()
    for fb in itertools.product(range(1, N + 1), repeat=n):
        if any(abs(fb[u] - fb[v]) > 1 for u, v in E):
            continue
        for mask in range(1 << n):
            inA = lambda x: mask >> x & 1
            if all(not (inA(u) != inA(v)) or (fb[u] >= fb[v] if inA(u) else fb[v] >= fb[u]) for u, v in E):
                seen.add((mask, tuple(fb), tuple(fb[x] if inA(x) else 0 for x in range(n))))
    return len(seen)

random.seed(2)
cnt = cnt2 = 0
for _ in range(60):
    n = random.randint(2, 5)
    while True:
        E = [(u, v) for u, v in itertools.combinations(range(n), 2) if random.random() < random.choice((0.4, 0.6, 0.9))]
        adj = [set() for _ in range(n)]
        for u, v in E:
            adj[u].add(v); adj[v].add(u)
        D = bfs(n, adj)
        if all(x is not None for row in D for x in row) and E:
            break
    best = brute(n, E, D)
    for d in range(1, best + 2):
        a = decide(n, adj, E, D, d, dfs_answer)
        assert a == (d >= best), (n, E, d, best, a)
        if n <= 4:
            b = decide(n, adj, E, D, d, halving_answer)
            assert b == a, (n, E, d, a, b)
            cnt2 += 1
    cnt += 1
cnt3 = 0
for _ in range(40):
    n = random.randint(1, 5); N = random.randint(1, 4)
    while True:
        E = [(u, v) for u, v in itertools.combinations(range(n), 2) if random.random() < 0.5]
        adj = [set() for _ in range(n)]
        for u, v in E:
            adj[u].add(v); adj[v].add(u)
        if all(x is not None for row in bfs(n, adj) for x in row):
            break
    c = triples(n, E, N)
    assert c <= 2 * N * 5 ** (n - 1), (n, E, N, c)
    cnt3 += 1
print(f"Lemma 2.5 count <= 2N 5^(n-1) on {cnt3} random connected graphs (n <= 5, N <= 4)")
print(f"state graph agrees with brute force on {cnt} random connected graphs (n <= 5, all d up to opt + 1); "
      f"search plus halving agrees on {cnt2} (graph, d) pairs with n <= 4")
print("all checks passed")
