"""The three-round adaptive learner (k random settings in round 1) on random bipartite d-regular graphs, at the combinatorial level.

Round j <= k: X on a random set R_j (each vertex with probability p = 1/(4d)), Z elsewhere; every clean
vertex of R_j (no neighbour in R_j) has its neighbourhood recovered, the others are detected as not clean.
Then stage 1 learns the unknown vertices of one colour class of the largest known component, stage 2 the
unknown vertices of the other side. The learner succeeds when every edge is known after stage 2.
Also checks the two events of the proof: the overlap graph of S on each side is connected (Lemma C) and
every vertex has a vertex of S on its side within distance 2 (Lemma D).
"""
import sys
import numpy as np
from stages import bip_regular, components

def overlap_connected(adj, S, side):
    """Is the graph on S ∩ side, with x ~ y when N(x) ∩ N(y) is nonempty, connected?"""
    Ss = [v for v in S if side(v)]
    if not Ss:
        return False
    inS = set(Ss); seen = {Ss[0]}; stack = [Ss[0]]
    while stack:
        v = stack.pop()
        for b in adj[v]:
            for w in adj[b]:
                if w in inS and w not in seen:
                    seen.add(w); stack.append(w)
    return len(seen) == len(Ss)

def covered(adj, S):
    inS = set(S)
    return all(any(w in inS for b in adj[a] for w in adj[b]) for a in range(len(adj)))

def learn(adj, d, k, rng):
    n = len(adj); m = n // 2; known = [False] * n; S = []
    for _ in range(k):
        R = set(v for v in range(n) if rng.random() < 1.0 / (4 * d))
        for v in R:
            if not known[v] and not (adj[v] & R):
                known[v] = True; S.append(v)
    events = (overlap_connected(adj, S, lambda v: v < m), overlap_connected(adj, S, lambda v: v >= m), covered(adj, S))
    for _ in range(2):
        comp, col, c = components(adj, known)
        sizes = np.bincount([x for x in comp if x >= 0], minlength=c)
        g = int(np.argmax(sizes))
        unk = [[v for v in range(n) if comp[v] == g and col[v] == f and not known[v]] for f in (0, 1)]
        W = unk[0] if unk[0] else unk[1]          # any colour class with unknown vertices
        assert all(not (adj[v] & set(W)) for v in W)  # a colour class of a component is independent
        for v in W:
            known[v] = True
    ok = all(known[v] or all(known[u] for u in adj[v]) for v in range(n))
    return ok, events

if __name__ == "__main__":
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
    trials = 10
    for m, d in [(1000, 8), (4000, 9), (10000, 10)]:
        graphs = [bip_regular(m, d, rng) for _ in range(trials)]
        for k in [1, 2, 4, 8]:
            res = [learn(g, d, k, rng) for g in graphs]
            succ = sum(r[0] for r in res); ev = [sum(r[1][i] for r in res) for i in range(3)]
            print(f"n={2*m} d={d} p=1/(4d) k={k}: success {succ}/{trials}, S_A connected {ev[0]}, S_B connected {ev[1]}, covered {ev[2]}")
            for ok, (ca, cb, cov) in res:      # the proof's events imply success
                assert ok or not (ca and cb and cov)
