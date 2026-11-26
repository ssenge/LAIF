"""Grouped extraction with the merge rule of the proof (smaller into larger, chunk kills, carries).

Rule at a merge of supernodes A (larger) and B (smaller): the groups of B are dissolved and its
columns form one chunk C. Every group of A with size <= |C| is merged into C; then groups whose
sizes lie in the same power-of-two class are merged until all classes differ. Each surviving
group of A keeps its rows and batches.

Asserts: (i) the arborescence weight equals the networkx optimum (n <= 129); (ii) every vertex lies
in at most 2 log2 n + 2 groups over the run, so the group sizes sum to at most n (2 log2 n + 2);
(iii) every row is deleted from batches at most L log2 n times in total; (iv) every group hands
out at most 2 (deletions in it) + 1 rows; (v) at most 2n - 1 picks.
Prints cost / (n^{1.5} L^2) with L = log2 n + 1, the cost of a batch of b rows from s columns
being sqrt(n s b) L.
"""
import math, random
from contraction_cost import nx_opt, random_family, chain_family, edmonds_path
from hard_families import block_chain
from grouped_cost import hier_family, sym_random

class G:
    def __init__(s, cols, W, off, n, stats):
        s.cols = list(cols); s.delta = 0.0; s.growth = 0; s.consumed = 0; s.handed = 0; s.deleted = 0
        s.key = [min((W[u][v] - off[v] for v in s.cols if v != u), default=math.inf) for u in range(n)]
        s.order = sorted(range(n), key=lambda u: s.key[u]); s.pos = 0; s.batch = []; s.next_b = 1; s.exhausted = False; s.last_head = None
        stats["size_sum"] += len(s.cols); stats["groups"].append(s)
        for v in s.cols: stats["memb"][v] += 1

def run(W, r=0, check=False):
    n = len(W); off = [0.0] * n; L = math.log2(n) + 1
    stats = {"size_sum": 0, "groups": [], "cost": 0.0, "memb": [0] * n, "rowdel": [0] * n, "picks": 0}
    parent = list(range(n)); members = {v: [v] for v in range(n)}
    groups = {v: [G([v], W, off, n, stats)] for v in range(n)}
    def find(v):
        while parent[v] != v: parent[v] = parent[parent[v]]; v = parent[v]
        return v
    def head(g, X):
        while True:
            while g.batch and find(g.batch[0]) == X:
                g.deleted += 1; stats["rowdel"][g.batch.pop(0)] += 1
            if g.batch:
                if g.batch[0] != g.last_head:        # value of a new head: minimum finding over the columns
                    stats["cost"] += math.sqrt(len(g.cols)) * L; g.last_head = g.batch[0]
                return g.batch[0]
            if g.exhausted: return None
            b = g.next_b; got = []
            while g.pos < n and len(got) < b:
                u = g.order[g.pos]; g.pos += 1
                if find(u) != X and g.key[u] < math.inf: got.append(u)
            stats["cost"] += math.sqrt(n * len(g.cols) * b) * L   # charged also when the search comes back empty
            if not got: g.exhausted = True; return None
            g.handed += len(got); g.batch = got; g.next_b = 2 * b
    def pick(X):
        best = None
        for g in groups[X]:
            u = head(g, X)
            if u is not None and (best is None or g.key[u] - g.delta < best[0]): best = (g.key[u] - g.delta, u, g)
        if best is None: return None
        c, u, g = best; g.consumed += 1; stats["picks"] += 1
        stats["cost"] += math.sqrt(len(g.cols)) * L + 1          # column of the chosen row, and one entry
        if check:                                                # brute force: least reduced in-arc of X
            bf = min((W[a][v] - off[v] for v in members[X] for a in range(n) if find(a) != X), default=math.inf)
            assert abs(bf - c) < 1e-9 * max(1.0, abs(c)), ("pick", bf, c)
        for h in groups[X]: h.delta += c
        for x in members[X]: off[x] += c
        return c, u
    def absorb(A, B):                      # |A| >= |B|
        parent[B] = A; chunk = members.pop(B); members[A] += chunk; groups.pop(B)
        keep, cols = [], list(chunk)
        for g in groups[A]:
            if len(g.cols) <= len(chunk): cols += g.cols
            else: g.growth += len(chunk); keep.append(g)
        new = [G(cols, W, off, n, stats)]
        allg = keep + new
        while True:
            cls = {}
            for g in allg: cls.setdefault(int(math.log2(len(g.cols))), []).append(g)
            dup = [L_ for L_ in cls.values() if len(L_) >= 2]
            if not dup: break
            a, b = dup[0][0], dup[0][1]; allg.remove(a); allg.remove(b)
            allg.append(G(a.cols + b.cols, W, off, n, stats))
        groups[A] = allg
        return A
    def merge(parts):
        parts = sorted(parts, key=lambda Z: -len(members[Z]))
        A = parts[0]
        for B in parts[1:]: A = absorb(A, B)
        return A
    done = {r}; total = 0.0
    for start in range(n):
        if find(start) in done: continue
        path = [find(start)]
        while True:
            X = path[-1]; p = pick(X)
            if p is None: run.last = stats; return math.inf, stats["cost"]   # no arc enters X: no arborescence
            c, u = p; total += c; Y = find(u)
            if Y in done: done.update(path); break
            if Y in path:
                i = path.index(Y); cyc = path[i:]; del path[i:]; path.append(merge(cyc))
            else: path.append(Y)
    lg = math.log2(n)
    for g in stats["groups"]:
        assert g.handed <= 2 * g.deleted + 1, ("handed", g.handed, g.deleted)
    assert max(stats["memb"]) <= 2 * lg + 2, ("membership", max(stats["memb"]))
    assert max(stats["rowdel"]) <= L * lg, ("row deletions", max(stats["rowdel"]))
    assert stats["picks"] <= 2 * n - 2
    stats["maxmemb"] = max(stats["memb"]); stats["maxdel"] = max(stats["rowdel"])
    run.last = stats
    return total, stats["cost"]

if __name__ == "__main__":
    rng = random.Random(17)
    fams = (("random", random_family), ("chain", chain_family), ("hier", hier_family), ("symrand", sym_random),
            ("blocks2", lambda n, r: block_chain(n, 2, r)), ("blocks8", lambda n, r: block_chain(n, 8, r)),
            ("ties", lambda n, r: [[float(r.randrange(4)) for _ in range(n)] for _ in range(n)]))
    for name, fam in fams:
        for n in (33, 65, 129, 257):
            W = fam(n, rng)
            if name == "hier":
                for v in range(n): W[0][v] = 50.0 * n
            tot, cost = run(W, check=n <= 65)
            if n <= 129:
                opt = nx_opt(W); assert abs(tot - opt) < 1e-6 * max(1, abs(opt)), (name, n, tot, opt)
            L = math.log2(n) + 1
            st = run.last
            print(f"{name:8s} n={n:4d} cost/(n^1.5 L^2)={cost / (n ** 1.5 * L * L):6.3f} max groups per vertex={st['maxmemb']:3d} "
                  f"max deletions per row={st['maxdel']:3d} picks/n={st['picks'] / n:4.2f}", flush=True)
    # missing arcs (infinite entries): sparse digraphs against networkx, and an unreachable vertex
    import networkx as nx
    for trial in range(40):
        n = rng.choice((9, 17, 33)); p = rng.choice((0.15, 0.3, 0.6))
        W = [[rng.random() if rng.random() < p else math.inf for _ in range(n)] for _ in range(n)]
        if trial % 4 == 0:
            v = rng.randrange(1, n)
            for u in range(n): W[u][v] = math.inf
        tot, _ = run(W, check=True)
        D = nx.DiGraph([(u, v, {"weight": W[u][v]}) for u in range(n) for v in range(1, n) if u != v and W[u][v] < math.inf])
        D.add_nodes_from(range(n))
        reach = len(nx.descendants(D, 0)) == n - 1
        if not reach: assert tot == math.inf, ("missed infeasible", trial)
        else:
            opt = sum(d["weight"] for _, _, d in nx.minimum_spanning_arborescence(D).edges(data=True))
            assert abs(tot - opt) < 1e-9 * max(1, opt), ("sparse", trial, tot, opt)
    print("all invariants hold")
