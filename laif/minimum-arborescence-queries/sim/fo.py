"""Fischer-Oshman (DISC 2019) meta-algorithm for directed MST, sequential simulation.

Written from Section 4 and 7 of the DISC paper only. Works at the level of super-vertices.
Each iteration: for every active component A_i, compute dist inside A_i to its cycle (SSSP on reversed
edges), beta_i = min over edges (u,v) entering A_i of w(u,v) + dist(v), contract U_i = {x: dist(x) <= beta_i},
reweight edges entering U_i by dist(head) - beta_i, and add the minimizing edge to H.

The SSSP is run at the physical level in the order of Dijkstra, charged with the set partition of
DHHM Theorem 18 (one TopK per set, K = |P|, N = in-degree sum of P). `hook` receives every read batch.
"""
import heapq
import math
import numpy as np

INF = np.int64(1) << 60


def scan_red(vals, types, K, rng):
    """Red edges of a read-in-random-order TopK tree. vals: finite values, types: source ids.

    An item is red iff it changes the list: new minimum for its type and within the K best types so far.
    Items that are not prefix minima of their type are black whatever the list holds, so filter them first.
    """
    n = len(vals)
    if n == 0:
        return 0
    order = rng.permutation(n)
    v, t = vals[order], types[order]
    best = {}
    red = 0
    h = []  # max-heap of (-value, type) with lazy deletion
    for x, ty in zip(v.tolist(), t.tolist()):
        cur = best.get(ty)
        if cur is not None and cur <= x:
            continue
        if cur is None and len(best) >= K:
            while h and best.get(h[0][1]) != -h[0][0]:
                heapq.heappop(h)
            if h and x >= -h[0][0]:
                continue
            w, ty2 = heapq.heappop(h)
            del best[ty2]
        best[ty] = x
        heapq.heappush(h, (-x, ty))
        red += 1
    return red


class FO:
    def __init__(self, W, root=0, seed=0):
        self.W = W
        self.n = W.shape[0]
        self.root = root
        self.rng = np.random.default_rng(seed)
        self.T = 0.0        # reads along the path of the tree
        self.G = 0.0        # red edges along the path
        self.cost = 0.0     # sum of sqrt(K N) over TopK calls, and sqrt(N) over min findings
        self.iters = 0
        self.builds = 0
        self.iter_log = []

    def charge_min(self, vals):
        n = len(vals)
        if n == 0:
            return
        self.T += n
        self.G += scan_red(vals, np.zeros(n, dtype=np.int64), 1, self.rng)
        self.cost += math.sqrt(n)

    def solve(self):
        n, root, W = self.n, self.root, self.W
        w = W.copy()
        finite = W < INF
        self.deg = finite.sum(axis=0)
        sid = np.arange(n)                      # super-vertex of each physical vertex
        members = {v: [v] for v in range(n)}
        H = {}
        next_id = n
        total = 0
        # first step of Edmonds: each vertex takes its cheapest entering edge
        for v in range(n):
            if v == root:
                continue
            col = w[:, v]
            idx = np.flatnonzero(col < INF)
            self.charge_min(col[idx])
            if len(idx) == 0:
                return None
            u = int(idx[np.argmin(col[idx])])
            c = int(col[u])
            total += c
            w[idx, v] -= c
            H[v] = (u, v)
        levels = []
        while True:
            comps = self._components(H, sid, members)
            if not comps:
                break
            self.iters += 1
            recs = []
            # all components use the weights at the start of the iteration; updates touch only heads in U_i
            neww = w.copy()
            t0 = self.T
            for (cycle, supers) in comps:
                phys = np.array(sorted(x for S in supers for x in members[S]))
                inA = np.zeros(n, dtype=bool)
                inA[phys] = True
                dist, nxt = self._internal_sssp(w, sid, members, cycle, supers, phys, inA)
                # beta: one minimum finding over the edges entering A
                sub = w[:, phys].copy()
                sub[inA, :] = INF
                hd = np.array([dist[sid[x]] for x in phys], dtype=float)
                self.charge_min(sub[sub < INF].astype(float))
                best = None
                us, cols = np.nonzero(sub < INF)
                if len(us):
                    vals = sub[us, cols] + hd[cols]
                    i = int(np.argmin(vals))
                    if np.isfinite(vals[i]):
                        best = (int(vals[i]), int(us[i]), int(phys[cols[i]]))
                if best is None:
                    return None
                beta, u, v = best
                total += beta
                U = [S for S in supers if dist[S] <= beta]
                Uphys = np.array(sorted(x for S in U for x in members[S]))
                inU = np.zeros(n, dtype=bool)
                inU[Uphys] = True
                for y in Uphys:
                    d = int(dist[sid[y]])
                    m = (w[:, y] < INF) & ~inU
                    neww[m, y] = w[m, y] + d - beta
                recs.append(dict(new=next_id, U=U, H={S: H[S] for S in U}, nxt={S: nxt[S] for S in U if S in nxt},
                                 e=(u, v), Uphys=Uphys))
                next_id += 1
            w = neww
            # apply the contractions
            for r in recs:
                mem = []
                for S in r["U"]:
                    mem += members.pop(S)
                    H.pop(S)
                members[r["new"]] = mem
                sid[np.array(mem)] = r["new"]
                H[r["new"]] = r["e"]
                r["snapshot_sid"] = None
            levels.append(recs)
            self.iter_log.append((len(comps), self.T - t0))
        # unpacking, Section 7 of the paper: T maps each current super-vertex to its physical entering edge
        T = dict(H)
        for recs in reversed(levels):
            for r in recs:
                e = T.pop(r["new"])
                for S, f in r["H"].items():
                    T[S] = f
                # locate the old super-vertex holding the head of e
                head = e[1]
                Sstar = next(S for S in r["U"] if head in self._mem(S, r))
                T[Sstar] = e
                S = Sstar
                while S in r["nxt"]:
                    (x, y, S2) = r["nxt"][S]
                    T[S2] = (x, y)
                    S = S2
        parent = np.full(n, -1)
        for S, (u, v) in T.items():
            parent[S] = u
        return parent, total

    def _mem(self, S, r):
        # members of an old super-vertex: recorded lazily from the snapshot taken at contraction
        return self.oldmem[S]

    def _components(self, H, sid, members):
        """Active components: for the functional graph S -> super(source of H[S]), the ones that hold a cycle."""
        self.oldmem = getattr(self, "oldmem", {})
        for S, mem in members.items():
            self.oldmem[S] = set(mem)
        par = {S: int(sid[e[0]]) for S, e in H.items()}
        state = {}
        cycles = {}
        rootS = int(sid[self.root])
        for S0 in list(H):
            S = S0
            path = []
            while S in par and S not in state:
                state[S] = S0
                path.append(S)
                S = par[S]
            if S in state and state[S] == S0 and S in par:  # new cycle closed
                i = path.index(S)
                cycles[S] = path[i:]
        comps = []
        children = {}
        for S, p in par.items():
            children.setdefault(p, []).append(S)
        for c, cyc in cycles.items():
            seen = set(cyc)
            st = list(cyc)
            while st:
                x = st.pop()
                for y in children.get(x, []):
                    if y not in seen:
                        seen.add(y)
                        st.append(y)
            comps.append((cyc, seen))
        return comps

    def _internal_sssp(self, w, sid, members, cycle, supers, phys, inA):
        """Distance to the cycle inside A at super-vertex level, and DHHM accounting at physical level."""
        n = self.n
        dist = {S: math.inf for S in supers}
        nxt = {}
        # meta graph inside A: edge S -> S' with weight min w(x, y), x in S, y in S'. Reverse Dijkstra.
        cyc = set(cycle)
        hp = []
        for S in cycle:
            dist[S] = 0
            hp.append((0, S))
        heapq.heapify(hp)
        done = set()
        order = []
        sub_u = phys
        while hp:
            d, S = heapq.heappop(hp)
            if S in done:
                continue
            done.add(S)
            order.append(S)
            mem = np.array(members[S])
            sub = w[np.ix_(sub_u, mem)]  # entering edges of S from inside A
            mask = (sub < INF) & (sid[sub_u][:, None] != S)
            ru, rv = np.nonzero(mask)
            for a, b in zip(ru.tolist(), rv.tolist()):
                x = int(sub_u[a])
                Sx = int(sid[x])
                nd = d + int(sub[a, b])
                if Sx not in done and nd < dist[Sx]:
                    dist[Sx] = nd
                    nxt[Sx] = (x, int(mem[b]), S)
                    heapq.heappush(hp, (nd, Sx))
        # DHHM set partition over the physical settled order
        phys_order = [x for S in order for x in members[S]]
        ph = phys_order
        settled_rank = {x: i for i, x in enumerate(ph)}
        pos_d = {x: dist[sid[x]] for x in ph}
        stack = []  # sets P1, ..., Pl as lists
        i = 0
        L = len(ph)
        # TopK per set when it becomes the top of the stack, as in step 2(a)
        cur = [ph[0]] if L else []
        while cur:
            self._topk_charge(w, cur, pos_d, inA, settled_rank, i, phys)
            stack.append(cur)
            i += 1
            if i >= L:
                break
            new = [ph[i]]
            while stack and len(stack[-1]) == len(new):
                new = stack.pop() + new
            cur = new
        return dist, nxt

    def _topk_charge(self, w, P, pos_d, inA, settled_rank, i, phys):
        """One TopK on set P, array model: N = all entering edges of P. Reversed edge x -> u, type u."""
        P = np.array(P)
        col = w[:, P]
        finite = col < INF
        N = int(self.deg[P].sum())
        K = len(P)
        self.builds += 1
        self.T += N
        self.cost += math.sqrt(K * max(N, 1))
        us, cs = np.nonzero(finite & inA[:, None])
        if len(us) == 0:
            return
        # only sources not settled yet are live: type u, value dist(x) + w(u, x)
        rank = np.full(self.n, -1)
        for x, r in settled_rank.items():
            rank[x] = r
        live = (rank[us] > i) | (rank[us] < 0)
        us, cs = us[live], cs[live]
        if len(us) == 0:
            return
        dx = np.array([pos_d[int(x)] for x in P], dtype=float)
        vals = col[us, cs].astype(float) + dx[cs]
        self.G += scan_red(vals, us.astype(np.int64), K, self.rng)


def solve(W, root=0, seed=0):
    r = FO(W, root, seed)
    return r, r.solve()
