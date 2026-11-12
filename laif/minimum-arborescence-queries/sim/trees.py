"""T and G of generalized decision trees (Beigi-Taghavi Theorem 4(ii)) for directed MST, on hard families.

T = reads on the path, G = red edges on the path, with every scan in random order and the black class being
"this answer does not change what the tree keeps". Numbers are for single paths with one random seed per run;
T is deterministic given the instance, G is an average over the scan order in the theorem.

Trees:
  plain     Edmonds path growing, each selection a fresh minimum finding over all edges entering the container.
  perhead   memory per head: each vertex keeps its K cheapest entering edges, doubling K on exhaustion.
  notes     ../README.md sections 3-4: binary-counter groups with TopK, scanned in random order.
  fo        Fischer-Oshman iterations, each SSSP as DHHM Theorem 18 sets, scanned in random order.
"""
import math
import sys
import numpy as np

sys.dont_write_bytecode = True
import arb
import instances as I
import fo
from arb import INF, Group

scan_red = fo.scan_red


def mode_scan(Wsub, y, mask, d, rng, s):
    f = Wsub - y
    f[Wsub >= INF] = INF
    f[mask, :] = INF
    us, cs = np.nonzero(f < INF)
    s.T += int((Wsub < INF).sum())
    s.G += scan_red(f[us, cs].astype(float), us.astype(np.int64), d, rng)
    return arb.top_k_exact(f, None, d, rng, s)


class Notes(arb.Run):
    def __init__(self, W):
        self.boot = True
        super().__init__(W, 0, mode_scan, 0)


class PerHead(arb.Run):
    def __init__(self, W):
        super().__init__(W, 0, mode_scan, 0)

    def _install(self, c, g):
        g.K = 1
        self.groups[c][int(g.verts[0])] = g
        self._build(c, g)

    def _contract(self, cycle):
        new = self.next_id
        self.next_id += 1
        self.children[new] = list(cycle)
        for c in cycle:
            self.up[c] = new
        self.node_y[new] = 0
        mem, grp = [], {}
        for c in cycle:
            mem += self.members.pop(c)
            grp.update(self.groups.pop(c))
        self.comp[np.array(mem)] = new
        self.members[new], self.groups[new] = mem, grp
        return new


class Plain(arb.Run):
    def __init__(self, W):
        super().__init__(W, 0, mode_scan, 0)

    def _build(self, c, g):
        pass

    def _min_in(self, c):
        s = self.stats
        verts = np.array(self.members[c])
        Wsub = self.W[:, verts]
        s.T += int((Wsub < INF).sum())
        f = (Wsub - self.y[verts]).astype(float)
        f[Wsub >= INF] = np.inf
        f[self.comp == c, :] = np.inf
        vals = f[np.isfinite(f)]
        if len(vals) == 0:
            return None
        vals = vals[self.rng.permutation(len(vals))]
        pm = np.minimum.accumulate(vals)
        s.G += 1 + int((pm[1:] < pm[:-1]).sum())
        i, j = np.unravel_index(np.argmin(f), f.shape)
        return int(f[i, j]), int(i), int(verts[j])


def backpath(n):
    """Every back edge is in the optimum, each becomes relevant only after the previous one: see sampling.py."""
    W = np.full((n, n), 100 * n, dtype=np.int64)
    for j in range(1, n - 1):
        W[j, j + 1] = 0
        W[j + 1, j] = 1
    B = 4 * n
    for k in range(1, n):
        W[0, k] = B - 2 * k
    np.fill_diagonal(W, INF)
    W[:, 0] = INF
    return W


def binary_merge(n):
    """Pairs merge with pairs: FO should need about log n iterations. Weight by level of the dyadic block."""
    W = np.empty((n, n), dtype=np.int64)
    for u in range(n):
        for v in range(n):
            x = (u - 1) ^ (v - 1)
            W[u, v] = (x.bit_length() if u and v else 40) * 2**x.bit_length() + (u % 3 if u else 0) if u != v else 0
    W[0, :] = 10**8
    np.fill_diagonal(W, INF)
    W[:, 0] = INF
    return W


def cases():
    fam = dict(I.FAMILIES)
    fam["backpath"] = backpath
    fam["binmerge"] = binary_merge
    return fam


def measure(W, which):
    W = W.copy()
    W[:, 0] = INF
    m = int((W < INF).sum())
    if which == "fo":
        run = fo.FO(W, 0, 7)
        res = run.solve()
        T, G, extra = run.T, run.G, run.iters
    else:
        cls = dict(plain=Plain, perhead=PerHead, notes=Notes)[which]
        arb.Stats.T = 0
        arb.Stats.G = 0
        run = cls(W)
        res = run.solve()
        T, G, extra = run.stats.T, run.stats.G, run.stats.rebuilds
    return m, T, G, extra, res


def main():
    ns = [int(x) for x in sys.argv[1].split(",")] if len(sys.argv) > 1 else [64, 128, 256]
    only = sys.argv[2].split(",") if len(sys.argv) > 2 else None
    print("family      n     tree      T/m      G/n     sqrt(TG)/sqrt(nm)  sqrt(TG)/n^1.5  extra")
    for name, f in cases().items():
        if only and name not in only:
            continue
        for n in ns:
            W = f(n)
            ref = None
            for which in ("plain", "perhead", "notes", "fo"):
                m, T, G, extra, res = measure(W, which)
                if res is not None:
                    cost = sum(int(W[res[0][v], v]) for v in range(1, n))
                    if ref is None:
                        ref = cost
                    assert cost == ref, (name, n, which, cost, ref)
                print(f"{name:10s} {n:5d} {which:8s} {T/m:9.2f} {G/n:8.2f} {math.sqrt(T*G/(n*m)):12.2f} {math.sqrt(T*G)/n**1.5:14.2f}   {extra}", flush=True)


if __name__ == "__main__":
    main()
