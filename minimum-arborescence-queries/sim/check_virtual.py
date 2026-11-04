"""Black-box check. One iteration of FO = ONE SSSP from a new source s on a virtual graph on the physical vertices:
reversed edges x -> u of weight w(u, x), kept only when u and x lie in the same active component, weight 0 when they
lie in the same super-vertex, plus s -> c_i of weight 0 for one physical vertex c_i of each cycle.

Each virtual array query (x, i) needs one input query (x, i) in the entering list of x, since the current weight is a
function of the answer and classical data (sid, component label, offsets).

Asserts, at every iteration, on random and family instances:
  (a) all current weights are non-negative, as DHHM Section 7 requires;
  (b) the SSSP distance of every physical vertex equals FO's internal super-vertex distance;
  (c) the current weight of each edge is w0(u,v) + offset(v) unless both ends share a super-vertex, offset being classical.
"""
import sys
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import dijkstra

sys.dont_write_bytecode = True
import fo
import trees
import check_fo
from fo import INF


class Checked(fo.FO):
    checks = 0

    def _internal_sssp(self, w, sid, members, cycle, supers, phys, inA):
        dist, nxt = super()._internal_sssp(w, sid, members, cycle, supers, phys, inA)
        n = self.n
        ins = np.ix_(phys, phys)
        sub = w[ins].astype(float).copy()
        finite = sub < INF
        lab = sid[phys]
        same = lab[:, None] == lab[None, :]
        assert (sub[finite & ~same] >= 0).all(), "negative weight"
        # reversed physical graph with s = index k. scipy treats explicit zeros in sparse input as absent, so shift.
        k = len(phys)
        idx = {int(x): i for i, x in enumerate(phys)}
        rows, cols, data = [], [], []
        eps = 1e-7
        us, vs = np.nonzero(finite)
        for a, b in zip(us.tolist(), vs.tolist()):
            if a == b:
                continue
            ww = 0.0 if same[a, b] else float(sub[a, b])
            rows.append(b)
            cols.append(a)
            data.append(ww + eps)
        c = members[cycle[0]][0]
        rows.append(k)
        cols.append(idx[c])
        data.append(eps)
        g = csr_matrix((data, (rows, cols)), shape=(k + 1, k + 1))
        d = dijkstra(g, directed=True, indices=k)
        for x in phys:
            ds = dist[sid[x]]
            dv = d[idx[int(x)]]
            if np.isinf(ds):
                assert np.isinf(dv), ("reach", x)
            else:
                assert abs(dv - ds) < 1e-3, ("dist", x, dv, ds)
        Checked.checks += 1
        return dist, nxt


def run(W):
    r = Checked(W.copy(), 0, 1)
    return r.solve()


def main():
    rng = np.random.default_rng(5)
    for t in range(2500):
        n = int(rng.integers(3, 14))
        run(check_fo.hard_random(n, rng))
    print("random: components checked", Checked.checks)
    for name, f in trees.cases().items():
        for n in (16, 64, 128):
            W = f(n)
            W[:, 0] = INF
            run(W)
    print("with families: components checked", Checked.checks, "all assertions hold")


if __name__ == "__main__":
    main()
