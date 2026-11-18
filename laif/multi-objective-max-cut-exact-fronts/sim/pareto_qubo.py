"""Exact Pareto set of a multi-objective QUBO  max (x^T Q_1 x, ..., x^T Q_m x), x in {0,1}^n,
by the frontier dynamic program of pareto_dp.py. lin[v] (m-vector) is the value of x_v = 1, pair[(u,v)] the value of x_u = x_v = 1.
pareto_qubo returns (width, front, labels) with labels[i] one binary vector attaining front[i]."""
import itertools, sys
import numpy as np
sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from pareto_dp import order, nondom
import moocore

def pareto_qubo(n, lin, pair, coords=None, stats=None, keep_x=False):
    m = lin.shape[1]; E = sorted(pair)
    w, o, last, pos = order(list(range(n)), E, coords)
    adj = {v: [] for v in range(n)}
    for (u, v) in E: adj[u].append((v, pair[(u, v)])); adj[v].append((u, pair[(u, v)]))
    states = {(): (np.zeros((1, m)), np.zeros((1, 0), dtype=np.uint8))}; front = []
    for i, v in enumerate(o):
        new = {}
        for key, (P, X) in states.items():
            asg = dict(zip(front, key))
            for b in (0, 1):
                add = lin[v] + sum((c for u, c in adj[v] if asg.get(u) == 1), np.zeros(m)) if b else np.zeros(m)
                nf = front + [v]; nk = key + (b,)
                kk = tuple(nk[j] for j, x in enumerate(nf) if last[x] > i)
                new.setdefault(kk, []).append((P + add, np.hstack([X, np.full((len(X), 1), b, np.uint8)]) if keep_x else X))
        front = [x for x in front + [v] if last[x] > i]
        states = {}
        for k, L in new.items():
            P = np.vstack([a for a, _ in L]); X = np.vstack([b for _, b in L]) if keep_x else None
            P, idx = np.unique(P, axis=0, return_index=True); keep = moocore.is_nondominated(P, maximise=True)
            states[k] = (P[keep], X[idx][keep] if keep_x else np.zeros((keep.sum(), 0), np.uint8))
        if stats is not None:
            stats["max_labels"] = max(stats.get("max_labels", 0), sum(len(P) for P, _ in states.values()))
    assert list(states) == [()]
    P, X = states[()]
    if keep_x:                                            # columns are in processing order o
        Xo = np.zeros_like(X); Xo[:, o] = X; X = Xo
    return w, P, X

def value(x, lin, pair):
    return x @ lin + sum((c for (u, v), c in pair.items() if x[u] and x[v]), np.zeros(lin.shape[1]))

def selftest(trials=40):
    rng = np.random.default_rng(3)
    for t in range(trials):
        n = int(rng.integers(3, 11)); m = int(rng.integers(2, 4))
        E = [(u, v) for u in range(n) for v in range(u + 1, n) if rng.random() < 0.4]
        lin = rng.normal(size=(n, m)); pair = {e: rng.normal(size=m) for e in E}
        if t % 3 == 0: lin = np.round(lin); pair = {e: np.round(c) for e, c in pair.items()}
        vals = np.array([value(np.array(x), lin, pair) for x in itertools.product((0, 1), repeat=n)])
        ref = nondom(vals); _, got, X = pareto_qubo(n, lin, pair, keep_x=True)
        assert len(ref) == len(got) and np.allclose(ref[np.lexsort(ref.T)], got[np.lexsort(got.T)]), (t, len(ref), len(got))
        for x, p in zip(X, got): assert np.allclose(value(x, lin, pair), p)
    return trials

if __name__ == "__main__":
    print("ok", selftest(), "random QUBO cases")
