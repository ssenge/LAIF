"""Max-Cut on random 3-regular graphs with N = 96 (the hardware family of arXiv:2603.10191 Sec. II C): the regularized
warm start alone, without a circuit, against the SDP with hyperplane rounding (key GW) and the cubic-graph SDP with
path and triangle constraints and local moves (key HLZ), with the exact optimum as reference. Metrics as there: approximation ratio = mean cut / OPT, p(success) = fraction of output bitstrings
with cut = OPT. LS = the single-step local search of Algorithm 3 there (one pass of improving single flips, then one pass of
improving double flips over the edges).
  RWS sampled     bitstrings x_i ~ Bernoulli(p_i) from the warm start (their 'RWS'); ratio exact, p(success) from SHOTS;
                  with LS: the first 2000 samples
  RWS rounded     s_i = sign(m_i), deterministic
  rule6           rounded, then 3 rounds of the flip rule (rws_local.rounds, radius 6), mean over 20 rule seeds
  X               polarized spins fixed, the rest solved exactly (c2_x.X)
  GW              SDP (30), SHOTS random-hyperplane roundings; with LS: the first 2000
  HLZ             SDP (34): unit vectors, the equalities v_i.v_j + v_i.v_k + v_j.v_k = -1 for every path (i,j),(j,k) in E,
                  and every violated triangle inequality of (34) added until none is violated by more than 1e-4; SHOTS
                  roundings, the first 1000 of them each followed by the local moves (a), (b), (c) of Sec. IV E 2 until none
                  increases the cut
OPT: exact, by variable elimination on all spins.
HLZ is capped at CAP seconds per graph (default 3 h): at the cap the separation stops and SCS is given the remaining time;
a capped graph is kept and flagged (HLZ.capped), its SDP value then is the last SCS iterate, not a certified bound.
Sampling uses default_rng((0, seed)) per graph.
Usage: python -I c1_n96.py graphs|a:b shots out.jsonl [CAP]"""
import os, sys, json, time, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, networkx as nx, cvxpy as cp
from rws_local import graph, rws_ca, rounds, cut
from c2_x import X
from frozen_ceiling import ceiling

def opt(G):
    """Exact maximum cut by variable elimination on all spins (frozen_ceiling.ceiling with no spin fixed)."""
    N = G.number_of_nodes(); c, s, w, _ = ceiling(G, np.zeros(N), np.ones(N, np.int64))
    nb = np.array([sorted(G[v]) for v in range(N)], np.int64); assert cut(nb, s) == c
    return c

def cutv(E, S):                                         # S: (shots, N) in {+1, -1}
    return (S[:, E[:, 0]] != S[:, E[:, 1]]).sum(1)

def ls(nb, s):
    """Algorithm 3: one pass of improving single flips, then one pass of improving double flips over the edges."""
    s = s.copy(); N = len(s)
    for i in range(N):
        if (s[nb[i]] == s[i]).sum() >= 2: s[i] = -s[i]
    for i in range(N):
        for j in nb[i]:
            if j > i:
                t = s.copy(); t[i] = -t[i]; t[j] = -t[j]
                if cut(nb, t) > cut(nb, s): s = t
    return s

def hlz_moves(G, nb, s):
    """Moves (a), (b), (c) of HLZ until none increases the cut."""
    s = s.copy()
    while True:
        c0 = cut(nb, s); same = np.array([(s[nb[v]] == s[v]).sum() for v in range(len(s))])
        V3 = np.where(same == 3)[0]
        if len(V3):                                     # (a): a V3 vertex with the fewest V3 neighbours
            v = min(V3, key=lambda u: ((same[nb[u]] == 3).sum(), u)); s[v] = -s[v]; assert cut(nb, s) > c0; continue
        U = nx.Graph([(i, j) for i, j in G.edges() if s[i] == s[j]]); moved = False
        for comp in nx.connected_components(U):         # uncut-edge components: V2 vertices have U-degree 2
            H = U.subgraph(comp); inner = [v for v in H if same[v] == 2]
            if all(same[v] == 2 for v in H) and nx.is_eulerian(H) and len(H) % 2 == 0:      # (c): a cycle
                cyc = [u for u, _ in nx.eulerian_circuit(H)]; flips = cyc[1::2]
            else:                                       # (b): a path u - v1 - ... - vk - w
                ends = [v for v in H if same[v] != 2]
                if len(ends) != 2 or not inner: continue
                path = nx.shortest_path(H, ends[0], ends[1]); flips = path[1:-1][0::2]
            t = s.copy(); t[flips] = -t[flips]
            if cut(nb, t) > c0: s = t; moved = True; break
        if not moved: return s

def sdp(G, hlz, cap=None):
    t0 = time.perf_counter(); capped = False; status = None
    N = G.number_of_nodes(); Y = cp.Variable((N, N), PSD=True); E = list(G.edges())
    obj = cp.Maximize(sum((1 - Y[i, j]) / 2 for i, j in E)); cons = [cp.diag(Y) == 1]
    if hlz:                                             # one vectorized constraint per family (scalar constraints blew up memory)
        P = np.array(sorted({tuple(sorted((i, k))) + (j,) for j in G for i, k in itertools.combinations(G[j], 2)}))
        cons += [Y[P[:, 0], P[:, 2]] + Y[P[:, 2], P[:, 1]] + Y[P[:, 0], P[:, 1]] == -1]
    T = np.array(list(itertools.combinations(range(N), 3))); SG = np.array([(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)])
    cut_rows = np.zeros((0, 2), np.int64)               # rows (triple index, sign index) already added
    for _ in range(30):
        tri = []
        if len(cut_rows):
            t, g = T[cut_rows[:, 0]], SG[cut_rows[:, 1]]
            tri = [cp.multiply(g[:, 0], Y[t[:, 0], t[:, 1]]) + cp.multiply(g[:, 1], Y[t[:, 0], t[:, 2]]) + cp.multiply(g[:, 2], Y[t[:, 1], t[:, 2]]) >= -1]
        left = None if cap is None else cap - (time.perf_counter() - t0)
        if left is not None and left <= 0: capped = True; break
        pr = cp.Problem(obj, cons + tri); pr.solve(solver=cp.SCS, eps_abs=1e-7, eps_rel=1e-7, max_iters=200000, **({} if left is None else dict(time_limit_secs=left)))   # SCS: first-order, low memory
        status = pr.status
        if left is not None and time.perf_counter() - t0 >= cap: capped = True; break
        if not hlz: break
        V = Y.value; val = SG[:, 0] * V[T[:, 0], T[:, 1]][:, None] + SG[:, 1] * V[T[:, 0], T[:, 2]][:, None] + SG[:, 2] * V[T[:, 1], T[:, 2]][:, None]
        ti, si = np.nonzero(val < -1 - 1e-4); new = np.c_[ti, si]
        old = {(a, b) for a, b in cut_rows}; new = np.array([r for r in new if (r[0], r[1]) not in old]).reshape(-1, 2)
        if len(new) == 0: break
        if len(new) > 2000: new = new[np.argsort(val[new[:, 0], new[:, 1]])[:2000]]   # shortcut: at most 2000 most violated cuts per round, enough for n = 96
        cut_rows = np.r_[cut_rows, new]
    w, U = np.linalg.eigh(Y.value); return U * np.sqrt(np.clip(w, 0, None)), Y.value, capped, status

def main(seeds, shots, out, cap=3 * 3600):
    with open(out, "a") as f:
        for sd in seeds:
            rng = np.random.default_rng((0, sd))
            G, nb = graph(96, sd); E = np.array(G.edges()); t0 = time.perf_counter(); O = opt(G); r = dict(N=96, seed=sd, OPT=O, t_opt=time.perf_counter() - t0)
            m, _ = rws_ca(nb, 0.6, 100, sd); p = (1 - m) / 2
            S = np.where(rng.random((shots, 96)) < p, -1, 1); cs = cutv(E, S)
            r["RWS_sampled"] = dict(ratio=float(np.sum((1 - m[E[:, 0]] * m[E[:, 1]]) / 2) / O), succ=float((cs == O).mean()))
            SL = np.array([ls(nb, x) for x in S[:2000]]); cl = cutv(E, SL)
            r["RWS_sampled_LS"] = dict(ratio=float(cl.mean() / O), succ=float((cl == O).mean()))
            s0 = np.where(m > 0, 1, -1).astype(np.int64); c0 = cut(nb, s0); c0l = cut(nb, ls(nb, s0))
            r["RWS_rounded"] = dict(ratio=c0 / O, succ=float(c0 == O)); r["RWS_rounded_LS"] = dict(ratio=c0l / O, succ=float(c0l == O))
            c6 = np.array([rounds(nb, s0, 3, k)[1][3] for k in range(20)]); r["rule6"] = dict(ratio=float(c6.mean() / O), succ=float((c6 == O).mean()))
            cx = X(G, m, 0.0)[0]; r["X"] = dict(ratio=cx / O, succ=float(cx == O)); r["polarized"] = float((np.abs(m) >= 1 - 1e-9).mean())
            for name, hl in (("GW", False), ("HLZ", True)):
                t0 = time.perf_counter(); V, Yv, capd, st = sdp(G, hl, cap if hl else None); R = rng.standard_normal((V.shape[1], shots))
                Sg = np.where(V @ R >= 0, 1, -1).T.astype(np.int64)
                if hl: Sg = np.array([hlz_moves(G, nb, x) for x in Sg[:1000]])
                cg = cutv(E, Sg); r[name] = dict(ratio=float(cg.mean() / O), succ=float((cg == O).mean()),
                                                 sdp=float(np.sum((1 - Yv[E[:, 0], E[:, 1]]) / 2)), t=time.perf_counter() - t0, capped=capd, status=st)
                if not hl:
                    cgl = cutv(E, np.array([ls(nb, x) for x in Sg[:2000]])); r["GW_LS"] = dict(ratio=float(cgl.mean() / O), succ=float((cgl == O).mean()))
            f.write(json.dumps(r) + "\n"); f.flush(); print(json.dumps(r), flush=True)

if __name__ == "__main__":
    if sys.argv[1] == "test":                           # OPT by brute force at n = 16; LS and HLZ moves never decrease the cut
        for sd in range(3):
            G, nb = graph(16, sd); E = np.array(G.edges())
            bf = max(cutv(E, np.array([[1] + list(b)])).item() for b in itertools.product((1, -1), repeat=15))
            assert opt(G) == bf
            rng = np.random.default_rng(sd)
            for _ in range(50):
                s = np.where(rng.random(16) < 0.5, 1, -1).astype(np.int64)
                assert cut(nb, ls(nb, s)) >= cut(nb, s) and cut(nb, hlz_moves(G, nb, s)) >= cut(nb, s)
            V, Yv, _, _ = sdp(G, True); assert np.all(np.abs(np.diag(Yv) - 1) < 1e-5)
            assert np.sum((1 - Yv[E[:, 0], E[:, 1]]) / 2) >= bf - 1e-4        # relaxation bound
        print("c1_n96 self-checks passed"); sys.exit()
    a = sys.argv[1]; seeds = range(*map(int, a.split(":"))) if ":" in a else range(int(a))
    main(seeds, int(sys.argv[2]), sys.argv[3], *(float(c) for c in sys.argv[4:5]))
