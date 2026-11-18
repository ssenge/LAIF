"""Fixed-Hamming-weight Boltzmann sampling pi_K(x) ~ exp(-beta E(x)), E(x) = sum_{ij in E} Q_ij x_i x_j, sum x = K, on the
instances of arXiv:2611.05883, with the mixing metric of that paper: normalized Hamming distance d(t) between replica pairs,
normalized autocorrelation C(l) (its Eq. 30) averaged over pairs, fit C(l) = exp(-tau l).
Proposals (one MCMC step each):
  gk  global Kawasaki: swap a uniform 1-bit with a uniform 0-bit, Metropolis.
  lk  local Kawasaki: a uniform edge; if its bits differ, swap them, Metropolis (otherwise the state is kept).
  ph  exact heat bath on a uniform edge (two-vertex block with its weight fixed).
  bh  exact heat bath on a uniform block of the paper (49 vertices): the block is redrawn from pi_K conditioned on the
      outside and on its Hamming weight, by a transfer-matrix pass over a vertex order of the block (acceptance 1).
Usage: python -I mcmc.py <144|1064> <coupling seed> [steps] [beta]"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, networkx as nx
from numba import njit
from scipy.optimize import curve_fit
from blocks import g144, g1064

def couplings(n, E, seed):
    rng = np.random.default_rng(seed); w = rng.normal(size=len(E))
    nb = [[] for _ in range(n)]
    for (u, v), q in zip(E, w): nb[u].append((v, q)); nb[v].append((u, q))
    ptr = np.cumsum([0] + [len(a) for a in nb]).astype(np.int64)
    idx = np.array([v for a in nb for v, _ in a], np.int64); val = np.array([q for a in nb for _, q in a])
    return ptr, idx, val, np.array(E, np.int64), w

def block_plan(B, ptr, idx, val):
    """Vertex order of block B with small frontiers, and per-step tables for the transfer-matrix pass."""
    G = nx.Graph(); G.add_nodes_from(B); inB = set(B)
    for v in B:
        for k in range(ptr[v], ptr[v + 1]):
            if idx[k] in inB: G.add_edge(v, int(idx[k]))
    best = None
    for s in B:                                               # BFS orders from every start: keep the narrowest
        order = list(nx.bfs_tree(G, s)); done = set(); F = []; widths = []
        for v in order:
            done.add(v); F = [u for u in F + [v] if any(w not in done for w in G[u])]; widths.append(len(F))
        if best is None or max(widths) < best[0]: best = (max(widths), order)
    W, order = best; b = len(order)
    pos_map = -np.ones((b, W), np.int64); coup = np.zeros((b, W)); vnew = -np.ones(b, np.int64); wold = np.zeros(b, np.int64)
    done = set(); F = []
    for t, v in enumerate(order):
        wold[t] = len(F)
        done.add(v); Fn = [u for u in F + [v] if any(w not in done for w in G[u])]
        for p, u in enumerate(F): pos_map[t, p] = Fn.index(u) if u in Fn else -1
        vnew[t] = Fn.index(v) if v in Fn else -1
        F = Fn
    assert not F
    return np.array(order, np.int64), W, pos_map, coup, vnew, wold

@njit(cache=True)
def de_swap(x, i, j, ptr, idx, val):
    """Energy change of setting x_i 1 -> 0 and x_j 0 -> 1."""
    d = 0.0
    for k in range(ptr[i], ptr[i + 1]): d -= val[k] * x[idx[k]]
    for k in range(ptr[j], ptr[j + 1]):
        if idx[k] != i: d += val[k] * x[idx[k]]
    return d

@njit(cache=True)
def block_heat_bath(x, order, W, pos_map, coup, vnew, wold, ptr, idx, val, inblk, beta, A):
    b = len(order); k = 0
    for t in range(b): k += x[order[t]]
    ext = np.zeros(b)
    for t in range(b):
        v = order[t]
        for q in range(ptr[v], ptr[v + 1]):
            if not inblk[idx[q]]: ext[t] += val[q] * x[idx[q]]
    A[0, :, :] = 0.0; A[0, 0, 0] = 1.0
    for t in range(b):
        A[t + 1, :, :] = 0.0
        for m in range(1 << wold[t]):
            for c in range(t + 1):
                a = A[t, m, c]
                if a == 0.0: continue
                nm = 0; e = ext[t]
                for p in range(wold[t]):
                    if (m >> p) & 1:
                        e += coup[t, p]
                        if pos_map[t, p] >= 0: nm |= 1 << pos_map[t, p]
                A[t + 1, nm, c] += a                                              # x_v = 0
                nm1 = nm | (1 << vnew[t]) if vnew[t] >= 0 else nm
                A[t + 1, nm1, c + 1] += a * np.exp(-beta * e)                     # x_v = 1
        s = A[t + 1].max(); A[t + 1] /= s
    m = 0; c = k; probs = np.zeros(2 << W)
    for t in range(b - 1, -1, -1):                                               # backward sampling
        tot = 0.0
        for mo in range(1 << wold[t]):
            nm = 0; e = ext[t]
            for p in range(wold[t]):
                if (mo >> p) & 1:
                    e += coup[t, p]
                    if pos_map[t, p] >= 0: nm |= 1 << pos_map[t, p]
            w0 = A[t, mo, c] if nm == m else 0.0
            nm1 = nm | (1 << vnew[t]) if vnew[t] >= 0 else nm
            w1 = A[t, mo, c - 1] * np.exp(-beta * e) if (c >= 1 and nm1 == m) else 0.0
            probs[2 * mo] = w0; probs[2 * mo + 1] = w1; tot += w0 + w1
        r = np.random.random() * tot; acc = 0.0; pick = 0
        for z in range(2 << wold[t]):
            acc += probs[z]
            if acc >= r and probs[z] > 0: pick = z; break
        mo, xv = pick >> 1, pick & 1
        x[order[t]] = xv; m = mo; c -= xv
    assert c == 0 and m == 0

@njit(cache=True)
def run(method, x0, steps, beta, ptr, idx, val, E, plans_order, plans_W, plans_pm, plans_cp, plans_vn, plans_wo, nblk, blen, seed):
    np.random.seed(seed)
    R, n = x0.shape; X = x0.copy(); D = np.zeros((R // 2, steps))
    A = np.zeros((blen + 1, 1 << plans_W.max(), blen + 1)); inblk = np.zeros(n, np.bool_)
    for t in range(steps):
        for r in range(R):
            x = X[r]
            if method == 0 or method == 1:
                if method == 0:
                    while True:
                        i = np.random.randint(n)
                        if x[i] == 1: break
                    while True:
                        j = np.random.randint(n)
                        if x[j] == 0: break
                else:
                    e = np.random.randint(E.shape[0]); i, j = E[e, 0], E[e, 1]
                    if x[i] == x[j]: continue
                    if x[i] == 0: i, j = j, i
                d = de_swap(x, i, j, ptr, idx, val)
                if d <= 0 or np.random.random() < np.exp(-beta * d): x[i] = 0; x[j] = 1
            elif method == 2:
                e = np.random.randint(E.shape[0]); i, j = E[e, 0], E[e, 1]
                if x[i] == x[j]: continue
                if x[i] == 0: i, j = j, i
                d = de_swap(x, i, j, ptr, idx, val)                               # heat bath between the two states
                if np.random.random() < 1.0 / (1.0 + np.exp(beta * d)): x[i] = 0; x[j] = 1
            else:
                q = np.random.randint(nblk); o = plans_order[q]
                for v in o: inblk[v] = True
                block_heat_bath(x, o, plans_W[q], plans_pm[q], plans_cp[q], plans_vn[q], plans_wo[q], ptr, idx, val, inblk, beta, A)
                for v in o: inblk[v] = False
        for p in range(R // 2):
            s = 0
            for v in range(n): s += X[2 * p, v] != X[2 * p + 1, v]
            D[p, t] = s / n
    return D

def autocorr(D, L):
    C = []
    for d in D:
        dd = d - d.mean(); den = (dd * dd).sum()
        C.append(np.array([(dd[: len(dd) - l] * dd[l:]).sum() / den for l in range(L)]))
    return np.mean(C, axis=0)

def fit_tau(C, cut=0.1):
    """Least-squares fit of exp(-tau l) on the lags before C first drops below cut (same rule for every method)."""
    L = int(np.argmax(C < cut)) if (C < cut).any() else len(C)
    L = max(L, 3); l = np.arange(L)
    return curve_fit(lambda l, t: np.exp(-t * l), l, C[:L], p0=[1.0 / L])[0][0], L

METHODS = {"gk": 0, "lk": 1, "ph": 2, "bh": 3}

def main(N, seed, steps, beta, methods=("gk", "lk", "ph", "bh"), R=16):
    n, E, blocks = g144() if N == 144 else g1064()
    ptr, idx, val, Ea, w = couplings(n, E, seed)
    Gq = {tuple(e): q for e, q in zip(E, w)}
    plans = []
    for B in blocks:
        plans.append(list(block_plan(B, ptr, idx, val)))
    # couplings between the vertex added at step t and the frontier vertices before it
    for P, B in zip(plans, blocks):
        order, W, pm, cp, vn, wo = P; inB = set(B); done = set(); F = []
        Gb = nx.Graph([e for e in E if e[0] in inB and e[1] in inB])
        for t, v in enumerate(order):
            for p, u in enumerate(F): cp[t, p] = Gq.get(tuple(sorted((u, v))), 0.0)
            done.add(v); F = [u for u in F + [v] if any(z not in done for z in Gb[u])]
    Wmax = max(P[1] for P in plans); b = len(blocks[0])
    po = np.array([P[0] for P in plans]); pW = np.array([P[1] for P in plans], np.int64)
    pm = np.full((len(plans), b, Wmax), -1, np.int64); cp = np.zeros((len(plans), b, Wmax))
    for q, P in enumerate(plans): pm[q, :, : P[1]] = P[2]; cp[q, :, : P[1]] = P[3]
    pv = np.array([P[4] for P in plans]); pwo = np.array([P[5] for P in plans])
    rng = np.random.default_rng(1000 + seed); K = n // 2
    x0 = np.zeros((R, n), np.int64)
    for r in range(R): x0[r, rng.choice(n, K, replace=False)] = 1
    out = {}
    for name in methods:
        run(METHODS[name], x0[:2], 2, beta, ptr, idx, val, Ea, po, pW, pm, cp, pv, pwo, len(plans), b, 0)      # compile
        t0 = time.perf_counter(); D = run(METHODS[name], x0, steps, beta, ptr, idx, val, Ea, po, pW, pm, cp, pv, pwo, len(plans), b, seed)
        dt = (time.perf_counter() - t0) / (steps * R)
        C = autocorr(D, min(steps // 2, 20000)); tau, L = fit_tau(C)
        out[name] = (tau, dt, L)
        print(f"N={n} seed={seed} beta={beta} {name}: tau={tau:.5g} per step (fit lags 0..{L - 1}), {1e6 * dt:.2f} us per step, "
              f"tau per second {tau / dt:.4g}, max frontier {Wmax}", flush=True)
    return out

if __name__ == "__main__":
    N, seed = int(sys.argv[1]), int(sys.argv[2])
    steps = int(sys.argv[3]) if len(sys.argv) > 3 else (3000 if N == 144 else 27000)
    beta = float(sys.argv[4]) if len(sys.argv) > 4 else 0.5
    main(N, seed, steps, beta)
