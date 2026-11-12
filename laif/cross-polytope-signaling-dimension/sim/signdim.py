"""Signaling dimension of the cross-polytope: is every primitive measurement r-simulable?
A primitive measurement is an affinely independent set T of cube vertices (d-bit integers, bit 1 = coordinate -1) with 0 in the
relative interior of conv T; f = 2 x (barycentric weights of 0). By Prop. 2.1 of the source paper it is r-simulable iff some
distribution F on the r-subsets of T has sum_{X disjoint from S} F(X) <= 1 - f(S) for every S inside T and inside a facet.
Usage: signdim.py d r [cores]    or    signdim.py --brute d"""
import sys, os, itertools
from collections import defaultdict
from multiprocessing import Pool
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog

def vec(x, d): return np.array([1 - 2 * ((x >> i) & 1) for i in range(d)])

def simulable(T, f, d, r):
    k = len(T)
    if k <= r: return True, None
    subs = list(itertools.combinations(range(k), r))
    A, b = [], []
    for i in range(d):
        for e in (0, 1):
            H = [j for j in range(k) if (T[j] >> i) & 1 == e]
            for m in range(1, len(H) + 1):
                for S in itertools.combinations(H, m):
                    A.append([1.0 if not set(X) & set(S) else 0.0 for X in subs]); b.append(1 - f[list(S)].sum())
    res = linprog(np.zeros(len(subs)), A_ub=A, b_ub=b, A_eq=[np.ones(len(subs))], b_eq=[1], bounds=(0, None), method="highs")
    return res.status == 0, (res.x if res.status == 0 else None)

def exact_cert(T, d, r):
    """Exact rational check: f from exact barycentric weights, F from the LP solution rounded to rationals."""
    k = len(T)
    if k <= r: return True
    A = [[Fr(1)] + [Fr(int(v)) for v in vec(x, d)] for x in T]        # rows: points with a leading 1
    # solve sum_j lam_j A_j = (1, 0, ..., 0) exactly on k independent coordinates (Gaussian elimination on the transpose)
    M = [[A[j][i] for j in range(k)] + [Fr(1 if i == 0 else 0)] for i in range(d + 1)]
    rows, piv = [], []
    for i in range(d + 1):
        v = M[i][:]
        for p, pr in zip(piv, rows):
            if v[p]: v = [a - v[p] * b for a, b in zip(v, pr)]
        c = next((j for j in range(k) if v[j]), None)
        if c is None: assert v[k] == 0; continue
        v = [a / v[c] for a in v]
        rows = [[a - pr[c] * b for a, b in zip(pr, v)] for pr in rows]; rows.append(v); piv.append(c)
    lam = [Fr(0)] * k
    for p, pr in zip(piv, rows): lam[p] = pr[k]
    f = [2 * l for l in lam]
    assert all(l > 0 for l in lam) and len(piv) == k
    ok, x = simulable(T, np.array([float(v) for v in f]), d, r)
    if not ok: return False
    subs = list(itertools.combinations(range(k), r))
    for den in (1, 2, 3, 4, 6, 8, 12, 24, 60, 120, 840, 10 ** 6):
        F = [Fr(round(v * den), den) for v in x]
        s = sum(F)
        if s == 0: continue
        F = [v / s for v in F]
        good = all(v >= 0 for v in F)
        for i in range(d):
            for e in (0, 1):
                H = [j for j in range(k) if (T[j] >> i) & 1 == e]
                for m in range(1, len(H) + 1):
                    for S in itertools.combinations(H, m):
                        if sum(F[a] for a, X in enumerate(subs) if not set(X) & set(S)) > 1 - sum(f[j] for j in S): good = False
        if good: return den
    return None

def exact_f(T, d):
    k = len(T)
    A = [[Fr(1)] + [Fr(int(v)) for v in vec(x, d)] for x in T]
    M = [[A[j][i] for j in range(k)] + [Fr(1 if i == 0 else 0)] for i in range(d + 1)]
    rows, piv = [], []
    for i in range(d + 1):
        v = M[i][:]
        for p, pr in zip(piv, rows):
            if v[p]: v = [a - v[p] * b for a, b in zip(v, pr)]
        c = next((j for j in range(k) if v[j]), None)
        if c is None: assert v[k] == 0; continue
        v = [a / v[c] for a in v]
        rows = [[a - pr[c] * b for a, b in zip(pr, v)] for pr in rows]; rows.append(v); piv.append(c)
    assert len(piv) == k
    lam = [Fr(0)] * k
    for p, pr in zip(piv, rows): lam[p] = pr[k]
    assert all(l > 0 for l in lam)
    return [2 * l for l in lam]

def exact_vertex(T, f, d, r):
    """Exact fallback: take a vertex of the LP, solve its active constraints exactly in rationals, verify every constraint."""
    k = len(T); subs = list(itertools.combinations(range(k), r))
    rows, rhs = [], []
    for i in range(d):
        for e in (0, 1):
            H = [j for j in range(k) if (T[j] >> i) & 1 == e]
            for m in range(1, len(H) + 1):
                for S in itertools.combinations(H, m):
                    rows.append([0 if set(X) & set(S) else 1 for X in subs]); rhs.append(1 - sum(f[j] for j in S))
    A = np.array(rows, float); b = np.array([float(v) for v in rhs])
    res = linprog(np.zeros(len(subs)), A_ub=A, b_ub=b, A_eq=[np.ones(len(subs))], b_eq=[1], bounds=(0, None), method="highs-ds")
    x = res.x
    eqs = [(row, v) for row, v, sl in zip(rows, rhs, b - A @ x) if sl < 1e-9] + [([1] * len(subs), Fr(1))]
    eqs += [([1 if j == i else 0 for j in range(len(subs))], Fr(0)) for i in range(len(subs)) if x[i] < 1e-9]
    n = len(subs); M = [[Fr(c) for c in row] + [Fr(v)] for row, v in eqs]; piv = []; R = []
    for v in M:                                         # exact row reduction
        for p, pr in zip(piv, R):
            if v[p]: c = v[p]; v = [a - c * q for a, q in zip(v, pr)]
        c = next((j for j in range(n) if v[j]), None)
        if c is None: continue
        v = [a / v[c] for a in v]
        R = [[a - pr[c] * q for a, q in zip(pr, v)] for pr in R]; R.append(v); piv.append(c)
    F = [Fr(0)] * n
    free = [j for j in range(n) if j not in piv]
    for j in free: F[j] = Fr(round(x[j] * 10 ** 6), 10 ** 6)
    for p, pr in zip(piv, R): F[p] = pr[n] - sum(pr[j] * F[j] for j in free)
    ok = all(v >= 0 for v in F) and sum(F) == 1 and all(sum(c * F[j] for j, c in enumerate(row) if c) <= v for row, v in zip(rows, rhs))
    return ok

def canon(T, d):
    prof = {x0: sorted(bin(x0 ^ t).count("1") for t in T) for x0 in T}
    m = min(prof.values())
    best = None
    for x0 in T:
        if prof[x0] != m: continue
        U = [t ^ x0 for t in T]
        cols = [[(u >> j) & 1 for u in U] for j in range(d)]
        w = [sum(c) for c in cols]
        inv = [(w[j], tuple(sorted(sum(a & b for a, b in zip(cols[j], cols[i])) for i in range(d) if i != j)),
                tuple(sorted(sum(cols[i][r] for i in range(d)) for r in range(len(U)) if cols[j][r]))) for j in range(d)]
        groups = defaultdict(list)
        for j in range(d): groups[inv[j]].append(j)
        keys = sorted(groups)
        for choice in itertools.product(*[itertools.permutations(groups[k]) for k in keys]):
            order = [j for g in choice for j in g]     # new position p holds old column order[p]
            img = sorted(sum(((u >> order[p]) & 1) << p for p in range(d)) for u in U)
            t = tuple(img)
            if best is None or t < best: best = t
    return best

def extend(args):
    T, d, k = args
    pts = PTS[d]
    out = set()
    cand = np.array([x for x in range(2 ** d) if x not in T])
    B = pts[np.c_[np.tile(T, (len(cand), 1)), cand]]
    G = B @ B.transpose(0, 2, 1)
    indep = np.abs(np.linalg.det(G)) > 0.5
    if k == d + 1 and indep.any():                     # last level: only simplices with 0 in the interior matter
        Bs = B[indep]
        lam = np.linalg.solve(Bs.transpose(0, 2, 1), np.tile(np.r_[1, np.zeros(d)], (len(Bs), 1))[..., None])[..., 0]
        keep = np.zeros(len(cand), bool); keep[np.flatnonzero(indep)[lam.min(1) > 1e-9]] = True
        indep = keep
    for x in cand[indep]:
        out.add(canon(tuple(sorted(T + (int(x),))), d))
    return out

PTS = {d: np.array([np.r_[1, vec(x, d)] for x in range(2 ** d)], float) for d in range(1, 9)}

def run(d, r, log=print, cores=8):
    pts = PTS[d]
    level = {canon((0,), d)}
    prim = []
    with Pool(cores) as pool:
        for k in range(2, d + 2):
            nxt = set()
            for part in pool.imap_unordered(extend, [(T, d, k) for T in level], chunksize=64): nxt |= part
            level = nxt
            for T in level:
                B = pts[list(T)]
                lam = np.linalg.lstsq(B.T, np.r_[1, np.zeros(d)], rcond=None)[0]
                if np.abs(B.T @ lam - np.r_[1, np.zeros(d)]).max() < 1e-9 and lam.min() > 1e-9: prim.append((T, 2 * lam))
            log(f"d = {d}: {len(level)} orbits of affinely independent {k}-sets{' with 0 inside' if k == d + 1 else ''}, primitive so far {len(prim)}")
    return prim

def count(args):
    k, a, d = args                                        # sets {0, a, ...} with second element a
    rest = range(a + 1, 2 ** d)
    C = np.zeros((1, 0), np.int64) if k == 2 else np.fromiter(itertools.chain.from_iterable(itertools.combinations(rest, k - 2)), dtype=np.int64).reshape(-1, k - 2)
    if len(C) == 0: return 0
    T = np.c_[np.zeros(len(C), np.int64), np.full(len(C), a), C]
    B = PTS[d][T]                                          # (m, k, d + 1)
    G = B @ B.transpose(0, 2, 1)                       # (m, k, k), nonsingular iff affinely independent
    det = np.linalg.det(G)
    ok = np.abs(det) > 0.5                             # integer matrix: det is an integer
    if not ok.any(): return 0
    B, G = B[ok], G[ok]
    e0 = np.zeros(d + 1); e0[0] = 1
    lam = np.linalg.solve(G, (B @ e0)[..., None])[..., 0]
    resid = np.abs(np.einsum("mk,mkj->mj", lam, B) - e0).max(1)
    return int(((resid < 1e-9) & (lam.min(1) > 1e-9)).sum())

def orbit_count(T, d):                                 # members of the orbit of T that contain the vertex 0
    imgs = {tuple(sorted(sum((((t ^ m) >> i) & 1) << p[i] for i in range(d)) for t in T)) for p in itertools.permutations(range(d)) for m in range(2 ** d)}
    return sum(1 for U in imgs if 0 in U)

if __name__ == "__main__":
    pr = lambda s: print(s, flush=True)
    if sys.argv[1] == "--brute":
        d = int(sys.argv[2])
        prim = run(d, d, lambda s: None)
        with Pool(8) as pool: brute = sum(pool.map(count, [(k, a, d) for k in range(2, d + 2) for a in range(1, 2 ** d)], chunksize=1))
        orb = sum(orbit_count(T, d) for T, f in prim)
        pr(f"d = {d}: primitive supports containing a fixed vertex: brute force {brute}, from the orbit list {orb}")
        assert brute == orb
    else:
        d, r = int(sys.argv[1]), int(sys.argv[2])
        prim = run(d, r, pr, int(sys.argv[3]) if len(sys.argv) > 3 else 8)
        sizes = sorted(len(T) for T, f in prim)
        pr(f"support sizes: " + ", ".join(f"{s}: {sizes.count(s)}" for s in sorted(set(sizes))))
        bad = [(T, f) for T, f in prim if not simulable(T, f, d, r)[0]]
        pr(f"d = {d}, r = {r}: {len(prim)} primitive measurements up to symmetry, {len(bad)} not r-simulable")
        for T, f in bad[:10]: pr(f"  not simulable: {[tuple(int(v) for v in vec(x, d)) for x in T]} f = {np.round(f, 4).tolist()}")
        if not bad:
            dens = [exact_cert(T, d, r) for T, f in prim]
            pr(f"exact rational certificates by rounding: {sum(1 for x in dens if x)} of {len(prim)}")
            rest = [T for (T, f), x in zip(prim, dens) if not x]
            if rest:
                ok = [exact_vertex(T, exact_f(T, d), d, r) for T in rest]
                pr(f"exact rational certificates from the active constraints of an LP vertex: {sum(ok)} of {len(rest)}")
                assert all(ok)
