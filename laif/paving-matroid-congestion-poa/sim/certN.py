"""Exact upper bound certificates for every reduced rank-2 type (types2.gen) with N players.
Per type: dual LP  min mu  s.t.  R^T y + mu cH >= cF,  y >= 0  (R: equilibrium rows of F against every basis,
cF, cH: cost rows). Weak duality: cost(F) <= mu cost(H) for all a, b >= 0 with F an equilibrium. The float dual y is
scaled to integers Y = round(D y) and mu is recomputed exactly from integer arithmetic; a type is certified when
the exact mu is at most the target. Types that fail are written out for an exact rerun."""
import sys, json, time
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog
from types2 import gen


def build(edges, col, N):
    m = len(col)
    bases = [(i, j) for i in range(m) for j in range(i + 1, m) if col[i] != col[j]]
    Fe, He = edges[:N], edges[N:]
    xF = np.zeros(m, np.int64); xH = np.zeros(m, np.int64)
    for u, v in Fe: xF[u] += 1; xF[v] += 1
    for u, v in He: xH[u] += 1; xH[v] += 1
    rows = []
    for p in set(Fe):
        for q in bases:
            if q == p: continue
            r = np.zeros(2 * m, np.int64)
            for e in p: r[e] += xF[e]; r[m + e] += 1
            for e in q: r[e] -= xF[e] + (e not in p); r[m + e] -= 1
            rows.append(r)
    R = np.array(rows, np.int64).reshape(len(rows), 2 * m)
    return R, np.concatenate([xF * xF, xF]), np.concatenate([xH * xH, xH])


def exact_mu(R, cF, cH, Y, D):
    """Smallest mu with R^T Y + D mu cH >= D cF exactly, or None if a coordinate with cH = 0 fails."""
    RtY = R.T @ Y
    mu = None
    for j in range(len(cF)):
        need = D * int(cF[j]) - int(RtY[j])
        if cH[j] == 0:
            if need > 0: return None
        else:
            v = Fr(need, D * int(cH[j])); mu = v if mu is None or v > mu else mu
    return mu if mu is not None else Fr(0)


def solve_exact(A, b):
    """Solve A x = b over Fractions (consistent, possibly overdetermined); free columns set to 0. None if inconsistent."""
    m, n = len(A), len(A[0]); M = [list(A[i]) + [b[i]] for i in range(m)]; piv = []; r = 0
    for c in range(n):
        pr = next((i for i in range(r, m) if M[i][c] != 0), None)
        if pr is None: continue
        M[r], M[pr] = M[pr], M[r]; inv = 1 / M[r][c]; M[r] = [v * inv for v in M[r]]
        for i in range(m):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [vi - f * vr for vi, vr in zip(M[i], M[r])]
        piv.append(c); r += 1
        if r == m: break
    if any(all(v == 0 for v in M[i][:n]) and M[i][n] != 0 for i in range(r, m)): return None
    x = [Fr(0)] * n
    for i, c in enumerate(piv): x[c] = M[i][n]
    return x


def exact_fallback(R, cF, cH, z, target):
    """Exact dual on the float support: tight constraints of R^T y + mu cH >= cF, solved over Fractions."""
    nr = len(R); y = z[:nr]
    sup = [k for k in range(nr) if y[k] > 1e-9]
    slack = R.T.astype(float) @ y + z[-1] * cH - cF
    tight = [j for j in range(len(cF)) if abs(slack[j]) < 1e-7]
    A = [[Fr(int(R[k][j])) for k in sup] + [Fr(int(cH[j]))] for j in tight]
    sol = solve_exact(A, [Fr(int(cF[j])) for j in tight]) if tight else None
    if sol is None or any(v < 0 for v in sol[:-1]): return None
    Y = [Fr(0)] * nr
    for k, v in zip(sup, sol[:-1]): Y[k] = v
    mu = sol[-1]
    for j in range(len(cF)):                                     # exact feasibility of every dual constraint
        if sum(Y[k] * int(R[k][j]) for k in sup) + mu * int(cH[j]) < int(cF[j]): return None
    return mu if mu <= target else None


def certify(edges, col, N, target):
    R, cF, cH = build(edges, col, N)
    nr = len(R)
    A = -np.hstack([R.T.astype(float), cH[:, None].astype(float)])
    res = linprog(np.append(np.zeros(nr), 1.0), A_ub=A, b_ub=-cF.astype(float),
                  bounds=[(0, None)] * nr + [(None, None)], method="highs")
    if res.status != 0: return None, None
    y = res.x[:nr]
    for D in (10**6, 10**9, 10**12):
        Y = np.array([int(round(v * D)) if v > 0 else 0 for v in y], dtype=object)
        mu = exact_mu(R.astype(object), cF, cH, Y, D)
        if mu is not None and mu <= target: return mu, res.x[-1]
    return exact_fallback(R, cF, cH, res.x, target), res.x[-1]


if __name__ == "__main__":
    N = int(sys.argv[1]); target = Fr(sys.argv[2]); out = open(sys.argv[3], "w")
    t = time.time(); n = 0; worst = Fr(0); worstT = None; fails = 0; tight = 0; fmax = 0.0
    for edges, col in gen(N):
        n += 1
        mu, f = certify(edges, col, N, target)
        fmax = max(fmax, f if f is not None else 0)
        if mu is None:
            fails += 1; out.write(json.dumps({"edges": edges, "col": col, "float": f}) + "\n")
        else:
            tight += mu == target
            if mu > worst: worst, worstT = mu, (edges, col)
        if n % 200000 == 0: print(n, "types", fails, "fails", "worst", worst, f"{time.time()-t:.0f}s", flush=True)
    print("DONE types", n, "float max", fmax, "fails", fails, "tight", tight, "worst certified", worst, worstT, f"{time.time()-t:.0f}s")
