"""Exact certificate: three bases of C^d with a regular point (psi, u) where the information I(u) vanishes.

The bases are U = (1 - iH)(1 + iH)^{-1} for rational self-adjoint H, so they are exactly unitary
over Q(i). A float solution is refined, d - 2 coordinates are fixed (slices) to get a square system, and the
standard root-existence test for quadratic systems is run in exact rational arithmetic (infinity norms):
  beta = |J0^{-1}|, eta = |J0^{-1} F(x0)|, L = bound on the change of J per unit step, h = beta L eta < 1/2
gives a root within 2 eta, at which J is invertible. Every outcome keeps q > 0 within that ball."""
import sys
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import least_squares

sys.path.insert(0, __import__("os").path.dirname(__file__))
from k3 import resid, split


# complex numbers over Q as pairs (re, im)
def cmul(a, b): return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])
def cadd(a, b): return (a[0] + b[0], a[1] + b[1])
def cconj(a): return (a[0], -a[1])
def csum(it):
    s = (Fr(0), Fr(0))
    for z in it: s = cadd(s, z)
    return s


def cinv_mat(M):
    n = len(M); A = [row[:] + [(Fr(int(i == j)), Fr(0)) for j in range(n)] for i, row in enumerate(M)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != (0, 0)); A[c], A[p] = A[p], A[c]
        a = A[c][c]; den = a[0] ** 2 + a[1] ** 2; ai = (a[0] / den, -a[1] / den)
        A[c] = [cmul(ai, x) for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != (0, 0):
                f = A[r][c]; A[r] = [cadd(x, cmul((-f[0], -f[1]), y)) for x, y in zip(A[r], A[c])]
    return [row[n:] for row in A]


def rational_unitary(d, rng):
    G = [[(Fr(int(rng.integers(-6, 7)), 4), Fr(int(rng.integers(-6, 7)), 4)) for _ in range(d)] for _ in range(d)]
    H = [[((G[i][j][0] + G[j][i][0]) / 2, (G[i][j][1] - G[j][i][1]) / 2) for j in range(d)] for i in range(d)]
    iH = [[(-H[i][j][1], H[i][j][0]) for j in range(d)] for i in range(d)]
    P = [[cadd((Fr(int(i == j)), Fr(0)), iH[i][j]) for j in range(d)] for i in range(d)]
    M = [[cadd((Fr(int(i == j)), Fr(0)), (-iH[i][j][0], -iH[i][j][1])) for j in range(d)] for i in range(d)]
    Pi = cinv_mat(P)
    return [[csum(cmul(M[i][k], Pi[k][j]) for k in range(d)) for j in range(d)] for i in range(d)]


def rows(Us):
    """rows <b_x| of all bases, dropping the last outcome of bases 2.. (those equations follow from the others)"""
    d = len(Us[0]); R = []
    for a, U in enumerate(Us):
        for x in range(d if a == 0 else d - 1):
            R.append([cconj(U[i][x]) for i in range(d)])
    return R


def F_exact(x, R, d, slices, x0):
    psi = [(x[i], x[d + i]) for i in range(d)]; u = [(x[2 * d + i], x[3 * d + i]) for i in range(d)]
    out = []
    for w in R:
        a = (Fr(0), Fr(0)); b = (Fr(0), Fr(0))
        for wi, p, v in zip(w, psi, u): a = cadd(a, cmul(wi, p)); b = cadd(b, cmul(wi, v))
        out.append(cmul(cconj(a), b)[0])
    ip = (Fr(0), Fr(0))
    for p, v in zip(psi, u): ip = cadd(ip, cmul(cconj(p), v))
    out.append(ip[1])
    out.append(sum(p[0] ** 2 + p[1] ** 2 for p in psi) - 1)
    out.append(sum(v[0] ** 2 + v[1] ** 2 for v in u) - 1)
    out.append(x[d])                              # gauge: Im psi_0 = 0
    out += [x[j] - x0[j] for j in slices]
    return out


def certify(d, seed):
    rng = np.random.default_rng(seed)
    Us = [rational_unitary(d, rng) for _ in range(3)]
    Uf = [np.array([[float(z[0]) + 1j * float(z[1]) for z in row] for row in U]) for U in Us]
    Ws = np.vstack([U.conj().T for U in Uf])
    for _ in range(200):
        r = least_squares(resid, rng.normal(size=4 * d) / np.sqrt(2 * d), args=(Ws,), xtol=1e-15, ftol=1e-15, gtol=1e-15, method="trf", max_nfev=4000)
        psi, u = split(r.x, d)
        if np.max(np.abs(r.fun)) < 1e-13 and np.min(np.abs(Ws @ psi) ** 2) > 1e-5: break
    else:
        return None
    x = r.x.copy(); psi, u = split(x, d); ph = psi[0] / abs(psi[0])      # gauge Im psi_0 = 0
    psi, u = psi / ph, u / ph; x = np.concatenate([psi.real, psi.imag, u.real, u.imag])
    R = rows(Us); n = 4 * d
    # slices: d - 2 coordinates along which the solution set is well parametrised
    Rf = [np.array([float(z[0]) + 1j * float(z[1]) for z in w]) for w in R]
    def Ffl(x, slices, x0):
        psi, u = split(x, d)
        return np.array([(np.vdot(w.conj(), psi).conj() * (w @ u)).real for w in Rf] + [np.vdot(psi, u).imag, np.vdot(psi, psi).real - 1, np.vdot(u, u).real - 1, x[d]] + [x[j] - x0[j] for j in slices])
    def jac(f, x, *a, h=1e-7):
        return np.column_stack([(f(x + h * e, *a) - f(x - h * e, *a)) / (2 * h) for e in np.eye(n)])
    Jb = jac(Ffl, x, [], x)
    null = np.linalg.svd(Jb)[2][-(d - 2):].T if d > 2 else np.zeros((n, 0))
    from scipy.linalg import qr
    slices = list(qr(null.T, pivoting=True)[2][:d - 2]) if d > 2 else []
    x0 = x.copy()
    for _ in range(5):
        x = x - np.linalg.solve(jac(Ffl, x, slices, x0), Ffl(x, slices, x0))
    X0 = [Fr(float(v)) for v in x]; S0 = [Fr(float(v)) for v in x0]
    F0 = F_exact(X0, R, d, slices, S0)
    # quadratic forms by polarisation: F_i(x) = x^T Q_i x + l_i x + c_i
    z = [Fr(0)] * n
    def ev(v): return F_exact(v, R, d, slices, S0)
    c = ev(z); E = []
    for j in range(n):
        e = z[:]; e[j] = Fr(1); f1 = ev(e); e[j] = Fr(-1); f2 = ev(e)
        E.append(([(p + m) / 2 - ci for p, m, ci in zip(f1, f2, c)], [(p - m) / 2 for p, m in zip(f1, f2)]))
    m = len(c); Q = [[[Fr(0)] * n for _ in range(n)] for _ in range(m)]
    for j in range(n):
        for i in range(m): Q[i][j][j] = E[j][0][i]
        for k in range(j + 1, n):
            e = z[:]; e[j] = e[k] = Fr(1); f = ev(e)
            for i in range(m):
                Q[i][j][k] = Q[i][k][j] = (f[i] - c[i] - E[j][0][i] - E[k][0][i] - E[j][1][i] - E[k][1][i]) / 2
    assert m == n
    J0 = [[2 * sum(Q[i][j][k] * X0[k] for k in range(n)) + E[j][1][i] for j in range(n)] for i in range(n)]
    # self-checks: the quadratic model reproduces F at a random rational point, and J0 matches a numerical Jacobian
    y = [Fr(int(rng.integers(-9, 10)), 7) for _ in range(n)]; Fy = ev(y)
    for i in range(m):
        assert Fy[i] == sum(y[j] * Q[i][j][k] * y[k] for j in range(n) for k in range(n)) + sum(E[j][1][i] * y[j] for j in range(n)) + c[i]
    assert np.max(np.abs(np.array(J0, dtype=float) - jac(Ffl, x, slices, x0))) < 1e-6
    # exact inverse
    A = [row[:] + [Fr(int(i == j)) for j in range(n)] for i, row in enumerate(J0)]
    for col in range(n):
        p = max(range(col, n), key=lambda r: abs(A[r][col])); A[col], A[p] = A[p], A[col]
        piv = A[col][col]; A[col] = [v / piv for v in A[col]]
        for r in range(n):
            if r != col and A[r][col] != 0:
                f = A[r][col]; A[r] = [v - f * w for v, w in zip(A[r], A[col])]
    Ji = [row[n:] for row in A]
    beta = max(sum(abs(v) for v in row) for row in Ji)
    eta = max(abs(sum(a * b for a, b in zip(row, F0))) for row in Ji)
    L = max(2 * sum(abs(v) for row in Qi for v in row) for Qi in Q)
    h = beta * L * eta
    rad = 2 * eta
    qmin = None
    for U in Us:
        for xx in range(d):
            s = (Fr(0), Fr(0))
            for i in range(d): s = cadd(s, cmul(cconj(U[i][xx]), (X0[i], X0[d + i])))
            q = s[0] ** 2 + s[1] ** 2
            qmin = q if qmin is None else min(qmin, q)
    regular = qmin > 2 * d * rad ** 2 * 4      # |<b|psi*>| >= |<b|psi0>| - |psi* - psi0|_2, |.|_2 <= sqrt(2d) rad
    return float(h), float(rad), float(qmin), h < Fr(1, 2) and regular


if __name__ == "__main__":
    for d in [3, 4, 5]:
        for seed in range(2):
            out = certify(d, 100 * d + seed)
            print(f"d={d} seed={seed}: h = {out[0]:.2e}, root within {out[1]:.1e}, q_min = {out[2]:.2e}, certified: {out[3]}", flush=True)
