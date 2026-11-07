"""Checks Theorem 3 of ../README.md: a fold point of the SU(8) brick wall circuit of [1], certified in interval
arithmetic, and the traps of Theorem 2 next to it.

Certificate. Fix all angles but x_36 (counting from 1, index 35 in the code). Let g = det J and h = tr(adj J d_w J) with w = adj J e_j.
If g(a) g(b) < 0 and |h(a)| > (b - a) * 125 d^3, where 125 d^{5/2} bounds |h'|, then some t in (a, b) is a fold point.
Both conditions are checked with interval arithmetic at 160 digits (mpmath.iv). The regular preimage and the traps
next to the fold are checked in double precision at x0, the double nearest the fold point.
"""
import itertools
import numpy as np
from mpmath import mp, iv
from scipy.linalg import expm
from scipy.optimize import least_squares

P1 = {"I": np.eye(2), "X": np.array([[0, 1], [1, 0]]), "Y": np.array([[0, -1j], [1j, 0]]), "Z": np.diag([1, -1])}


def word(s):
    M = np.eye(1)
    for c in s:
        M = np.kron(M, P1[c])
    return M.astype(complex)


def one(q, c):
    return "".join(c if k == q else "I" for k in range(3))


def cz(a, b):
    return np.diag([-1.0 if (i >> (2 - a)) & 1 and (i >> (2 - b)) & 1 else 1.0 for i in range(8)]).astype(complex)


# the SU(8) brick wall of [1]: RZ, RY, RZ on each qubit, then 14 bricks CZ_ab RY_a RY_b RZ_a RZ_b on (0,1), (1,2), ...,
# the last brick only RY_a RY_b; 63 rotations, 14 CZ gates
GATES = [("r", one(q, c)) for c in "ZYZ" for q in range(3)]
for i in range(14):
    a, b = (0, 1) if i % 2 == 0 else (1, 2)
    GATES += [("f", cz(a, b))] + [("r", one(q, c)) for c, q in (("Y", a), ("Y", b), ("Z", a), ("Z", b))][: 4 if i < 13 else 2]
NAMES = ["".join(t) for t in itertools.product("IXYZ", repeat=3)][1:]
d = len(NAMES)
assert sum(t == "r" for t, _ in GATES) == d == 63
BAS = [word(s) for s in NAMES]
IDX = {s: i for i, s in enumerate(NAMES)}


def F(x):
    U, k = np.eye(8, dtype=complex), 0
    for t, g in GATES:
        if t == "f":
            U = g @ U
        else:
            U = expm(-0.5j * x[k] * word(g)) @ U; k += 1
    return U


def Jac(x):
    """Column k: coefficients tr(P_w H_k)/8 of H_k = V_k P_k V_k^dag, with dF = -(i/2) H_k F dx_k."""
    cols, V, k = [], np.eye(8, dtype=complex), d - 1
    for t, g in GATES[::-1]:
        if t == "f":
            V = V @ g
        else:
            H = V @ word(g) @ V.conj().T
            cols.append([np.real(np.trace(B @ H)) / 8 for B in BAS])
            V = V @ expm(-0.5j * x[k] * word(g)); k -= 1
    return np.array(cols[::-1]).T


# adjoint action of each gate on strings: rotations fix commuting strings and map Q to cos t Q + sign sin t R
DATA, ROT_OF = [], {}
for gi, (t, g) in enumerate(GATES):
    dd = []
    for q in NAMES:
        Q = word(q)
        if t == "r":
            P = word(g)
            if np.allclose(P @ Q, Q @ P):
                dd.append(None); continue
            PQ = P @ Q
            r = next(r for r in NAMES if abs(np.trace(word(r) @ PQ)) > 1)
            dd.append((IDX[r], int(round(np.real(-1j * np.trace(word(r) @ PQ) / 8)))))
        else:
            Cq = g @ Q @ g.conj().T
            r = next(r for r in NAMES if abs(np.trace(word(r) @ Cq)) > 1)
            dd.append((IDX[r], int(round(np.real(np.trace(word(r) @ Cq) / 8)))))
    if t == "r":
        ROT_OF[gi] = len(ROT_OF)
    DATA.append((t, g, dd))
ROT = sorted(ROT_OF)


def columns(ctx, x, z=None):
    """J and its derivative d_z J along the direction z, as row lists over ctx (mp or iv)."""
    zero = ctx.mpf(0)
    c, s = [ctx.cos(a) for a in x], [ctx.sin(a) for a in x]
    J, dJ = [], []
    for g in ROT:
        vec = {IDX[DATA[g][1]]: (ctx.mpf(1), zero)}
        for h in range(g + 1, len(DATA)):
            t, _, dd = DATA[h]; new = {}
            def add(q, a, da):
                new[q] = (new[q][0] + a, new[q][1] + da) if q in new else (a, da)
            if t == "f":
                for q, (a, da) in vec.items():
                    r, sg = dd[q]; add(r, sg * a, sg * da)
            else:
                k = ROT_OF[h]; ch, sh = c[k], s[k]; zk = z[k] if z is not None else zero
                for q, (a, da) in vec.items():
                    if dd[q] is None:
                        add(q, a, da)
                    else:
                        r, sg = dd[q]
                        add(q, ch * a, ch * da - sh * zk * a)
                        add(r, sg * sh * a, sg * (sh * da + ch * zk * a))
            vec = new
        J.append([vec[q][0] if q in vec else zero for q in range(d)])
        dJ.append([vec[q][1] if q in vec else zero for q in range(d)])
    rows = lambda cols: [[cols[j][i] for j in range(d)] for i in range(d)]
    return rows(J), rows(dJ)


def lu(ctx, A):
    A = [row[:] for row in A]; order = list(range(d)); sign = 1
    size = (lambda v: abs(v.mid)) if ctx is iv else abs
    for k in range(d):
        p = max(range(k, d), key=lambda i: size(A[i][k]))
        if p != k:
            A[k], A[p] = A[p], A[k]; order[k], order[p] = order[p], order[k]; sign = -sign
        for i in range(k + 1, d):
            f = A[i][k] / A[k][k]; A[i][k] = f
            for j in range(k + 1, d):
                A[i][j] = A[i][j] - f * A[k][j]
    return sign, A, order


def solve(fac, b):
    _, A, order = fac
    y = [b[order[i]] for i in range(d)]
    for i in range(d):
        for j in range(i):
            y[i] = y[i] - A[i][j] * y[j]
    for i in reversed(range(d)):
        for j in range(i + 1, d):
            y[i] = y[i] - A[i][j] * y[j]
        y[i] = y[i] / A[i][i]
    return y


def g_and_h(ctx, x, j):
    """g = det J and h = tr(adj J d_w J), w = adj J e_j, using adj J = g J^{-1}."""
    J = columns(ctx, x)[0]
    fac = lu(ctx, J)
    g = ctx.mpf(fac[0])
    for i in range(d):
        g = g * fac[1][i][i]
    z = solve(fac, [ctx.mpf(int(i == j)) for i in range(d)])
    dJ = columns(ctx, x, z)[1]
    T = ctx.mpf(0)
    for i in range(d):
        T = T + solve(fac, [dJ[r][i] for r in range(d)])[i]
    return g, g * g * T


mp.dps = iv.dps = 160
K = 35
XT = [1.3512478812167348, 1.5545203109017967, 2.072523019859703, 2.8740904256684123, 0.5122772734460249, 4.72955549946307, 3.6383071941090184, 1.8830321387973437, 0.48723948401795963, 4.795207340565125, 0.8235935733119912, 0.8369620180302245, 0.8211133331361262, 0.5105861592314477, 5.695031192822646, 1.6917118277497045, 1.9252344492369309, 5.232600972507753, 3.8950939736371266, 1.1758565766484745, 2.7320132440092015, 5.553848643028158, 2.3585445084336745, 4.466600530189464, 0.6082607737830155, 4.569916350751292, 4.8787270378207115, 5.188445709947812, 4.2361297571884435, 2.329382849341934, 0.4034558959882754, 3.259567211561603, 4.759260954558277, 1.1990717962148876, 1.672817830478689, 5.023018236365426, 4.701905880898942, 5.633420573318256, 0.7900572554731561, 1.1578038940336262, 5.0236389511728445, 4.049648791940636, 4.530005652376697, 6.262897938745029, 5.901041717244075, 5.296882713563143, 4.88276263341993, 2.4819789290386955, 4.028961326319425, 1.158906150593644, 4.772044465136576, 4.760710850689077, 4.532031488448627, 2.7947546949261515, 2.376177085322832, 2.637498554647891, 0.20947659220359036, 5.305019749992851, 3.407810445708931, 2.4348514188339085, 3.4433663046809015, 4.534199218072607, 2.3967893298679512]
xs = [mp.mpf(v) for v in XT]                                         # exact binary values of the floats above
at = lambda t: xs[:K] + [t] + xs[K + 1:]

# derivative matrices agree with finite differences
xf = np.array(XT)
Jm, dJm = columns(mp, xs, [mp.mpf(int(i == 40)) for i in range(d)])
e = np.zeros(d); e[40] = 1e-6
assert np.abs(np.array(Jm, dtype=float) - Jac(xf)).max() < 1e-12
assert np.abs(np.array(dJm, dtype=float) - (Jac(xf + e) - Jac(xf - e)) / 2e-6).max() < 1e-8

# root of det J along x_K (any approximation will do: the certificate below is what counts)
t0 = mp.findroot(lambda t: g_and_h(mp, at(t), 0)[0], xs[K], solver="secant", tol=mp.mpf(10) ** -140)
x0 = np.array(XT); x0[K] = float(t0)
Uu, S, Vt = np.linalg.svd(Jac(x0)); u, v = Uu[:, -1], Vt[-1]
j = int(np.argmax(np.abs(u)))
kap = u @ ((Jac(x0 + 1e-6 * v) - Jac(x0 - 1e-6 * v)) / 2e-6) @ v
HP = 125 * d ** 3                                                    # >= 125 d^{5/2} >= max |h'|
hm = g_and_h(mp, at(t0 + mp.mpf(10) ** -60), j)[1]
delta = abs(hm) / HP / 1000
a, b = t0 - delta, t0 + delta
ga, ha = g_and_h(iv, [iv.mpf(y) for y in at(a)], j)
gb, _ = g_and_h(iv, [iv.mpf(y) for y in at(b)], j)
sign_change = bool((ga < 0 and gb > 0) or (ga > 0 and gb < 0))
h_away = bool(ha > 0 or ha < 0)
hlow = min(abs(mp.mpf(ha.a)), abs(mp.mpf(ha.b)))
assert sign_change and h_away and hlow > (b - a) * HP
print(f"SU(8) brick wall of [1], all angles fixed but x_{K + 1}: det J changes sign on (a, b) with a = {mp.nstr(a, 25)}, "
      f"b - a = {mp.nstr(b - a, 3)}, and |h| >= {mp.nstr(hlow, 4)} > (b - a) * 125 d^3 there, in interval arithmetic "
      f"at 160 digits: a fold point")
print(f"  at x_{K + 1} = t0 (floating point): sigma_62 = {S[-2]:.4f}, sigma_63 = {S[-1]:.1e}, kappa = {kap:+.4f} for unit null vectors")


# regular preimage of F(x0) and traps of Theorem 2
def res(y, Ut):
    r = (F(y) - Ut).ravel(); return np.concatenate([r.real, r.imag])


def res_jac(y, Ut):
    Fy, J = F(y), Jac(y)
    A = np.array([(-0.5j * sum(J[w, k] * BAS[w] for w in range(d)) @ Fy).ravel() for k in range(d)]).T
    return np.concatenate([A.real, A.imag])


fit = lambda start, Ut: least_squares(res, start, jac=res_jac, args=(Ut,), method="lm", xtol=1e-15, ftol=1e-15, gtol=1e-15).x
rng = np.random.default_rng(5)
U0 = F(x0)
x1 = fit(rng.uniform(0, 4 * np.pi, d), U0)
s1 = np.linalg.svd(Jac(x1), compute_uv=False)[-1]
assert np.abs(F(x1) - U0).max() < 1e-12 and s1 > 1e-2
print(f"F(x0) has a regular preimage x1: max |F(x1) - F(x0)| = {np.abs(F(x1) - U0).max():.1e}, sigma_min(J(x1)) = {s1:.3f}")
loss = lambda x, Ut: 1 - np.real(np.trace(Ut.conj().T @ F(x))) / 8


def grad(x, Ut):
    Fx, J = F(x), Jac(x)
    return np.array([-np.real(np.trace(-0.5j * Ut.conj().T @ sum(J[w, k] * BAS[w] for w in range(d)) @ Fx)) / 8 for k in range(d)])


def hess(x, Ut, s=1e-5):
    H = np.array([(grad(x + s * e, Ut) - grad(x - s * e, Ut)) / (2 * s) for e in np.eye(d)])
    return (H + H.T) / 2


W = sum(u[w] * BAS[w] for w in range(d))
for eps in (-np.sign(kap) * 1e-3, -np.sign(kap) * 1e-4):
    Ut = expm(-0.5j * eps * W) @ U0
    x = x0.copy()
    for _ in range(6):
        x = x - np.linalg.solve(hess(x, Ut), grad(x, Ut))
    lmin = np.linalg.eigvalsh(hess(x, Ut))[0]
    other = fit(x1, Ut)
    L, Lo = loss(x, Ut), loss(other, Ut)
    assert abs(L / (eps ** 2 / 8) - 1) < 1e-5 and abs(lmin / (abs(eps * kap) / 4) - 1) < 0.01 and Lo < 1e-14 and np.linalg.norm(x - x0) < 1e-8
    print(f"eps = {eps:+.0e} (trap side): critical point at distance {np.linalg.norm(x - x0):.1e} from x0, loss {L:.6e} = "
          f"{L / (eps ** 2 / 8):.5f} eps^2/8, smallest second-derivative eigenvalue {lmin:.2e} (|eps kappa|/4 = "
          f"{abs(eps * kap) / 4:.2e}); from x1 the loss reaches {Lo:.1e}, so the minimum is spurious")
print("brick wall checks pass")
