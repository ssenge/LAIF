"""Spurious local minima at a fold point of a 15-parameter two-qubit PQC.

The circuit and fold point are those of the refutation of [1, Conjecture 3] in [5]: words
(YY, IY, XX, ZY, ZX, IZ, XY, YZ, IX, XZ, ZI, YI, YX, XI, ZZ) in F = R_{P_1}(a_1) ... R_{P_15}(a_15), with
a_5 = a_6 = a_7 = a_10 = pi/4 (counting from 0) and the other inputs 0. J is the 15 x 15 matrix of string
coefficients of the generators of dF. At these angles J has entries in Q(sqrt 2): the fold conditions
rank J = 14 and kappa = u^T (d_v J) v != 0 are checked exactly with sympy. Then the compilation loss is
examined for targets moved off F(x0) along the missed direction.
"""
import itertools
import numpy as np
import mpmath as mp
import sympy as sp
from scipy.optimize import least_squares

mp.mp.dps = 60
THEIRS = "YY IY XX ZY ZX IZ XY YZ IX XZ ZI YI YX XI ZZ".split()  # leftmost factor first
WORDS = THEIRS[::-1]  # here F(x) = R_{W_15}(x_15) ... R_{W_1}(x_1), the first word acts first
ALPHA = [0.0] * 15
for j in (5, 6, 7, 10):
    ALPHA[j] = np.pi / 4
X0 = np.array(ALPHA[::-1])
P1 = {"I": np.eye(2), "X": np.array([[0, 1], [1, 0]]), "Y": np.array([[0, -1j], [1j, 0]]), "Z": np.diag([1, -1])}
pauli = lambda w: np.kron(P1[w[0]], P1[w[1]]).astype(complex)
BASIS = [pauli("".join(t)) for t in itertools.product("IXYZ", repeat=2)][1:]
SEQ = [pauli(w) for w in WORDS]
D, d = 4, 15


# ---------- double precision (search, optimisation) ----------
def rot(P, t):
    return np.cos(t / 2) * np.eye(D) - 1j * np.sin(t / 2) * P


def F(x):
    U = np.eye(D, dtype=complex)
    for P, t in zip(SEQ, x):
        U = rot(P, t) @ U
    return U


def J(x):
    cols, V = [], np.eye(D, dtype=complex)
    for P, t in zip(SEQ[::-1], x[::-1]):
        H = V @ P @ V.conj().T
        cols.append([np.real(np.trace(B @ H)) / D for B in BASIS])
        V = V @ rot(P, t)
    return np.array(cols[::-1]).T


# ---------- 60 digits (certificate) ----------
MSEQ = [mp.matrix(P.tolist()) for P in SEQ]
MBASIS = [mp.matrix(B.tolist()) for B in BASIS]
MI = mp.eye(D)


def mrot(P, t):
    return mp.cos(t / 2) * MI - 1j * mp.sin(t / 2) * P


def mJ(x):
    cols, V = [], mp.eye(D)
    for P, t in zip(MSEQ[::-1], x[::-1]):
        H = V * P * V.H
        cols.append([mp.re(sum((B * H)[i, i] for i in range(D))) / D for B in MBASIS])
        V = V * mrot(P, t)
    cols = cols[::-1]
    return mp.matrix([[cols[k][r] for k in range(d)] for r in range(d)])


def exact_fold():
    """Exact J and d_j J at X0 over Q(sqrt 2), via the adjoint action in the string basis."""
    names = ["".join(t) for t in itertools.product("IXYZ", repeat=2)][1:]
    mats = [pauli(w) for w in names]
    def ad(P, c, s_):  # Ad_{R_P(t)} on string coefficients, with c = cos t, s_ = sin t (or their derivatives)
        A = sp.zeros(d, d)
        for q, Q in enumerate(mats):
            if np.allclose(P @ Q, Q @ P):
                A[q, q] = 1 if c is not None else 0
                continue
            PQ = P @ Q  # = phase * P_r with phase = +-i
            r = next(r for r, M in enumerate(mats) if abs(np.trace(M @ PQ)) > 1)
            phase = np.trace(mats[r] @ PQ) / D
            A[q, q] = c if c is not None else 0
            A[r, q] = int(round(np.real(-1j * phase))) * s_  # R Q R^dag = cos t Q - i sin t P Q
        return A
    h = sp.sqrt(2) / 2
    trig = {0.0: (1, 0, 0, 1), np.pi / 4: (h, h, -h, h)}  # cos, sin, d cos, d sin
    gates = [(pauli(w), trig[float(t)]) for w, t in zip(WORDS, X0)]
    Ad = [ad(P, cs[0], cs[1]) for P, cs in gates]
    dAd = []
    for P, cs in gates:
        A = ad(P, cs[2], cs[3])
        for q, Q in enumerate(mats):
            if np.allclose(P @ Q, Q @ P):
                A[q, q] = 0  # commuting words do not move
        dAd.append(A)
    e = lambda w: sp.Matrix([1 if names[q] == w else 0 for q in range(d)])
    def column(k, j=None):  # H_k = Ad(R_15) ... Ad(R_{k+1}) P_k, optionally differentiated in x_j
        vec = e(WORDS[k])
        for m in range(k + 1, d):
            vec = (dAd[m] if m == j else Ad[m]) * vec
        return vec
    J = sp.Matrix.hstack(*[column(k) for k in range(d)]).applyfunc(sp.nsimplify)
    dJ = [sp.Matrix.hstack(*[column(k, j) if j > k else sp.zeros(d, 1) for k in range(d)]) for j in range(d)]
    assert np.allclose(np.array(J.evalf(30).tolist(), dtype=float), globals()["J"](X0), atol=1e-12)
    assert J.rank(simplify=True) == 14
    v = J.nullspace(simplify=True)[0]
    u = J.T.nullspace(simplify=True)[0]
    dvJ = sum((v[j] * dJ[j] for j in range(d)), sp.zeros(d, d))
    kappa = sp.nsimplify(sp.simplify((u.T * dvJ * v)[0] / (u.norm() * v.norm() ** 2)))
    assert kappa != 0
    s14 = np.linalg.svd(globals()["J"](X0), compute_uv=False)[-2]
    un = np.array((u / u.norm()).evalf(30).tolist(), dtype=float).ravel()
    print(f"exact over Q(sqrt 2): rank J(x0) = 14, kappa = u^T (d_v J) v = {kappa} = {float(kappa):.6f} != 0 "
          f"(unit null vectors); sigma_14 = {s14:.4f}: a fold point")
    return X0, un, float(kappa)


def loss(x, Ut):
    return 1 - np.real(np.trace(Ut.conj().T @ F(x))) / D


def residual(x, Ut):
    R = F(x) - Ut
    return np.concatenate([R.real.ravel(), R.imag.ravel()]) / np.sqrt(2 * D)  # squared norm = loss


def solve(x, Ut):
    return least_squares(residual, x, args=(Ut,), method="lm", xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=20000).x


def mF(x):
    U = mp.eye(D)
    for P, t in zip(MSEQ, x):
        U = mrot(P, t) * U
    return U


def mloss_derivs(xb, Ut):
    """Gradient and second derivative of the loss at xb, central differences at 40 digits."""
    xb = [t if isinstance(t, mp.mpf) else mp.mpf(float(t)) for t in xb]
    MUt = mp.matrix(Ut.conj().T.tolist())
    L = lambda y: 1 - mp.re(sum((MUt * mF([a + b for a, b in zip(xb, y)]))[k, k] for k in range(D))) / D
    h = mp.mpf(10) ** -12
    e = lambda i, c: [c if k == i else 0 for k in range(d)]
    grad = [(L(e(i, h)) - L(e(i, -h))) / (2 * h) for i in range(d)]
    H = np.zeros((d, d))
    for i in range(d):
        for j in range(i, d):
            f = lambda a, b: L([x + y for x, y in zip(e(i, a * h), e(j, b * h))])
            H[i, j] = H[j, i] = float((f(1, 1) - f(1, -1) - f(-1, 1) + f(-1, -1)) / (4 * h * h))
    return L([0] * d), grad, H


def check_trap(x0, u, kappa, rng):
    W = sum(c * B for c, B in zip(u, BASIS))  # unit direction of su(4) missed by dF at x0
    mp.mp.dps = 40
    sols = [solve(rng.uniform(0, 4 * np.pi, d), F(x0)) for _ in range(10)]
    x1 = max((x for x in sols if np.linalg.norm(residual(x, F(x0))) < 1e-13),
             key=lambda x: np.linalg.svd(J(x), compute_uv=False)[-1])
    s1 = np.linalg.svd(J(x1), compute_uv=False)[-1]
    assert s1 > 1e-2
    print(f"F(x0) has the regular preimage x1 (residual {np.linalg.norm(residual(x1, F(x0))):.1e}, sigma_min = {s1:.3f}), "
          "so targets near F(x0) have loss-zero parameters near x1")
    side = -np.sign(kappa)  # targets exp(-i eps W/2) F(x0) with eps kappa < 0 lie outside the local image
    for eps in (1e-2, 1e-3, 1e-4):
        for sgn in (side, -side):
            lam = np.linalg.eigvalsh(mloss_derivs(x0, mp_expm(W, sgn * eps) @ F(x0))[2])[0]
            assert (lam > 0) == (sgn == side)
            print(f"eps = {sgn * eps:+.0e} ({'outside' if sgn == side else 'inside'} the local image): smallest "
                  f"second-derivative eigenvalue of the loss at x0 {lam:+.3e}; -eps kappa/4 = {-sgn * eps * float(kappa) / 4:+.3e}")
        Ut = mp_expm(W, side * eps) @ F(x0)
        xm = [mp.mpf(float(t)) for t in solve(x0, Ut)]
        for _ in range(3):  # second-order steps at 40 digits
            val, grad, H = mloss_derivs(xm, Ut)
            step = np.linalg.solve(H, np.array([float(g) for g in grad]))
            xm = [a - mp.mpf(float(b)) for a, b in zip(xm, step)]
        val, grad, H = mloss_derivs(xm, Ut)
        gn, lam, val = float(mp.sqrt(sum(g ** 2 for g in grad))), np.linalg.eigvalsh(H)[0], float(val)
        # third derivatives of the loss are at most (sqrt(15)/2)^3 < 7.3, so with |grad| <= lam^2/30 a critical
        # point lies within 2|grad|/lam, where the second derivative stays >= lam/2: a strict local minimum
        assert lam > 0 and gn < lam ** 2 / 30 and abs(val / (eps ** 2 / 8) - 1) < 0.01
        xm = np.array([float(t) for t in xm])
        sols = [solve(rng.uniform(0, 4 * np.pi, d), Ut) for _ in range(10)]
        best = min(sols, key=lambda x: np.linalg.norm(residual(x, Ut)))
        lbest = float(mloss_derivs(best, Ut)[0])  # the loss itself, at 40 digits
        assert lbest < 1e-6 * val
        print(f"  local minimum at distance {np.linalg.norm(xm - x0):.1e} from x0: loss {val:.6e} = "
              f"{val / (eps ** 2 / 8):.6f} eps^2/8, gradient {gn:.1e}, smallest second-derivative eigenvalue "
              f"{lam:.3e}; another parameter has loss {lbest:.1e}, so the minimum is spurious")


def mp_expm(W, eps):
    w, Q = np.linalg.eigh(W)
    return Q @ np.diag(np.exp(-1j * eps * w / 2)) @ Q.conj().T


if __name__ == "__main__":
    rng = np.random.default_rng(15)
    x0, u, kappa = exact_fold()
    check_trap(x0, u, kappa, rng)
    print("fold and trap checks pass")
