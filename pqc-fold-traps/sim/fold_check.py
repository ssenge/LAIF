"""A fold point of a 15-parameter two-qubit PQC, and the local minimum it creates.

F(x) = prod_k exp(-i x_k P_k / 2) maps T^15 into SU(4). J(x) is the 15 x 15 matrix of Pauli coefficients of
the generators of dF (unit columns). A fold point x0: rank J(x0) = 14 and kappa = u^T (d_v J) v != 0, with
v, u the right and left null vectors. Then grad det J(x0) . w = c u^T (d_w J) v with c != 0, so the critical set
is a smooth hypersurface near x0, ker J(x0) is transverse to it, and F(C) contains a 14-dimensional piece.
"""
import itertools
import numpy as np
import mpmath as mp
from scipy.optimize import brentq, least_squares

mp.mp.dps = 60
WORDS = "YX XY IX IY XX IZ YZ XI YY ZX YI IY IX XX XZ".split()
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


def mdet(x):
    return mp.det(mJ(x))


def find_fold(seed=7):
    rng = np.random.default_rng(seed)
    th = rng.uniform(0, 4 * np.pi, d)
    while True:
        w = rng.normal(size=d)
        w /= np.linalg.norm(w)
        ts = np.linspace(0, 6, 600)
        vals = [np.linalg.det(J(th + s * w)) for s in ts]
        for i in range(len(ts) - 1):
            if vals[i] * vals[i + 1] < 0:
                s0 = brentq(lambda s: np.linalg.det(J(th + s * w)), ts[i], ts[i + 1], xtol=1e-15)
                x = th + s0 * w
                if np.linalg.svd(J(x), compute_uv=False)[-2] > 0.05:
                    return x


def certify(x_double):
    x = [mp.mpf(float(t)) for t in x_double]
    h = mp.mpf(10) ** -25
    for _ in range(6):  # second-order steps on det along its gradient
        g = [(mdet([x[j] + (h if j == k else 0) for j in range(d)]) - mdet([x[j] - (h if j == k else 0) for j in range(d)])) / (2 * h) for k in range(d)]
        g2 = sum(t ** 2 for t in g)
        f0 = mdet(x)
        x = [x[k] - f0 * g[k] / g2 for k in range(d)]
    gn = mp.sqrt(g2)
    U, S, V = mp.svd_r(mJ(x))
    s14, s15 = S[d - 2], S[d - 1]
    u = [U[r, d - 1] for r in range(d)]
    v = [V[d - 1, r] for r in range(d)]
    Jp = mJ([x[k] + h * v[k] for k in range(d)])
    Jm = mJ([x[k] - h * v[k] for k in range(d)])
    kappa = sum(u[r] * (Jp[r, c] - Jm[r, c]) / (2 * h) * v[c] for r in range(d) for c in range(d))
    # sign change of det J across the critical set at distance delta: a zero x0 within delta of x
    delta = mp.mpf(10) ** -30
    dp = mdet([x[k] + delta * g[k] / gn for k in range(d)])
    dm = mdet([x[k] - delta * g[k] / gn for k in range(d)])
    assert dp * dm < 0
    # perturbation from x to x0: |dJ| <= 15 delta, |d^2 J| <= 60 delta; singular subspace perturbation for the null vectors
    dJ = 15 * delta
    sin_t = dJ / (s14 - dJ)
    kappa_err = 60 * delta + 15 * 4 * sin_t + 15 * 2 * (s15 + dJ)
    assert s14 - dJ > 0.05 and abs(kappa) > 1e6 * kappa_err
    print(f"fold point x0 within {mp.nstr(delta, 2)} of x: det J changes sign ({mp.nstr(dm, 3)}, {mp.nstr(dp, 3)})")
    print(f"sigma_14 = {mp.nstr(s14, 6)}, sigma_15 = {mp.nstr(s15, 3)} at x; |grad det J| = {mp.nstr(gn, 4)}")
    print(f"kappa = u^T (d_v J) v = {mp.nstr(kappa, 6)}, perturbation bound {mp.nstr(kappa_err, 3)}: "
          "rank 14 and kernel transverse at x0, a fold")
    return np.array([float(t) for t in x]), np.array([float(t) for t in u]), kappa


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
    """Gradient and Hessian of the loss at xb, central differences at 40 digits."""
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
    for eps in (1e-3, 1e-4):
        for sgn in (side, -side):
            lam = np.linalg.eigvalsh(mloss_derivs(x0, mp_expm(W, sgn * eps) @ F(x0))[2])[0]
            assert (lam > 0) == (sgn == side)
            print(f"eps = {sgn * eps:+.0e} ({'outside' if sgn == side else 'inside'} the local image): smallest "
                  f"Hessian eigenvalue of the loss at x0 {lam:+.3e}; eps v^T H1 v = {-sgn * eps * float(kappa) / 4:+.3e}")
        Ut = mp_expm(W, side * eps) @ F(x0)
        xm = [mp.mpf(float(t)) for t in solve(x0, Ut)]
        for _ in range(3):  # second-order steps at 40 digits
            val, grad, H = mloss_derivs(xm, Ut)
            step = np.linalg.solve(H, np.array([float(g) for g in grad]))
            xm = [a - mp.mpf(float(b)) for a, b in zip(xm, step)]
        val, grad, H = mloss_derivs(xm, Ut)
        gn, lam, val = float(mp.sqrt(sum(g ** 2 for g in grad))), np.linalg.eigvalsh(H)[0], float(val)
        # third derivatives of the loss are at most (sqrt(15)/2)^3 < 7.3, so with |grad| <= lam^2/30 a critical
        # point lies within 2|grad|/lam, where the Hessian stays >= lam/2: a strict local minimum
        assert lam > 0 and gn < lam ** 2 / 30 and abs(val / (eps ** 2 / 8) - 1) < 0.01
        xm = np.array([float(t) for t in xm])
        sols = [solve(rng.uniform(0, 4 * np.pi, d), Ut) for _ in range(10)]
        best = min(sols, key=lambda x: np.linalg.norm(residual(x, Ut)))
        res, smin = np.linalg.norm(residual(best, Ut)), np.linalg.svd(J(best), compute_uv=False)[-1]
        assert res < 1e-13 and smin > 1e-3  # inverse function theorem: an exact preimage within ~res/smin
        print(f"  local minimum at distance {np.linalg.norm(xm - x0):.1e} from x0: loss {val:.6e} = "
              f"{val / (eps ** 2 / 8):.6f} eps^2/8, gradient {gn:.1e}, smallest Hessian eigenvalue "
              f"{lam:.3e}; other parameters reach residual {res:.1e} at a regular point "
              f"(sigma_min = {smin:.3f}), so the minimum is spurious")


def mp_expm(W, eps):
    w, Q = np.linalg.eigh(W)
    return Q @ np.diag(np.exp(-1j * eps * w / 2)) @ Q.conj().T


if __name__ == "__main__":
    rng = np.random.default_rng(15)
    x_double = find_fold()
    x0, u, kappa = certify(x_double)
    check_trap(x0, u, kappa, rng)
    print("fold and trap checks pass")
