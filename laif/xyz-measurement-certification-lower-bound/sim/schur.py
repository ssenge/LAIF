"""Exact non-adaptive two-point value for X/Y/Z product settings, reduced by permutation symmetry.

delta*(psi, g) = min over states s0, s1 with <psi|s0|psi> - <psi|s1|psi> >= g of max over settings b in {X,Y,Z}^n
of H^2(P_b(s0), P_b(s1)), with H^2 = 1 - sum sqrt(pq). For copy-wise adaptive settings, the Hellinger affinity of
T copies is at least (1 - delta*)^T, so testing the pair needs T >= c / delta*.

For a permutation-invariant target the program is invariant under qubit permutations and convex, so s0, s1 can be
taken permutation invariant: s = sum_J s_J (x) I_{m_J} in the coupled (Schur) basis. For a product vector
phi = e_1 (x) ... (x) e_n, <phi|s|phi> = sum_J tr(s_J R_J(phi)), where R_J(phi) = sum over coupling paths of the
J-component outer products; R is computed by aggregating Gram matrices along sequential spin-1/2 coupling.
"""
import itertools, sys, time
import numpy as np, cvxpy as cp
from math import comb

s3 = 1 / np.sqrt(3)
AX = {'X': np.array([[1, 1], [1, -1]]) / np.sqrt(2), 'Y': np.array([[1, 1], [1j, -1j]]) / np.sqrt(2), 'Z': np.eye(2)}
th = np.arccos(s3)
a = np.array([np.cos(th / 2), np.exp(1j * np.pi / 4) * np.sin(th / 2)])  # Bloch vector (1,1,1)/sqrt3
ab = np.array([-a[1].conj(), a[0].conj()])


def cg(j2, up):
    """Isometry V_j (x) C^2 -> V_{j +- 1/2}; spins as twice-values j2, basis m = j..-j, qubit |0> = up."""
    jj = j2 / 2; jn2 = j2 + 1 if up else j2 - 1; jn = jn2 / 2
    C = np.zeros((jn2 + 1, 2 * (j2 + 1)))
    for r in range(jn2 + 1):
        m = jn - r
        for s, ms in ((0, 0.5), (1, -0.5)):
            m1 = m - ms
            if abs(m1) > jj + 1e-9: continue
            c = int(round(jj - m1))
            if up:
                val = np.sqrt((jj + m + 0.5) / (2 * jj + 1)) if s == 0 else np.sqrt((jj - m + 0.5) / (2 * jj + 1))
            else:
                val = -np.sqrt((jj - m + 0.5) / (2 * jj + 1)) if s == 0 else np.sqrt((jj + m + 0.5) / (2 * jj + 1))
            C[r, 2 * c + s] = val
    return C


CG = {}
def getcg(j2, up):
    if (j2, up) not in CG: CG[(j2, up)] = cg(j2, up)
    return CG[(j2, up)]


def gram(es, fs=None):
    """R_J(phi, chi) = sum_paths v_phi v_chi^dagger per J (twice-values), phi = (x) es, chi = (x) fs."""
    fs = es if fs is None else fs
    G = {1: np.outer(es[0], fs[0].conj())}
    for e, f in zip(es[1:], fs[1:]):
        E = np.outer(e, f.conj()); H = {}
        for j2, g in G.items():
            K = np.kron(g, E)
            for up in (True, False):
                if not up and j2 == 0: continue
                C = getcg(j2, up); jn2 = j2 + 1 if up else j2 - 1
                H[jn2] = H.get(jn2, 0) + C @ K @ C.T
        G = H
    return G


def mult(n):
    m = {n % 2: 0}; m = {1: 1}
    for _ in range(n - 1):
        h = {}
        for j2, c in m.items():
            h[j2 + 1] = h.get(j2 + 1, 0) + c
            if j2 > 0: h[j2 - 1] = h.get(j2 - 1, 0) + c
        m = h
    return m


def rows(n):
    """One row per (setting type, outcome type): the coefficient matrices R_J and the multiplicity."""
    out = []; g = 0
    for nX in range(n + 1):
        for nY in range(n + 1 - nX):
            nZ = n - nX - nY
            for kX, kY, kZ in itertools.product(range(nX + 1), range(nY + 1), range(nZ + 1)):
                es = ([AX['X'][:, 1]] * kX + [AX['X'][:, 0]] * (nX - kX) + [AX['Y'][:, 1]] * kY + [AX['Y'][:, 0]] * (nY - kY)
                      + [AX['Z'][:, 1]] * kZ + [AX['Z'][:, 0]] * (nZ - kZ))
                out.append((g, comb(nX, kX) * comb(nY, kY) * comb(nZ, kZ), gram(es)))
            g += 1
    return out, g


def target(n, kind):
    if kind == 'prod':
        return {k: v for k, v in gram([a] * n).items()}
    A, B = [a] * n, [ab] * n
    out = {}
    for x, y in ((A, A), (A, B), (B, A), (B, B)):
        for k, v in gram(x, y).items(): out[k] = out.get(k, 0) + v / 2
    return out


def delta_star(n, kind, g=0.5, R=None, ret=False):
    R, ng = rows(n) if R is None else R
    m = mult(n); Js = sorted(m)
    S0 = {j: cp.Variable((j + 1, j + 1), hermitian=True) for j in Js}
    S1 = {j: cp.Variable((j + 1, j + 1), hermitian=True) for j in Js}
    # real(tr(S D)) = <vec Re S, vec Re D^T> - <vec Im S, vec Im D^T>, stacked over blocks
    def coef(D):
        return np.concatenate([np.concatenate([np.real(D[j].T).ravel(), -np.imag(D[j].T).ravel()]) if j in D
                               else np.zeros(2 * (j + 1) ** 2) for j in Js])
    vec = lambda S: cp.hstack([e for j in Js for e in (cp.vec(cp.real(S[j]), order='C'), cp.vec(cp.imag(S[j]), order='C'))])
    A = np.array([coef(D) for _, _, D in R]); A[np.abs(A) < 1e-15] = 0
    Pt = coef(target(n, kind)); x0, x1 = vec(S0), vec(S1)
    p = A @ x0; q = A @ x1
    z = cp.Variable(len(R)); t = cp.Variable()
    Wm = np.zeros((ng, len(R)))
    for i, (gi, w, _) in enumerate(R): Wm[gi, i] = w
    cons = [S0[j] >> 0 for j in Js] + [S1[j] >> 0 for j in Js]
    cons += [sum(m[j] * cp.real(cp.trace(S0[j])) for j in Js) == 1, sum(m[j] * cp.real(cp.trace(S1[j])) for j in Js) == 1,
             Pt @ (x0 - x1) >= g, cp.SOC(p + q, cp.vstack([p - q, 2 * z])), Wm @ z >= t]
    pr = cp.Problem(cp.Maximize(t), cons); pr.solve(solver=cp.CLARABEL)
    if ret: return 1 - pr.value, {j: S0[j].value for j in Js}, {j: S1[j].value for j in Js}
    return 1 - pr.value


def _selftest():
    # 1) completeness: sum_J m_J-free trace of R_J equals |phi|^2 = 1 for random product vectors
    rng = np.random.default_rng(0)
    for n in (2, 3, 5):
        es = [(lambda v: v / np.linalg.norm(v))(rng.normal(size=2) + 1j * rng.normal(size=2)) for _ in range(n)]
        G = gram(es); assert abs(sum(np.trace(v) for v in G.values()) - 1) < 1e-12
    # 2) brute force at n = 4: build the coupled basis explicitly, a random invariant s, compare <phi|s|phi>
    n = 4; paths = {1: [np.eye(2)]}  # per j2: list of (2^k x (j2+1)) basis matrices, one per path
    for _ in range(n - 1):
        h = {}
        for j2, lst in paths.items():
            for B in lst:
                for up in (True, False):
                    if not up and j2 == 0: continue
                    C = getcg(j2, up); jn2 = j2 + 1 if up else j2 - 1
                    # columns of B are |j m path>, new basis vectors = (B (x) I2) C^T
                    h.setdefault(jn2, []).append(np.kron(B, np.eye(2)) @ C.T)
        paths = h
    s = np.zeros((2 ** n, 2 ** n), complex); blocks = {}
    for j2, lst in paths.items():
        M = rng.normal(size=(j2 + 1, j2 + 1)) + 1j * rng.normal(size=(j2 + 1, j2 + 1)); blocks[j2] = M @ M.conj().T
        for B in lst: s += B @ blocks[j2] @ B.conj().T
    assert np.allclose(s, s.conj().T)
    P = np.kron(np.kron(np.kron(np.eye(2)[[1, 0]], np.eye(2)), np.eye(2)), np.eye(2))  # swap check below
    for _ in range(5):
        es = [(lambda v: v / np.linalg.norm(v))(rng.normal(size=2) + 1j * rng.normal(size=2)) for _ in range(n)]
        phi = es[0]
        for e in es[1:]: phi = np.kron(phi, e)
        G = gram(es); val = sum(np.trace(blocks[j] @ G[j]) for j in G)
        assert abs(val - phi.conj() @ s @ phi) < 1e-10, (val, phi.conj() @ s @ phi)
    # permutation invariance of s (swap qubits 0, 1)
    Sw = np.zeros((16, 16))
    for i in range(16):
        b = [(i >> (3 - k)) & 1 for k in range(4)]; b[0], b[1] = b[1], b[0]
        Sw[sum(x << (3 - k) for k, x in enumerate(b)), i] = 1
    assert np.allclose(Sw @ s @ Sw.T, s)
    assert mult(4) == {4: 1, 2: 3, 0: 2}
    print("selftest ok")


if __name__ == '__main__':
    _selftest()
    g = float(sys.argv[1]); assert 0 < g < 1
    for n in map(int, sys.argv[2:]):
        t0 = time.time(); R = rows(n)
        for kind in ('prod', 'cat'):
            d = delta_star(n, kind, g=g, R=R)
            print(f"n={n:2d} {kind:4s} 1/delta*={1/d:9.2f}  16*1.5^n={16*1.5**n:9.1f}  (3/2)^(n/2)={1.5**(n/2):7.2f}  ({time.time()-t0:.0f}s)", flush=True)
