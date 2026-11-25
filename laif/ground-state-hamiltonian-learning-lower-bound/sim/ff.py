"""Free-fermion check of Var_psi0(V) ~ 1/n for the transverse-field chains of lower.py, up to n = 400.
Majorana form: H = (i/4) a^T A a with A real antisymmetric; V likewise with B. Var(V) is computed from the ground-state
covariance by Wick's theorem; the formula is asserted against exact diagonalization at n = 6 and 8."""
import numpy as np, itertools
def majorana_mats(h, J, w):
    n = len(h); A = np.zeros((2 * n, 2 * n))
    for x in range(n):  # -w_x h_x X_x = -w_x h_x (-i a_{2x} a_{2x+1}) -> i/4 * 2 * (w h) (a_{2x} a_{2x+1} - a_{2x+1} a_{2x})
        A[2 * x, 2 * x + 1] += 2 * w[x] * h[x]; A[2 * x + 1, 2 * x] -= 2 * w[x] * h[x]
        if x < n - 1:  # -w_x J_x Z_x Z_{x+1} = -w_x J_x (-i a_{2x+1} a_{2x+2})
            A[2 * x + 1, 2 * x + 2] += 2 * w[x] * J[x]; A[2 * x + 2, 2 * x + 1] -= 2 * w[x] * J[x]
    return A
def var_ff(h, J, f):
    n = len(h); A = majorana_mats(h, J, np.ones(n)); B = majorana_mats(h, J, f)
    ev, U = np.linalg.eigh(1j * A); G = U @ np.diag(-np.sign(ev)) @ U.conj().T   # G_jk = <a_j a_k> - delta_jk, i.e. i*Gamma
    C = np.eye(2 * n) + G                                                          # C_jk = <a_j a_k>
    # Q = (i/4) sum B_jk a_j a_k; Var(Q) = -(1/16) sum B_jk B_lm (<a_j a_k a_l a_m> - <a_j a_k><a_l a_m>)
    # Wick: <jklm> - <jk><lm> = -<jl><km> + <jm><kl>
    T1 = np.trace(B.T @ C @ B @ C.T); T2 = np.trace(B.T @ C @ B.T @ C.T)  # sums B_jk B_lm C_jl C_km and B_jk B_lm C_jm C_kl
    return (-(1 / 16) * (-T1 + T2)).real
def var_ed(h, J, f):
    import scipy.sparse as sp, scipy.sparse.linalg as sla
    X = sp.csr_matrix([[0., 1], [1, 0]]); Z = sp.csr_matrix([[1., 0], [0, -1]]); n = len(h)
    def site(ops):
        m = sp.identity(1, format='csr')
        for i in range(n): m = sp.kron(m, ops.get(i, sp.identity(2, format='csr')), format='csr')
        return m
    loc = [-h[x] * site({x: X}) - (J[x] * site({x: Z, x + 1: Z}) if x < n - 1 else 0) for x in range(n)]
    w, v = sla.eigsh(sum(loc), k=1, which='SA'); p = v[:, 0]; Vp = sum(fi * t for fi, t in zip(f, loc)) @ p
    return Vp @ Vp - (p @ Vp) ** 2
rng = np.random.default_rng(11)
for n in (6, 8):
    h = rng.uniform(2, 3, n); J = rng.uniform(.5, 1, n - 1); f = np.sin(np.pi * (np.arange(n) + .5) / n)
    a, b = var_ff(h, J, f), var_ed(h, J, f); assert abs(a - b) < 1e-9, (a, b)
print("Wick formula matches exact diagonalization at n = 6, 8")
for n in (10, 25, 50, 100, 200, 400, 800):
    r = []
    for rep in range(3):
        h = rng.uniform(2, 3, n); J = rng.uniform(.5, 1, n - 1); f = np.sin(np.pi * (np.arange(n) + .5) / n)
        r.append(n * var_ff(h, J, f))
    print(f"n={n:3d} n*Var(V) = {', '.join(f'{x:.4f}' for x in r)}", flush=True)
