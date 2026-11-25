"""Checks for the lower bound on learning a chain Hamiltonian from copies of its ground state (README, Theorem 1).
Instances: transverse-field chains H0 = -sum_x J_x Z_x Z_{x+1} - sum_x h_x X_x (open), h_x in [2, 3], J_x in [1/2, 1].
Local terms h_x = -h_x X_x - J_x Z_x Z_{x+1} (the last site has no bond). Modulation f(x) = sin(pi (x + 1/2) / n),
V = sum_x f(x) h_x, H1 = H0 + eps V = sum_x (1 + eps f(x)) h_x. Asserts, by exact diagonalization:
 (1) the gap of H0 + t V for t in [0, eps] is at least 2 (min h - (1 + eps) max J) (free-fermion bound);
 (2) 1 - |<psi0|psi1>|^2 <= 2 eps^2 Var_psi0(V) / Delta'^2 (Lemma 3);
 (3) the summation-by-parts identity of Lemma 4, (V - <V>) psi0 = sum_y g_y (S_{>y} - <S_{>y}>) psi0, g_y = f(y + 1) - f(y);
 (4) Var_psi0(V) <= max_y sum_y' |K(y, y')| * sum_y g_y^2 with K the covariance matrix of the S_{>y} (Schur test);
and prints n * Var_psi0(V), which stays bounded."""
import numpy as np, scipy.sparse as sp, scipy.sparse.linalg as sla
X = sp.csr_matrix([[0., 1], [1, 0]]); Z = sp.csr_matrix([[1., 0], [0, -1]])
def site(n, ops):
    m = sp.identity(1, format='csr')
    for i in range(n): m = sp.kron(m, ops.get(i, sp.identity(2, format='csr')), format='csr')
    return m
def ground(H):
    w, v = sla.eigsh(H, k=2, which='SA', tol=1e-12); o = np.argsort(w)
    return w[o[0]], w[o[1]] - w[o[0]], v[:, o[0]]
rng = np.random.default_rng(7)
worst2 = 0
for n in (6, 8, 10, 12, 14):
    for rep in range(3):
        h = rng.uniform(2, 3, n); J = rng.uniform(.5, 1, n - 1)
        loc = [-h[x] * site(n, {x: X}) - (J[x] * site(n, {x: Z, x + 1: Z}) if x < n - 1 else 0) for x in range(n)]
        H0 = sum(loc); f = np.sin(np.pi * (np.arange(n) + .5) / n); V = sum(fi * t for fi, t in zip(f, loc))
        E0, gap0, p0 = ground(H0); Vp = V @ p0; mV = p0 @ Vp; var = Vp @ Vp - mV ** 2
        # (3) summation by parts
        g = f[1:] - f[:-1]
        S = [sum(loc[y + 1:]) for y in range(n - 1)]
        Sc = [s @ p0 - (p0 @ (s @ p0)) * p0 for s in S]
        lhs = Vp - mV * p0; rhs = sum(gy * sc for gy, sc in zip(g, Sc)) + 0 * p0
        assert np.linalg.norm(lhs - rhs) < 1e-8, np.linalg.norm(lhs - rhs)
        # (4) Schur test
        K = np.array([[a @ b for b in Sc] for a in Sc])
        assert var <= np.max(np.abs(K).sum(1)) * (g @ g) + 1e-10
        for eps in (0.05, 0.2, 0.5):
            lb = 2 * (h.min() - (1 + eps) * J.max())
            gaps = [ground(H0 + t * V)[1] for t in np.linspace(0, eps, 5)]
            assert min(gaps) >= lb - 1e-9, (min(gaps), lb)          # (1)
            _, gap1, p1 = ground(H0 + eps * V); dp = min(gaps)
            inf = 1 - (p0 @ p1) ** 2; bound = 2 * eps ** 2 * var / dp ** 2
            assert inf <= bound + 1e-12, (inf, bound)                 # (2)
            worst2 = max(worst2, inf / bound)
        print(f"n={n:2d} gap={gap0:.3f} Var(V)={var:.4e} n*Var(V)={n*var:.4f} Schur={np.max(np.abs(K).sum(1))*(g@g):.4e} "
              f"infidelity(eps=0.2)={1-(p0 @ ground(H0 + .2 * V)[2])**2:.3e}", flush=True)
print(f"largest infidelity / Lemma 3 bound: {worst2:.4f}")
