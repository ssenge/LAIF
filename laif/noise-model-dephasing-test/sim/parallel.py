"""Checks for the parallel lower bound. Coupling on omega = (k, g): g_i i.i.d. complex normal vectors, k_i i.i.d. uniform.
w2 = (g_i/|g_i|) (fresh), wH = orthonormalization (e_1..e_n) of g in order, w1 = (e_{rank(k_i)}) (one fixed basis, collisions repeat).
Z_ab = d^n E[(K_a - K_b)^dag (K_a - K_b)], K_w = |w><w| on (C^d)^{(x)n}.
Claims: Z_H2 = I - (2 - gamma) Q with Q = (d)_n E|e><e|, Q = I - R, 0 <= R <= sum_{i<j} 2 Pi_sym^{ij}/(d+1);
lambda_max(Z_1H) <= 2n(n-1)/(d+1) + gamma n(n-1)/d. Monte Carlo with S samples, tolerance from the sampling error."""
import itertools, math
import numpy as np
rng = np.random.default_rng(2)
def gs(G):
    Q, R = np.linalg.qr(G); return Q * (np.diag(R) / abs(np.diag(R)))   # orthonormalization of the columns in order, positive diagonal
def kron(vs):
    out = np.array([1.0 + 0j])
    for v in vs: out = np.kron(out, v)
    return out
def run(d, n, S):
    D = d ** n; Z12 = np.zeros((D, D), complex); Z1H = np.zeros((D, D), complex); ZH2 = np.zeros((D, D), complex); EQ = np.zeros((D, D), complex)
    for _ in range(S):
        G = (rng.standard_normal((d, n)) + 1j * rng.standard_normal((d, n))) / math.sqrt(2)
        k = rng.integers(0, d, n); order = list(dict.fromkeys(k)); first = [int(np.where(k == c)[0][0]) for c in order]
        E1 = gs(G[:, first]); w1 = kron([E1[:, order.index(c)] for c in k])
        EH = gs(G); wH = kron([EH[:, i] for i in range(n)]); w2 = kron([G[:, i] / np.linalg.norm(G[:, i]) for i in range(n)])
        def z(a, b):   # (K_a - K_b)^dag (K_a - K_b) for unit a, b
            ab = np.vdot(a, b); return np.outer(a, a.conj()) + np.outer(b, b.conj()) - ab * np.outer(a, b.conj()) - ab.conjugate() * np.outer(b, a.conj())
        Z12 += z(w1, w2); Z1H += z(w1, wH); ZH2 += z(wH, w2); EQ += np.outer(wH, wH.conj())
    f = d ** n / S; Z12 *= f; Z1H *= f; ZH2 *= f
    gamma = d ** n / math.prod(range(d - n + 1, d + 1)); Q = EQ / S * math.prod(range(d - n + 1, d + 1))
    return Z12, Z1H, ZH2, Q, gamma
for d, n, S in ((3, 2, 200000), (4, 2, 200000), (6, 2, 100000), (3, 3, 50000), (6, 3, 30000)):
    Z12, Z1H, ZH2, Q, gamma = run(d, n, S); I = np.eye(d ** n)
    err = np.linalg.norm(ZH2 - (I - (2 - gamma) * Q), 2)
    lam = lambda M: np.linalg.eigvalsh((M + M.conj().T) / 2).max()
    b = (gamma - 1) + (2 - gamma) * n * (n - 1) / (d + 1); a = 2 * n * (n - 1) / (d + 1) + gamma * n * (n - 1) / d
    tol = 6 * d ** n / math.sqrt(S)
    print(f"d={d} n={n}: |Z_H2 - (I-(2-g)Q)| = {err:.3f} (tol {tol:.3f}); lam Z_H2 {lam(ZH2):.4f} <= {b:.4f}; lam Z_1H {lam(Z1H):.4f} <= {a:.4f}; lam Z_12 {lam(Z12):.4f}")
    assert err < tol
    if gamma <= 2: assert lam(ZH2) <= b + tol and lam(Z1H) <= a + tol   # the bounds are stated for gamma <= 2
    if n == 2:   # exact spectrum of Z_H2: gamma - 1 on the antisymmetric part, 3/(d+1) on the symmetric part
        ev = np.sort(np.linalg.eigvalsh((ZH2 + ZH2.conj().T) / 2)); m_a = d * (d - 1) // 2
        assert abs(ev[-1] - max(gamma - 1, 3 / (d + 1))) < tol
print("parallel checks passed")
# exact form for n = 2: Q = I - 2 Pi_sym/(d+1), so Z_H2 = (gamma - 1) I + (2 - gamma) 2 Pi_sym/(d+1); the error must shrink like 1/sqrt(S)
for d in (3, 5):
    I = np.eye(d * d); F_ = np.zeros((d * d, d * d))
    for i in range(d):
        for j in range(d): F_[i * d + j, j * d + i] = 1
    Psym = (I + F_) / 2; gamma = d / (d - 1); exact = (gamma - 1) * I + (2 - gamma) * 2 * Psym / (d + 1)
    errs = [np.linalg.norm(run(d, 2, S)[2] - exact, 2) for S in (20000, 320000)]
    print(f"d={d}: |Z_H2 - exact| at S = 2e4, 3.2e5: {errs[0]:.4f}, {errs[1]:.4f}")
    assert errs[1] < errs[0] / 2.5 and errs[1] < 0.02
print("exact n = 2 form confirmed")
