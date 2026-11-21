"""Checks for the parallel lower bound. Coupling on omega = (k, g): g_i i.i.d. complex normal vectors, k_i i.i.d. uniform.
w2 = (g_i/|g_i|) (fresh), wH = orthonormalization (e_1..e_n) of g in order, w1 = (e_{rank(k_i)}) (one fixed basis, collisions repeat).
Z_ab = d^n E[(K_a - K_b)^dag (K_a - K_b)], K_w = |w><w| on (C^d)^{(x)n}.
Claims: Z_H2 = I - (2 - gamma) Q with Q = (d)_n E|e><e|, Q = I - R, 0 <= R <= sum_{i<j} 2 Pi_sym^{ij}/(d+1);
lambda_max(Z_1H) <= 2n(n-1)/(d+1) + gamma n(n-1)/d. The sampled Z_H2 is compared with its exact form for n = 2, 3
(R by inclusion and exclusion), the error shrinking like 1/sqrt(S); exact lambda_max are compared with the bounds."""
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
def perm_op(d, n, perm):   # permutation of n tensor factors of C^d
    D = d ** n; M = np.zeros((D, D))
    for idx in itertools.product(range(d), repeat=n):
        a = np.ravel_multi_index(idx, (d,) * n); b = np.ravel_multi_index(tuple(idx[perm[j]] for j in range(n)), (d,) * n); M[b, a] = 1
    return M
def sym(d, n, sub):   # projector onto the symmetric subspace of the factors in sub
    ps = list(itertools.permutations(sub)); out = 0
    for q in ps:
        perm = list(range(n))
        for a, b in zip(sub, q): perm[a] = b
        out = out + perm_op(d, n, perm)
    return out / len(ps)
def R_exact(d, n):   # average sum over index tuples with a repeat, by inclusion and exclusion (n = 2, 3)
    R = sum(2 * sym(d, n, [i, j]) / (d + 1) for i in range(n) for j in range(i + 1, n))
    if n == 3: R = R - 12 * sym(d, 3, [0, 1, 2]) / ((d + 1) * (d + 2))
    return R
lam = lambda M: np.linalg.eigvalsh((M + M.conj().T) / 2).max()
# exact Z_H2 = (gamma - 1) I + (2 - gamma) R; the sampled matrix must approach it like 1/sqrt(S)
for d, n in ((3, 2), (5, 2), (3, 3), (4, 3)):
    gamma = d ** n / math.prod(range(d - n + 1, d + 1)); exact = (gamma - 1) * np.eye(d ** n) + (2 - gamma) * R_exact(d, n)
    errs = [np.linalg.norm(run(d, n, S)[2] - exact, 2) for S in (10000, 160000)]
    print(f"d={d} n={n}: |Z_H2 - exact| at S = 1e4, 1.6e5: {errs[0]:.4f}, {errs[1]:.4f}")
    assert errs[1] < errs[0] / 2.5 and errs[1] < 0.05
# exact lambda_max(Z_H2) against the bound (gamma - 1) + (2 - gamma) n(n-1)/(d+1), where gamma <= 2
for d, n in ((3, 2), (4, 2), (6, 2), (10, 2), (6, 3), (8, 3)):
    gamma = d ** n / math.prod(range(d - n + 1, d + 1)); assert gamma <= 2
    lz = lam((gamma - 1) * np.eye(d ** n) + (2 - gamma) * R_exact(d, n)); bnd = (gamma - 1) + (2 - gamma) * n * (n - 1) / (d + 1)
    print(f"d={d} n={n}: exact lambda_max(Z_H2) = {lz:.4f} <= {bnd:.4f}"); assert lz <= bnd + 1e-12
    if n == 2: assert abs(lz - 3 / (d + 1)) < 1e-12
# Z_1H for n = 2: lambda_max = 3/(d+1) exactly, below the bound 2n(n-1)/(d+1) + gamma n(n-1)/d
for d in (3, 5):
    l1 = lam(run(d, 2, 160000)[1]); bnd = 4 / (d + 1) + 2 * d / ((d - 1) * d)
    print(f"d={d} n=2: sampled lambda_max(Z_1H) = {l1:.4f}, exact 3/(d+1) = {3 / (d + 1):.4f}, bound {bnd:.4f}"); assert abs(l1 - 3 / (d + 1)) < 0.03
print("parallel checks passed")
