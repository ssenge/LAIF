"""Forced second-order leak for every regular one-copy-per-step protocol (Theorem 4).
Any step family Lambda_Delta = Tr_23 + Delta G + Delta^2 E + O(Delta^3) that is first-order consistent has the same G
(the polarization of Lind_L), hence the same Choi matrix C1. Complete positivity forces, by a Schur complement,
e+ C2 e >= e+ C1 C0^+ C1 e on vectors e with C0 e = 0 and C1 e in range(C0). For L = |0><0| and e_i = |0>|L> (x) |i>,
i != 0, the bound is 1/4 per output, so the leak out of |0> is at least (d-1)/4 per Delta^2. WML attains it.
Choi convention: C[(a, i), (b, j)] = <i| Lambda(|a><b|) |j>, a, b on S (x) P (system first), i, j on S."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "RAYON_NUM_THREADS"):
    os.environ[_v] = "1"
import numpy as np
from wml import error_map

def G_apply(X, d):
    """G(X) for X on S (x) P (P = C^d (x) C^d, |L> = (L (x) I)|Gamma>): the unique linear extension of
    rho (x) |L><L'| -> L rho L'+ - (1/2)(L'+ L rho + rho L'+ L)."""
    D = d**3; X = X.reshape(d, d * d, d, d * d)
    out = np.zeros((d, d), complex)
    for p in range(d * d):
        for q in range(d * d):
            Lp = np.zeros((d, d)); Lp[p // d, p % d] = 1      # |p> = |row>_2|col>_3  <->  matrix unit
            Lq = np.zeros((d, d)); Lq[q // d, q % d] = 1
            rho = X[:, p, :, q]
            out += Lp @ rho @ Lq.T - 0.5 * (Lq.T @ Lp @ rho + rho @ Lq.T @ Lp)
    return out

def choi(apply, d):
    D = d**3; C = np.zeros((D * d, D * d), complex)
    for a in range(D):
        for b in range(D):
            X = np.zeros((D, D)); X[a, b] = 1
            C[a * d:(a + 1) * d, b * d:(b + 1) * d] = apply(X)
    return C

def tr23(X, d):
    return np.einsum("apbp->ab", X.reshape(d, d * d, d, d * d))

for d in range(2, 5):
    D = d**3
    C0 = choi(lambda X: tr23(X, d), d); C1 = choi(lambda X: G_apply(X, d), d)
    # G reproduces Lind_L on product inputs
    rng = np.random.default_rng(d); L = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); L /= np.linalg.norm(L)
    r = rng.normal(size=(d, d)); r = r @ r.T; r /= np.trace(r)
    vL = np.kron(L, np.eye(d)) @ np.eye(d).reshape(-1); X = np.kron(r, np.outer(vL, vL.conj()))
    LL = L.conj().T @ L; ref = L @ r @ L.conj().T - 0.5 * (LL @ r + r @ LL)
    assert np.abs(G_apply(X, d) - ref).max() < 1e-12
    C0p = np.linalg.pinv(C0); PN = np.eye(D * d) - C0 @ C0p
    s = 0 * d * d + 0          # input |0>_1 |L> with L = |0><0|: |0>_2 |0>_3
    leak = 0.0
    for i in range(1, d):
        e = np.zeros(D * d); e[s * d + i] = 1
        assert np.abs(C0 @ e).max() < 1e-12 and np.abs(PN @ (C1 @ e)).max() < 1e-12      # e is admissible
        f = (C1 @ e).conj() @ C0p @ (C1 @ e)
        assert abs(f - 0.25) < 1e-12, f
        leak += f.real
    P = np.zeros((d, d), complex); P[0, 0] = 1
    E0 = (error_map(P) @ np.diag(np.eye(d)[0]).reshape(-1, order="F")).reshape(d, d, order="F")
    wml_leak = sum(E0[i, i].real for i in range(1, d))
    print("d=%d  forced leak out of |0> per Delta^2: %.6f = (d-1)/4 = %.6f;  WML leak %.6f" % (d, leak, (d - 1) / 4, wml_leak))
    assert abs(leak - (d - 1) / 4) < 1e-12 and abs(wml_leak - leak) < 1e-12
