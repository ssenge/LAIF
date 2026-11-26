"""Theorem 4 with k fresh copies per step. A step Lambda_Delta: S (x) P^k -> S with Lambda_Delta(rho (x) pi_L^k)
= rho + Delta Lind_L(rho) + O(Delta^2). The first-order map G is forced only on L(S) (x) L(Sym^k P), since the operators
|v><v|^(x)k span L(Sym^k P); there it equals Gsym = (1/k) sum_j G1 on copy j (x) Tr on the others. The Schur bound reads
<i|E(|0><0| (x) pi_L^k)|i> >= (1/d^2) ||Pi_Sym w||^2 with w(p) = sum_m <m| G(|m, p><0, L^k|) |i> (Choi of Tr_P^k is
|Gamma><Gamma| (x) I). For L = |0><0| this is 1/(4k) per output state i != 0, so a step leaks at least (d-1) Delta^2/(4k),
and k consecutive WML steps of time Delta/k attain it."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "RAYON_NUM_THREADS"):
    os.environ[_v] = "1"
import itertools, math
import numpy as np
from wml import step

def G1(rho, Lp, Lq):            # G on rho (x) |Lp><Lq|: polarization of Lind
    return Lp @ rho @ Lq.conj().T - 0.5 * (Lq.conj().T @ Lp @ rho + rho @ Lq.conj().T @ Lp)

def unit(d, idx):               # matrix unit for program basis index idx = row * d + col
    M = np.zeros((d, d)); M[idx // d, idx % d] = 1; return M

def w_vector(d, k, i, which="sym"):
    """w(p) over the program basis p of P^k (P = C^{d^2}), for L = |0><0| (|L> = basis index 0) and output i.
    which = "sym": Gsym; which = "first": G1 on copy 1 (x) Tr on the others (agrees with Gsym only on Sym^k)."""
    P = d * d; L = unit(d, 0)
    w = np.zeros(P**k, complex)
    for n, p in enumerate(itertools.product(range(P), repeat=k)):
        copies = range(k) if which == "sym" else [0]
        acc = 0.0
        for j in copies:
            if any(p[l] != 0 for l in range(k) if l != j): continue        # Tr of |p_l><L| is <L|p_l>
            for m in range(d):
                rho = np.zeros((d, d)); rho[m, 0] = 1                       # |m><0| on the system
                acc += G1(rho, unit(d, p[j]), L)[m, i]
        w[n] = acc / len(copies)
    return w

def admissible(d, k, i):
    """C1 e lies in range(C0) = span{sum_m |m, p>|m>}: <y|Gsym(|m, p><0, L^k|)|i> vanishes for y != m and does not
    depend on m for y = m (C0 e = 0 holds since the output i differs from the system input 0)."""
    P = d * d; L = unit(d, 0)
    for p in itertools.product(range(P), repeat=k):
        col = np.zeros((d, d), complex)          # col[m, y]
        for j in range(k):
            if any(p[l] != 0 for l in range(k) if l != j): continue
            for m in range(d):
                rho = np.zeros((d, d)); rho[m, 0] = 1
                col[m] += G1(rho, unit(d, p[j]), L)[:, i] / k
        if np.abs(col - np.diag(np.diag(col))).max() > 1e-12 or np.ptp(np.diag(col)) > 1e-12: return False
    return True

def sym_projector(P, k):
    N = P**k; Pi = np.zeros((N, N))
    idx = {p: n for n, p in enumerate(itertools.product(range(P), repeat=k))}
    for p, n in idx.items():
        for s in itertools.permutations(range(k)):
            Pi[idx[tuple(p[x] for x in s)], n] += 1
    return Pi / math.factorial(k)

for d, k in ((2, 1), (3, 1), (2, 2), (3, 2), (4, 2), (2, 3), (3, 3)):
    Pi = sym_projector(d * d, k)
    assert np.abs(Pi @ Pi - Pi).max() < 1e-12
    leak = 0.0
    for i in range(1, d):
        assert admissible(d, k, i)
        ws, wf = w_vector(d, k, i, "sym"), w_vector(d, k, i, "first")
        a, b = np.linalg.norm(Pi @ ws)**2 / d**2, np.linalg.norm(Pi @ wf)**2 / d**2
        assert abs(a - b) < 1e-12                    # the forced part does not depend on the representative of G
        assert abs(a - 1 / (4 * k)) < 1e-12, (d, k, a)
        leak += a
    # attainment: k WML steps of time Delta/k, input |0><0|, leak per Delta^2
    Lm = unit(d, 0); Delta = 1e-3
    Phi = np.linalg.matrix_power(step(Lm, Delta / k), k)
    out = (Phi @ np.diag(np.eye(d)[0]).reshape(-1, order="F")).reshape(d, d, order="F")
    wml_leak = (1 - out[0, 0].real) / Delta**2
    print("d=%d k=%d  forced leak per Delta^2 %.6f = (d-1)/(4k) = %.6f;  k WML steps of Delta/k: %.6f"
          % (d, k, leak, (d - 1) / (4 * k), wml_leak))
    assert abs(leak - (d - 1) / (4 * k)) < 1e-12 and abs(wml_leak - leak) < 1e-3 * (d - 1)
