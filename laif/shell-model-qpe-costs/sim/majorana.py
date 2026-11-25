"""Pauli (Majorana) 1-norm of the shell-model Hamiltonian, with symmetry shifts optimized for it.
a_p = (g_{2p} + i g_{2p+1}) / 2. Under Jordan-Wigner each Majorana monomial is one Pauli string, so the 1-norm of the
Majorana expansion without the identity term is the 1-norm of the Pauli LCU.
usage: python majorana.py snt A Z N"""
import sys, numpy as np, scipy.sparse.linalg as sla
from scipy.optimize import linprog
from shell import build, basis, hamiltonian
from shifts import operators, lam, l1_fit

def mono_mul(a, b):
    """product of two sorted Majorana monomials (tuples); returns (sign, monomial)"""
    lst = list(a) + list(b); sg = 1
    # bubble sort with anticommutation, g_i g_i = 1
    i = 0; arr = lst
    changed = True
    while changed:
        changed = False
        for k in range(len(arr) - 1):
            if arr[k] > arr[k + 1]:
                arr[k], arr[k + 1] = arr[k + 1], arr[k]; sg = -sg; changed = True
    out = []
    for x in arr:
        if out and out[-1] == x: out.pop()
        else: out.append(x)
    return sg, tuple(out)

def ladder(p, dag):    # a_p or a_p^dag as {monomial: coeff}
    return {(2 * p,): 0.5, (2 * p + 1,): (-0.5j if dag else 0.5j)}

def expand(ops):
    acc = {(): 1.0}
    for (p, dag) in ops:
        new = {}
        for m1, c1 in acc.items():
            for m2, c2 in ladder(p, dag).items():
                s, m = mono_mul(m1, m2); new[m] = new.get(m, 0) + s * c1 * c2
        acc = new
    return acc

def majorana_terms(t, W):
    """dict monomial -> coefficient for sum t_p n_p + sum W a+p a+q a_s a_r"""
    H = {}
    def add(d, c):
        for m, v in d.items(): H[m] = H.get(m, 0) + c * v
    for p, tp in enumerate(t):
        if tp: add(expand([(p, True), (p, False)]), tp)
    for (p, q, r, s), v in W.items():
        add(expand([(p, True), (q, True), (s, False), (r, False)]), v)
    for m, v in H.items():        # hermitian: a monomial of length k is hermitian times i^(k(k-1)/2)
        assert abs((v / 1j ** (len(m) * (len(m) - 1) // 2)).imag) < 1e-9, (m, v)
    return H

def pauli_norm(H):
    return sum(abs(v) for m, v in H.items() if m != () and abs(v) > 1e-12)

if __name__ == "__main__":
    path, A, Z, N = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    states, orbs, t, W = build(path, A)
    ops = operators(states, orbs)
    names = ["Np", "Nn", "Np2", "Nn2", "NpNn", "Jz", "Jz2", "J2", "T2"]
    target = {"J2": 0, "T2": abs(Z - N) / 2 * (abs(Z - N) / 2 + 1), "Np2": Z * Z, "Nn2": N * N, "NpNn": Z * N, "Jz2": 0, "Np": Z, "Nn": N, "Jz": 0}
    H0 = majorana_terms(t, W)
    Hk = [majorana_terms(*ops[k]) for k in names]
    keys = sorted(set(H0).union(*[set(h) for h in Hk]) - {()})
    b = np.array([H0.get(m, 0) for m in keys]); A_ = np.column_stack([[h.get(m, 0) for m in keys] for h in Hk])
    # real parametrization: coefficients are real or purely imaginary per monomial; use magnitudes with fixed phase
    ph = np.array([1 if abs(np.imag(x)) < 1e-12 and abs(np.real(x)) > 0 else (1j if abs(np.imag(x)) > 0 else 1) for x in b])
    for col in A_.T:
        nz = np.abs(col) > 1e-12
        ph = np.where((np.abs(b) < 1e-12) & nz, np.where(np.abs(np.imag(col)) > 1e-12, 1j, 1), ph)
    br = np.real(b / ph); Ar = np.real(A_ / ph[:, None])
    assert np.allclose(br * ph, b) and np.allclose(Ar * ph[:, None], A_)
    m, nc = Ar.shape
    print("Pauli terms %d, Pauli 1-norm unshifted %.2f (fermionic-operator LCU of the source: %.2f)" % (m, np.abs(br).sum(), lam(t, W)))
    cost = np.concatenate([np.zeros(nc), np.ones(m)])
    c = l1_fit(br, Ar); r = br - Ar @ c
    print("shifts", dict(zip(names, np.round(c, 4))))
    print("Pauli 1-norm shifted %.2f, ratio to source %.3f, nonzero Pauli terms %d" % (np.abs(r).sum(), lam(t, W) / np.abs(r).sum(), int((np.abs(r) > 1e-9).sum())))
    # exact check: rebuild the shifted fermionic Hamiltonian and compare ground energies
    t2 = t - sum(ci * ops[k][0] for ci, k in zip(c, names)); W2 = dict(W)
    for ci, k in zip(c, names):
        for q, v in ops[k][1].items(): W2[q] = W2.get(q, 0) - ci * v
    B = basis(states, orbs, Z, N, 0)
    e = sla.eigsh(hamiltonian(states, t, W, B), k=1, which="SA")[0][0]
    e2 = sla.eigsh(hamiltonian(states, t2, W2, B), k=1, which="SA")[0][0]
    const = sum(ci * target[k] for ci, k in zip(c, names))
    assert abs(e2 + const - e) < 1e-6
    H2 = majorana_terms(t2, W2); assert abs(pauli_norm(H2) - np.abs(r).sum()) < 1e-6
    print("E0 %.4f reproduced after the shift (constant %.4f)" % (e, const))
