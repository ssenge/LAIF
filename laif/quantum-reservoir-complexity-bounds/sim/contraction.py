"""Contraction coefficient, in the entrywise 2-norm on traceless operators, of the partial-trace reservoir map
T(v, A) = tr_0[e^{-iH}(A (x) diag(v, 1-v))e^{iH}], H = sum_{i<j} J_ij (X_i X_j + Y_i Y_j) + gamma sum_i Z_i, qubit 0 the ancilla.
Checks:
1. The constant of the source, 2 sqrt2 (eps^2 - eps s) + 1 with s = sqrt(sqrt2 - 1), equals sqrt2 (v^2 + (1-v)^2) at the end
   of the input interval, while the bound of the argument is sqrt2 sqrt(v^2 + (1-v)^2) >= 1.
2. For J = pi on every pair (and any gamma) e^{-iH} is a product of single-qubit Z rotations: the map is unitary on the
   reservoir and its coefficient is exactly 1, for every input v.
"""
import itertools
import numpy as np
from functools import reduce

I2 = np.eye(2); X = np.array([[0, 1], [1, 0]]); Y = np.array([[0, -1j], [1j, 0]]); Z = np.diag([1., -1])


def op(P, i, q):
    return reduce(np.kron, [P if k == i else I2 for k in range(q)])


def ham(J, g, q):
    H = sum(J[a, b] * (op(X, a, q) @ op(X, b, q) + op(Y, a, q) @ op(Y, b, q)) for a, b in itertools.combinations(range(q), 2))
    return H + g * sum(op(Z, i, q) for i in range(q))


def coeff(J, g, v, n):                                   # n reservoir qubits, ancilla first
    q = n + 1; w, Vm = np.linalg.eigh(ham(J, g, q)); U = Vm @ np.diag(np.exp(-1j * w)) @ Vm.conj().T
    d = 2 ** n; sig = np.diag([v, 1 - v])
    basis = []                                           # orthonormal traceless Hermitian basis
    for a in range(d):
        for b in range(a + 1, d):
            E = np.zeros((d, d), complex); E[a, b] = E[b, a] = 1 / np.sqrt(2); basis.append(E)
            E = np.zeros((d, d), complex); E[a, b] = -1j / np.sqrt(2); E[b, a] = 1j / np.sqrt(2); basis.append(E)
    for a in range(1, d):
        D = np.zeros(d); D[:a] = 1; D[a] = -a; basis.append(np.diag(D / np.linalg.norm(D)).astype(complex))
    cols = []
    for E in basis:
        M = U @ np.kron(sig, E) @ U.conj().T
        R = M.reshape(2, d, 2, d).trace(axis1=0, axis2=2)  # trace out the ancilla
        cols.append([np.trace(F.conj().T @ R).real for F in basis])
    return np.linalg.norm(np.array(cols).T, 2)


s = np.sqrt(np.sqrt(2) - 1)
for eps in [0.01, 0.1, 0.3, 0.6]:
    v = 0.5 * (1 + s) - eps
    src = 2 * np.sqrt(2) * (eps ** 2 - eps * s) + 1
    assert abs(src - np.sqrt(2) * (v ** 2 + (1 - v) ** 2)) < 1e-12 and src < 1
    assert np.sqrt(2) * np.sqrt(v ** 2 + (1 - v) ** 2) >= 1
rng = np.random.default_rng(3)
for n in [1, 2, 3]:
    q = n + 1
    for g in [0.0, 0.37, 1.2]:
        J = np.triu(np.full((q, q), np.pi), 1)
        for v in [0.3, 0.5, 0.7]:
            c = coeff(J, g, v, n)
            assert abs(c - 1) < 1e-9, c
    J = np.triu(rng.uniform(0.2, 1.0, (q, q)), 1)
    print(f"n = {n}: coefficient 1 at J = pi; random J in [0.2, 1]: {coeff(J, 0.5, 0.5, n):.4f}")
print("all checks passed")
