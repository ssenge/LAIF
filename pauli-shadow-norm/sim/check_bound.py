# Checks of Theorem 1 (NOTES.md): for every N-qubit operator O and state sigma, with random Pauli basis
# measurements and the product estimator rhohat = (x)_i (3|b_i x_i><b_i x_i| - I),
#     E_{B, x ~ sigma} |Tr(O rhohat)|^2 <= c^N Tr(O^dag O),   c = 1 + 1/sqrt 2,
# with equality for product O and sigma. Also the single-qubit closed form and the product step.
import itertools
import numpy as np
import shadow as S
import herm as Hm

c = 1 + 1 / np.sqrt(2)
rng = np.random.default_rng(7)


def L1(r):
    """single-qubit map in the normalized Pauli basis {I, X, Y, Z}/sqrt2, sigma with Bloch vector r."""
    m = np.zeros((4, 4))
    for b in range(3):
        for s in (1, -1):
            v = np.zeros(4); v[0] = 1; v[1 + b] = 3 * s; v /= np.sqrt(2)          # vec(rhohat) in that basis
            m += (1 + s * r[b]) / 2 * np.outer(v, v) / 3
    return m


# 1. closed form L1(sigma) = [[1/2, r^T/2], [r/2, 3/2 I]], top eigenvalue 1 + sqrt(1 + |r|^2)/2 <= c
for _ in range(200):
    r = rng.normal(size=3); r *= rng.uniform(0, 1) / np.linalg.norm(r)
    m = L1(r)
    assert np.allclose(m, np.block([[np.array([[0.5]]), r[None, :] / 2], [r[:, None] / 2, 1.5 * np.eye(3)]]))
    assert abs(np.linalg.eigvalsh(m)[-1] - (1 + np.sqrt(1 + r @ r) / 2)) < 1e-12
print("single qubit: nu(L1) = 1 + 1/sqrt2 =", c)


def second_moment(O, sigma, Us, FN):
    """E_{B, x ~ sigma} |Tr(O rhohat_{B,x})|^2 for self-adjoint or general O (real and imaginary parts)."""
    tot = 0
    for part in (0.5 * (O + O.conj().T), -0.5j * (O - O.conj().T)):    # O = H1 + i H2, |Tr(O rh)|^2 = Tr(H1 rh)^2 + Tr(H2 rh)^2
        M, _ = S.M_of(part, Us, FN)
        tot += np.trace(sigma @ M).real
    return tot


# 2. random operators and entangled states: never above the bound
for N in (1, 2, 3, 4):
    Us, FN = S.setup(N)
    d = 2 ** N
    worst = 0
    for _ in range(60):
        O = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        if rng.uniform() < 0.5:
            O = O + O.conj().T
        k = rng.integers(1, d + 1)
        A = rng.normal(size=(d, k)) + 1j * rng.normal(size=(d, k)); sigma = A @ A.conj().T; sigma /= np.trace(sigma)
        val = second_moment(O, sigma, Us, FN) / (c ** N * np.trace(O.conj().T @ O).real)
        assert val <= 1 + 1e-10
        worst = max(worst, val)
    # equality: product of the single-qubit optimizers, O_1 = (I + sqrt2 ... ) from the top eigenvector of L1(z)
    w, V = np.linalg.eigh(L1(np.array([0, 0, 1.0])))
    a = V[:, -1]
    O1 = (a[0] * np.eye(2) + a[3] * np.diag([1.0, -1.0])) / np.sqrt(2)
    s1 = np.diag([1.0, 0.0])
    O, sigma = np.array([[1.0]]), np.array([[1.0]])
    for _ in range(N):
        O, sigma = np.kron(O, O1), np.kron(sigma, s1)
    eq = second_moment(O, sigma, Us, FN) / (c ** N * np.trace(O @ O).real)
    assert abs(eq - 1) < 1e-10
    print(f"N={N}: max ratio over random (O, sigma) {worst:.4f}; product optimizer attains 1 (={eq:.12f})")

# 3. the search over self-adjoint O and states sigma does not pass c^N
for N in (2, 3):
    b = Hm.run(N, 4, 40, rng)
    assert b <= c ** N * (1 + 1e-9)
    print(f"N={N}: alternating search {b:.6f} vs c^N {c ** N:.6f}")
print("bound checks: ok")
