"""Checks for the gradient instance of Lemma 1.

QNN(theta; rho) = tr(Z_0 U(theta) (|0><0| (x) rho) U(theta)^dag),
U(theta) = prod_k exp(i theta_k Y_0 (x) P_k) H_0, over all non-identity Paulis P_k.
Claim: d QNN / d theta_k at theta = 0 equals 2 tr(P_k rho).
"""
import itertools
import numpy as np
from scipy.linalg import expm

I2 = np.eye(2)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]])
Z = np.diag([1.0 + 0j, -1.0])
H = np.array([[1, 1], [1, -1]], dtype=complex) / np.sqrt(2)


def kron(*ms):
    out = np.eye(1)
    for m in ms:
        out = np.kron(out, m)
    return out


def paulis(n):
    for p in itertools.product([I2, X, Y, Z], repeat=n):
        yield kron(*p)


def random_state(n, rng):
    g = rng.normal(size=(2**n, 2**n)) + 1j * rng.normal(size=(2**n, 2**n))
    r = g @ g.conj().T
    return r / np.trace(r)


def qnn(theta, gens, rho):
    u = kron(H, np.eye(len(rho)))
    for t, g in zip(theta, gens):
        u = expm(1j * t * g) @ u
    zero = np.diag([1.0, 0.0])
    s = u @ kron(zero, rho) @ u.conj().T
    return np.real(np.trace(kron(Z, np.eye(len(rho))) @ s))


def check(n, seed=0, h=1e-5):
    rng = np.random.default_rng(seed)
    rho = random_state(n, rng)
    ps = list(paulis(n))[1:]
    gens = [kron(Y, p) for p in ps]
    m = len(gens)
    err = 0.0
    for k, p in enumerate(ps):
        e = np.zeros(m)
        e[k] = h
        fd = (qnn(e, gens, rho) - qnn(-e, gens, rho)) / (2 * h)
        err = max(err, abs(fd - 2 * np.real(np.trace(p @ rho))))
    assert err < 1e-7, err
    # the derivative at 0 does not depend on the gate order
    perm = rng.permutation(m)
    k = int(rng.integers(m))
    e = np.zeros(m)
    e[k] = h
    g2 = [gens[j] for j in perm]
    e2 = e[perm]
    fd2 = (qnn(e2, g2, rho) - qnn(-e2, g2, rho)) / (2 * h)
    assert abs(fd2 - 2 * np.real(np.trace(ps[k] @ rho))) < 1e-7
    print(f"n = {n}: M = {m} parameters, max |dQNN/dtheta_k - 2 tr(P_k rho)| = {err:.1e}")


if __name__ == "__main__":
    for n in (1, 2, 3):
        check(n, seed=n)
    print("gradient identity of Lemma 1 holds")
