"""Checks for the tangent count of re-uploading circuits (README.md).

The tangent-coefficient functions h_j(x) = (<r|U(x)^dag d_j U(x)|0>)_{r>=1} are sampled
at 4E+7 points, which determines trigonometric polynomials of degree <= E exactly, and
the dimension of their real span is computed as a matrix rank.
"""
import itertools

import numpy as np

rng = np.random.default_rng(7)
PAULI = [np.eye(2), np.array([[0, 1], [1, 0]]), np.array([[0, -1j], [1j, 0]]), np.diag([1.0, -1.0])]


def pauli_words(n):
    out = []
    for w in itertools.product(range(4), repeat=n):
        if any(w):
            m = np.array([[1.0]])
            for a in w:
                m = np.kron(m, PAULI[a])
            out.append(m)
    return out


def uniform_unitary(d):
    z = (rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / abs(np.diag(r)))


def encoding(x, n, qubits):
    s = np.array([[1.0]])
    for q in range(n):
        g = np.cos(x / 2) * np.eye(2) - 1j * np.sin(x / 2) * PAULI[1] if q in qubits else np.eye(2)
        s = np.kron(s, g)
    return s


def tangent_dim(n, layers, gates):
    """layers[k] = encoded qubits of layer k; gates = L+1 blocks, each a list of unitaries."""
    d = 2 ** n
    words = pauli_words(n)
    E = sum(len(q) for q in layers)
    xs = np.linspace(0, 2 * np.pi, 4 * E + 7, endpoint=False)
    rows, per_block = [], []
    for ell, block in enumerate(gates):
        for g in range(len(block)):
            for w in words:
                vals = []
                for x in xs:
                    pre = np.eye(d)
                    for k in range(ell):
                        for G in gates[k]:
                            pre = G @ pre
                        pre = encoding(x, n, layers[k]) @ pre
                    for G in block[:g]:
                        pre = G @ pre
                    vals.append((pre.conj().T @ w @ pre[:, 0])[1:])
                v = 1j * np.array(vals).ravel()
                rows.append(np.concatenate([v.real, v.imag]))
        s = np.linalg.svd(np.array(rows), compute_uv=False)
        per_block.append(int(np.sum(s > 1e-9 * s[0])))
    return per_block


def bound(n, E):
    return 2 * (2 ** n - 1) * (E + 1)


def random_gates(d, L, per_block=1):
    return [[uniform_unitary(d) for _ in range(per_block)] for _ in range(L + 1)]


def main():
    print("one encoded qubit (ancilla layout), uniform gates: dim T after each block")
    for n, Emax in [(1, 5), (2, 6), (3, 4)]:
        for E in range(1, Emax + 1):
            dims = tangent_dim(n, [[0]] * E, random_gates(2 ** n, E))
            assert dims == [2 * (2 ** n - 1) * (ell + 1) for ell in range(E + 1)], dims
        print(f"   N={n}: dim T = 2(2^N-1)(E+1) for E = 1..{Emax}, increment {2 * (2 ** n - 1)} per block")
    dims = tangent_dim(2, [[0]] * 3, random_gates(4, 3, per_block=3))
    assert dims[-1] == bound(2, 3)
    print(f"   N=2, E=3, three gates per block: {dims[-1]}")

    print("other layouts, uniform gates: dim T <= 2(2^N-1)(E+1)")
    for n, layers in [(2, [[0, 1]] * 2), (2, [[0, 1]] * 3), (2, [[0], [0, 1], [1]]), (3, [[0, 1]] * 2),
                      (3, [[0, 1, 2], [1]]), (3, [[2], [0, 2], [1]])]:
        E = sum(len(q) for q in layers)
        dims = tangent_dim(n, layers, random_gates(2 ** n, len(layers)))
        assert dims[-1] <= bound(n, E)
        print(f"   N={n} layers={layers}: {dims[-1]} <= {bound(n, E)}")
    E = 4
    dims = tangent_dim(2, [[0, 1]] * (E // 2), random_gates(4, E // 2))
    assert dims[-1] == 5 * E + 6
    print(f"   parallel circuit N=2, E={E}: {dims[-1]} = 5E+6")

    print("special gates: dim T <= 2(2^N-1)(E+1)")
    H = np.array([[1, 1], [1, -1]]) / np.sqrt(2)
    cnot = np.eye(4)[[0, 1, 3, 2]]
    specials = {
        "identity": lambda: np.eye(4),
        "H x I": lambda: np.kron(H, np.eye(2)),
        "CNOT (H x H)": lambda: cnot @ np.kron(H, H),
        "mixed": lambda: [np.eye(4), np.kron(H, np.eye(2)), cnot, uniform_unitary(4)][rng.integers(4)],
    }
    for name, f in specials.items():
        for E in (2, 4):
            dims = tangent_dim(2, [[0]] * E, [[f()] for _ in range(E + 1)])
            assert dims[-1] <= bound(2, E)
            print(f"   {name:13s} E={E}: {dims[-1]} <= {bound(2, E)}")

    print("constraint map dp -> Re<p, dp> has rank 2E+1 at uniform gates (N=2, one encoded qubit)")
    for E in range(1, 7):
        d = 4
        gates = random_gates(d, E)
        # p(z) = e^{iEx/2} psi(x): sample the coefficients a_k of psi by a discrete transform
        M = 2 * E + 2
        xs = 2 * np.pi * np.arange(M) / M
        psi = []
        for x in xs:
            u = gates[0][0]
            for k in range(1, E + 1):
                u = gates[k][0] @ encoding(x, 2, [0]) @ u
            psi.append(np.exp(1j * E * x / 2) * u[:, 0])
        psi = np.array(psi)
        a = np.array([(psi * np.exp(-1j * k * xs)[:, None]).mean(axis=0) for k in range(E + 1)])
        recon = np.array([sum(a[k] * np.exp(1j * k * x) for k in range(E + 1)) for x in xs])
        assert np.allclose(recon, psi)
        # Re<p, dp> as a real trigonometric polynomial: columns for real and imaginary parts of dp
        cols = []
        for k in range(E + 1):
            for c in range(d):
                for phase in (1, 1j):
                    coef = np.zeros(2 * E + 1, complex)  # frequencies -E..E of <p, dp>
                    for j in range(E + 1):
                        coef[k - j + E] += np.conj(a[j, c]) * phase
                    re = (coef + np.conj(coef[::-1])) / 2  # coefficients of the real part
                    cols.append(np.concatenate([re.real, re.imag]))
        rank = np.linalg.matrix_rank(np.array(cols).T, tol=1e-9)
        assert rank == 2 * E + 1
    print("   rank 2E+1 for E = 1..6")
    print("all checks passed")


if __name__ == "__main__":
    main()
