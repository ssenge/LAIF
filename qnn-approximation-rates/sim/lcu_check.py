#!/usr/bin/env python3
"""Checks Theorem 2 of ../README.md: the fixed-encoding circuit that outputs P(y)/lambda for a real trigonometric
polynomial P, and the rate of the de la Vallee-Poussin step.

1. Circuit identity. For a random real P with frequencies in {-2N..2N}^d, build the circuit on an index register of q
   qubits plus one ancilla as matrices: the state preparation V from a tree of uniformly controlled RY rotations
   (2^q - 1 angles), then, controlled by the ancilla of a Hadamard test, a diagonal of trainable phases (n angles) and
   the fixed data diagonal D(y) = sum_k e^{i k.y} |k><k|. Check <X_ancilla> = P(y)/lambda on a grid.
2. Rate. For 2 pi-periodic test functions of Holder order beta, check that the sup error of the tensor
   de la Vallee-Poussin mean V_N times N^beta stays bounded as N grows.
"""
import itertools
import numpy as np


def ry(t):
    c, s = np.cos(t / 2), np.sin(t / 2)
    return np.array([[c, -s], [s, c]])


def state_prep(amp, q):
    """Tree of uniformly controlled RY rotations with V|0> = amp (real, nonnegative). Returns V and its angle count."""
    a = np.zeros(2 ** q)
    a[: len(amp)] = amp
    V = np.eye(2 ** q)
    angles = 0
    for level in range(q):
        # rotation on qubit `level`, controlled by the value of the qubits before it
        blk = 2 ** (q - level)
        U = np.zeros((2 ** q, 2 ** q))
        for pre in range(2 ** level):
            seg = a[pre * blk : (pre + 1) * blk]
            l, r = np.linalg.norm(seg[: blk // 2]), np.linalg.norm(seg[blk // 2 :])
            t = 2 * np.arctan2(r, l)
            angles += 1
            R = np.kron(ry(t), np.eye(blk // 2))
            U[pre * blk : (pre + 1) * blk, pre * blk : (pre + 1) * blk] = R
        V = U @ V
    return V, angles


def circuit_check(d, N, rng):
    K = list(itertools.product(range(-2 * N, 2 * N + 1), repeat=d))
    n = len(K)
    c = {}
    for k in K:  # random real polynomial: c_{-k} = conj(c_k)
        mk = tuple(-x for x in k)
        if mk in c:
            c[k] = np.conj(c[mk])
        else:
            c[k] = rng.normal() + 1j * rng.normal() if any(k) else rng.normal() + 0j
    lam = sum(abs(v) for v in c.values())
    q = int(np.ceil(np.log2(n)))
    V, angles = state_prep(np.sqrt(np.array([abs(c[k]) for k in K]) / lam), q)
    phases = np.zeros(2 ** q)
    phases[:n] = [np.angle(c[k]) for k in K]
    ks = np.zeros((2 ** q, d))
    ks[:n] = K
    zero = np.zeros(2 ** q)
    zero[0] = 1
    worst = 0.0
    for _ in range(200):
        y = rng.uniform(-np.pi, np.pi, d)
        reg = V @ zero
        # Hadamard test: ancilla |+>, then phases and D(y) controlled by the ancilla, measure X on the ancilla
        psi = np.concatenate([reg, np.exp(1j * (ks @ y + phases)) * reg]) / np.sqrt(2)
        X = np.kron(np.array([[0, 1], [1, 0]]), np.eye(2 ** q))
        out = np.real(psi.conj() @ X @ psi)
        P = np.real(sum(c[k] * np.exp(1j * np.dot(k, y)) for k in K))
        worst = max(worst, abs(out - P / lam))
    assert worst < 1e-10, worst
    assert angles == 2 ** q - 1  # one angle per tree node; nodes over padding entries get angle 0
    print(f"d={d} N={N}: n={n} frequencies, {q + 1} qubits, {angles} + {n} trainable angles, max |<X> - P/lambda| = {worst:.1e}")


def vp_error(G, N):
    """Sup error of the tensor de la Vallee-Poussin mean of grid samples G (2 pi-periodic, d axes)."""
    M = G.shape[0]
    k = np.abs(np.fft.fftfreq(M, 1 / M))
    m1 = np.clip(2 - k / N, 0, 1)
    F = np.fft.fftn(G)
    for ax in range(G.ndim):
        shape = [1] * G.ndim
        shape[ax] = M
        F = F * m1.reshape(shape)
    return np.abs(np.real(np.fft.ifftn(F)) - G).max()


def rate_check():
    M = 2 ** 14
    y = 2 * np.pi * np.arange(M) / M
    for beta in [0.5, 1.5, 2.5]:
        G = np.abs(np.sin(y / 2)) ** beta  # Holder of order beta on the circle, and not better at y = 0
        r = [vp_error(G, N) * N ** beta for N in [8, 32, 128, 512]]
        print(f"d=1 beta={beta}: N^beta * error = " + ", ".join(f"{x:.3f}" for x in r))
        assert max(r) / min(r) < 3
    M = 2 ** 10
    y = 2 * np.pi * np.arange(M) / M
    Y1, Y2 = np.meshgrid(y, y, indexing="ij")
    G = np.abs(np.sin(Y1 / 2)) ** 1.5 * np.cos(Y2) + np.abs(np.sin((Y1 + Y2) / 2)) ** 1.5
    r = [vp_error(G, N) * N ** 1.5 for N in [4, 16, 64]]
    print("d=2 beta=1.5: N^beta * error = " + ", ".join(f"{x:.3f}" for x in r))
    assert max(r) / min(r) < 3


def main():
    rng = np.random.default_rng(0)
    circuit_check(1, 1, rng)
    circuit_check(1, 3, rng)
    circuit_check(2, 1, rng)
    rate_check()


if __name__ == "__main__":
    main()
