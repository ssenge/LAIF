"""Checks for the re-uploading amplitude ceiling (README.md).

C(m, d): the largest |c_{mL-d}| over all channels between and after L >= 2 uploads of m qubits
and all readouts with ||O|| <= 1. By Theorem 1 it is the value of a small concave program.
"""
import math

import numpy as np
from scipy.optimize import minimize

rng = np.random.default_rng(3)


def binom(m):
    return np.array([math.comb(m, t) for t in range(m + 1)]) / 2 ** m


def closed_form(m, d):
    return sum(math.sqrt(math.comb(m, t) * math.comb(m, d - t)) for t in range(d + 1)) / 2 ** m


def tail(m, d):  # T(m, d) of the reference
    return binom(m)[: d + 1].sum()


def single_upload(m, k, grid=721):
    """c*(m, k) of the reference: max over phi of the trace norm of (e^{i phi} M_k + h.c.)/2."""
    v = np.sqrt(binom(m))
    N = np.zeros((m + 1, m + 1))
    for j in range(k, m + 1):
        N[j, j - k] = v[j] * v[j - k]
    return max(np.abs(np.linalg.eigvalsh((np.exp(1j * f) * N + np.exp(-1j * f) * N.T) / 2)).sum()
               for f in np.linspace(0, np.pi, grid))


def program(m, d, trials=40):
    """Symmetric form of the program: maximise sum_t sqrt(a_t a_{d-t}) over a, u >= 0 with
    sum_{t<=J} a_t <= sum_{c<=J} u_c and u_c + u_{m-c} <= B(c) (u_{m-c} absent if m - c > d)."""
    Bm, n = binom(m), d + 1
    cons = []
    for c in range(n):
        if m - c == c:
            cons.append(lambda z, c=c: Bm[c] - 2 * z[n + c])
        elif m - c <= d:
            cons.append(lambda z, c=c: Bm[c] - z[n + c] - z[n + m - c])
        else:
            cons.append(lambda z, c=c: Bm[c] - z[n + c])
    for J in range(n):
        cons.append(lambda z, J=J: np.sum(z[n:n + J + 1]) - np.sum(z[:J + 1]))
    obj = lambda z: -np.sum(np.sqrt(np.maximum(z[:n], 0) * np.maximum(z[:n][::-1], 0)))
    best = 0.0
    for _ in range(trials):
        z0 = rng.random(2 * n) * Bm[:n].max() * 0.5
        r = minimize(obj, z0, constraints=[{"type": "ineq", "fun": f} for f in cons],
                     bounds=[(0, 1)] * (2 * n), method="SLSQP", options={"ftol": 1e-15, "maxiter": 2000})
        if all(f(r.x) > -1e-10 for f in cons):
            best = max(best, -r.fun)
    return best


def circuit_value(m, anc, L, d, unitaries):
    """max over ||O|| <= 1 of |c_{mL-d}| for RY(x) on m qubits, unitaries on m + anc qubits in between."""
    n = m + anc
    D = 2 ** n
    Y = np.array([[0, -1j], [1j, 0]])
    K = m * L - d
    N = 2 * m * L + 3
    M = np.zeros((D, D), complex)
    for x in 2 * np.pi * np.arange(N) / N:
        g = np.cos(x / 2) * np.eye(2) - 1j * np.sin(x / 2) * Y
        R = np.array([[1.0]])
        for q in range(n):
            R = np.kron(R, g if q < m else np.eye(2))
        psi = np.zeros(D, complex)
        psi[0] = 1
        psi = R @ psi
        for V in unitaries:
            psi = R @ (V @ psi)
        M += np.outer(psi, psi.conj()) * np.exp(1j * K * x) / N
    return max(np.abs(np.linalg.eigvalsh((np.exp(1j * f) * M + np.exp(-1j * f) * M.conj().T) / 2)).sum()
               for f in np.linspace(0, np.pi, 61))


def uniform_unitary(D):
    z = (rng.normal(size=(D, D)) + 1j * rng.normal(size=(D, D))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / abs(np.diag(r)))


def main():
    print("1. for 2d < m: program = closed form = single-upload ceiling c*(m, m-d) < T(m, d)")
    for m in range(2, 13):
        for d in range(1, (m + 1) // 2):
            V, cs = closed_form(m, d), single_upload(m, m - d)
            assert abs(V - cs) < 1e-9 and V < tail(m, d)
            if m <= 8:
                assert abs(program(m, d) - V) < 1e-6
    print("   checked for m = 2..12 (program for m <= 8)")
    print("2. C(m, d) for L >= 2 against the single upload and T(m, d); C <= 1/2")
    print("   m  d   C(m,d)   c*(m,m-d)  T(m,d)")
    for m in range(2, 9):
        for d in range(m):
            C = closed_form(m, d) if 2 * d < m else program(m, d)
            assert C <= 0.5 + 1e-9 and C <= tail(m, d) + 1e-12
            print(f"   {m}  {d}   {C:.5f}  {single_upload(m, m - d):.5f}    {tail(m, d):.5f}")
    print("3. d = 1: C(m, 1) = 2 sqrt(m) / 2^m for m >= 3")
    for m in range(3, 13):
        assert abs(closed_form(m, 1) - 2 * math.sqrt(m) / 2 ** m) < 1e-12
    print("   ok for m = 3..12")
    print("4. random circuits never exceed C(m, d)")
    for m, anc, L, trials in [(2, 1, 2, 300), (2, 2, 2, 100), (3, 1, 2, 100), (2, 1, 3, 100)]:
        for d in range(m):
            C = closed_form(m, d) if 2 * d < m else program(m, d)
            worst = max(circuit_value(m, anc, L, d, [uniform_unitary(2 ** (m + anc)) for _ in range(L - 1)])
                        for _ in range(trials))
            assert worst <= C + 1e-9
            print(f"   m={m} ancillas={anc} L={L} d={d}: largest {worst:.4f} <= C = {C:.4f}")
    print("all checks passed")


if __name__ == "__main__":
    main()
