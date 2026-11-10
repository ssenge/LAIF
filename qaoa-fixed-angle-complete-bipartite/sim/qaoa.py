"""Exact QAOA MaxCut edge values: regular tree (sum over histories), K_{d,d} (two collective spins),
and a plain statevector for small graphs (used only to test the other two)."""
import itertools
import math

import numpy as np
from scipy.special import gammaln


def mixer(b):
    return np.array([[math.cos(b), -1j * math.sin(b)], [-1j * math.sin(b), math.cos(b)]])


def histories(p):
    """All histories h = (z^1..z^p, z^0, w^p..w^1) in {+1,-1}^(2p+1) and their weights f(h)."""
    H = np.array(list(itertools.product([1, -1], repeat=2 * p + 1)))
    return H


def weights(beta, H):
    p = len(beta)
    idx = (1 - H) // 2  # spin +1 -> basis 0
    z, z0, w = idx[:, :p], idx[:, p], idx[:, p + 1:][:, ::-1]  # w[:, t] = w^{t+1}

    def amp(x):
        a = np.full(len(H), 1 / math.sqrt(2), complex)
        for t in range(p - 1):
            a = a * mixer(beta[t])[x[:, t + 1], x[:, t]]
        return a * mixer(beta[p - 1])[z0, x[:, p - 1]]

    return amp(z) * np.conj(amp(w))


def edge_matrix(gamma, H):
    p = len(gamma)
    G = np.concatenate([np.asarray(gamma) / 2, [0.0], -np.asarray(gamma)[::-1] / 2])
    return np.exp(1j * (H * G) @ H.T)  # exp(i sum_t gamma_t/2 (z_t z'_t - w_t w'_t))


def tree_zz(beta, gamma, d):
    """<Z_u Z_v> at the centre edge of the depth-p (d-1)-ary double tree."""
    p = len(beta)
    H = histories(p)
    f = weights(beta, H)
    E = edge_matrix(gamma, H)
    m = E @ f  # leaf message
    for _ in range(p - 1):
        m = E @ (f * m ** (d - 1))
    g = f * m ** (d - 1)
    z0 = H[:, p]
    return float(np.real((g * z0) @ E @ (g * z0)))


def tree_cut(beta, gamma, d):
    return (1 - tree_zz(beta, gamma, d)) / 2


_jx = {}


def jx_eig(d):
    if d not in _jx:
        j = d / 2
        m = j - np.arange(d + 1)  # basis k = number of ones, S_z = d/2 - k
        off = 0.5 * np.sqrt(j * (j + 1) - m[1:] * (m[1:] + 1))
        J = np.diag(off, 1) + np.diag(off, -1)
        _jx[d] = np.linalg.eigh(J)
    return _jx[d]


def kdd_state(beta, gamma, d):
    k = np.arange(d + 1)
    amp = np.exp(0.5 * (gammaln(d + 1) - gammaln(k + 1) - gammaln(d - k + 1)) - d / 2 * math.log(2))
    M = d - 2 * k
    psi = np.outer(amp, amp).astype(complex)
    MM = np.outer(M, M)
    w, V = jx_eig(d)
    for b, g in zip(beta, gamma):
        psi *= np.exp(0.5j * g * MM)  # exp(-i g C) up to a global phase, C = (d^2 - M_A M_B)/2
        R = (V * np.exp(-2j * b * w)) @ V.conj().T
        psi = R @ psi @ R.T
    return psi, MM


def kdd_cut(beta, gamma, d):
    """Cut fraction of K_{d,d}, the same for every edge."""
    psi, MM = kdd_state(beta, gamma, d)
    return float((1 - np.sum(np.abs(psi) ** 2 * MM) / d ** 2) / 2)


def statevector_cut(beta, gamma, n, edges, edge=None):
    """Mean cut per edge (or <cut> of one edge) by a plain statevector, n <= ~22."""
    z = 1 - 2 * ((np.arange(2 ** n)[:, None] >> np.arange(n)[::-1]) & 1)
    C = sum((1 - z[:, a] * z[:, b]) / 2 for a, b in edges)
    psi = np.full(2 ** n, 2 ** (-n / 2), complex)
    for b, g in zip(beta, gamma):
        psi *= np.exp(-1j * g * C)
        psi = psi.reshape([2] * n)
        for q in range(n):
            psi = np.tensordot(mixer(b), psi, axes=([1], [q]))
            psi = np.moveaxis(psi, 0, q)
        psi = psi.reshape(-1)
    pr = np.abs(psi) ** 2
    if edge is None:
        return float(pr @ C) / len(edges)
    a, b = edge
    return float(pr @ ((1 - z[:, a] * z[:, b]) / 2))


def tree_graph(d, p):
    """Edges of the double tree T_d^p, centre edge (0, 1)."""
    edges, frontier, n = [(0, 1)], [0, 1], 2
    for _ in range(p):
        new = []
        for v in frontier:
            for _ in range(d - 1):
                edges.append((v, n)); new.append(n); n += 1
        frontier = new
    return n, edges


if __name__ == "__main__":
    rng = np.random.default_rng(0)
    for _ in range(3):
        beta, gamma = rng.uniform(-1, 1, 2), rng.uniform(-1, 1, 2)
        n, E = tree_graph(3, 2)
        a, b = tree_cut(beta, gamma, 3), statevector_cut(beta, gamma, n, E, (0, 1))
        assert abs(a - b) < 1e-10, (a, b)
        for d in (2, 3, 4):
            Ek = [(i, d + j) for i in range(d) for j in range(d)]
            a, b = kdd_cut(beta, gamma, d), statevector_cut(beta, gamma, 2 * d, Ek)
            assert abs(a - b) < 1e-10, (d, a, b)
    n, E = tree_graph(4, 1)
    beta, gamma = [0.3], [0.7]
    assert abs(tree_cut(beta, gamma, 4) - statevector_cut(beta, gamma, n, E, (0, 1))) < 1e-10
    print("tree and K_{d,d} values agree with the statevector")
