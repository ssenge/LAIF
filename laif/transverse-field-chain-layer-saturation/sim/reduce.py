"""Pseudospin reduction of the VQCS circuit (transverse-field spin chain, periodic, even L): the overlap of two VQCS states on L qubits
equals the product over k_j = (2j-1) pi / L, j = 1..L/2, of the overlaps of the pseudospin states, where each pseudospin starts in
|+>, and a layer applies exp(-2i gamma n_k.sigma) then exp(-2i beta X) with n_k = cos(k) X + sin(k) Z.
Checked against exact state vectors on L qubits for random angle pairs (asserted)."""
import numpy as np
from functools import reduce
X = np.array([[0, 1], [1, 0]], complex); Z = np.diag([1., -1]).astype(complex); I2 = np.eye(2)
R = lambda n, a: np.cos(a) * I2 - 1j * np.sin(a) * n
pl = np.array([1, 1]) / np.sqrt(2)
def kron_all(ops): return reduce(np.kron, ops)
def chain(L):
    HX = -sum(kron_all([X if i == j else I2 for i in range(L)]) for j in range(L))
    zz = np.zeros(2 ** L)
    for j in range(L):
        zj = kron_all([Z if i == j else I2 for i in range(L)]).diagonal(); zj1 = kron_all([Z if i == (j + 1) % L else I2 for i in range(L)]).diagonal()
        zz -= (zj * zj1).real
    w, V = np.linalg.eigh(HX); return w, V, zz
def vqcs(L, g, b, H=None):
    w, V, zz = H if H is not None else chain(L); psi = kron_all([pl] * L).astype(complex)
    for gj, bj in zip(g, b):
        psi = np.exp(-1j * gj * zz) * psi; psi = V @ (np.exp(-1j * bj * w) * (V.conj().T @ psi))
    return psi
def pseudo(L, g, b):
    out = []
    for j in range(1, L // 2 + 1):
        k = (2 * j - 1) * np.pi / L; n = np.cos(k) * X + np.sin(k) * Z; v = pl.astype(complex)
        for gj, bj in zip(g, b): v = R(X, 2 * bj) @ (R(n, 2 * gj) @ v)
        out.append(v)
    return out
if __name__ == "__main__":
    rng = np.random.default_rng(0)
    for L in [4, 6, 8]:
        H = chain(L); worst = 0
        for _ in range(20):
            p = rng.integers(1, 5); g1, b1, g2, b2 = (rng.uniform(0, np.pi, p) for _ in range(4))
            phys = abs(np.vdot(vqcs(L, g1, b1, H), vqcs(L, g2, b2, H))) ** 2
            ps = np.prod([abs(np.vdot(u, v)) ** 2 for u, v in zip(pseudo(L, g1, b1), pseudo(L, g2, b2))])
            worst = max(worst, abs(phys - ps))
        assert worst < 1e-10, (L, worst); print(f"L={L}: max |physical overlap - pseudospin product| = {worst:.1e}")
