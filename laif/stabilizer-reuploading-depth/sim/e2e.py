"""End-to-end check with 2x2 unitaries: U_0 = R_y(x); U_{k+1} = W(U_k) with S_n^j = U S^j U^dagger.
Compares the axis z-component of U S U^dagger with the iterated polynomials and reports the accuracy reached."""
import numpy as np
from poly import WA, WB
from maps import G
Z = np.diag([1, -1]).astype(complex); X = np.array([[0, 1], [1, 0]], complex); Yp = np.array([[0, -1j], [1j, 0]])
S = np.diag([np.exp(-1j * np.pi / 4), np.exp(1j * np.pi / 4)])            # R_z(pi/2)
Ry = lambda x: np.array([[np.cos(x / 2), -np.sin(x / 2)], [np.sin(x / 2), np.cos(x / 2)]], complex)
def axis_z(U):                                                          # z-component of O(U) e_z
    return np.real(np.trace(Z @ U @ Z @ U.conj().T)) / 2
def step(U, word):
    W = np.eye(2, dtype=complex); Sk = lambda k: np.linalg.matrix_power(S, k)
    for typ, k in word: W = W @ (U @ Sk(k) @ U.conj().T if typ == "n" else Sk(k))
    a, _, b = np.linalg.svd(W); return a @ b                            # remove float drift from unitarity
for delta in [0.2, 0.05, 0.01]:
    xs = np.r_[np.linspace(delta, 1, 400), -np.linspace(delta, 1, 50)]
    eta = 1e-12; M, rho = 3.3273, 0.01                                   # Lemma 1: k1 + 8 A-steps, then j B-steps
    kA = max(0, int(np.ceil(np.log(5 * 1e-3 / (2 * delta ** 2)) / np.log(25.72)))) + 8
    kB = int(np.ceil(np.log2(np.log(1 / (M * eta)) / np.log(1 / (M * rho)))))
    errs = []
    for x in xs:
        U = Ry(x); tp = np.cos(x)
        for _ in range(kA): U = step(U, WA); tp = G(WA, tp)[0]
        for _ in range(kB): U = step(U, WB); tp = G(WB, tp)[0]
        assert abs(axis_z(U) - tp) < 1e-6
        errs.append(abs(axis_z(U) - 2 ** -0.5))
    assert max(errs) <= eta
    print(f"delta={delta}: {kA} A-steps + {kB} B-steps, encoding calls 10^{kA+kB}; max |n_z - 1/sqrt2| = {max(errs):.2e}")
