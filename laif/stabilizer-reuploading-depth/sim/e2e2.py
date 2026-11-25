"""End-to-end check of Lemma 1' with 2x2 unitaries: k1 + K_F steps of F = Q o P (100 copies each), then K_A steps of A
and j steps of B. Arguments: c K_F K_A (from out_certify2.txt). Compares with the iterated polynomials and with 1/sqrt2."""
import sys, numpy as np
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
WP = [("n", 1), ("z", 2), ("n", 2), ("z", 2), ("n", 2), ("z", 2), ("n", 1), ("z", 1), ("n", 3)]
WQ = [("n", 2), ("z", 2), ("n", 1), ("z", 3), ("n", 3), ("z", 2), ("n", 2), ("z", 2), ("n", 2)]
c, KF, KA = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]); kappa = 1e-5
eta = 1e-12; M, rho = 3.3274, 0.01
for delta in [0.2, 0.05, 0.01, 0.002]:
    k1 = max(0, int(np.ceil(np.log(5 * kappa / (2 * delta ** 2)) / np.log(c))))
    j = int(np.ceil(np.log2(np.log(1 / (M * eta)) / np.log(1 / (M * rho)))))
    xs = np.r_[np.linspace(delta, 1, 300), -np.linspace(delta, 1, 30)]; errs = []
    for x in xs:
        U = Ry(x); tp = np.cos(x)
        for _ in range(k1 + KF): U = step(step(U, WP), WQ); tp = G(WQ, G(WP, tp))[0]
        for _ in range(KA): U = step(U, WA); tp = G(WA, tp)[0]
        for _ in range(j): U = step(U, WB); tp = G(WB, tp)[0]
        assert abs(axis_z(U) - tp) < 1e-6; errs.append(abs(axis_z(U) - 2 ** -0.5))
    assert max(errs) <= eta
    print(f"delta={delta}: {k1 + KF} F-steps + {KA} A-steps + {j} B-steps, encoding calls 10^{2 * (k1 + KF) + KA + j}; max |n_z - 1/sqrt2| = {max(errs):.2e}")
