# Lower bound for states: the saved 4-qubit state rho has ||rho||_shadow^2 / Tr(rho^2) >= 5.39,
# and the ratio is multiplicative under tensor products (checked on products of random 1- and 2-qubit states).
import numpy as np
import shadow as S

rho = np.loadtxt("rho_N4.txt", dtype=complex)
assert np.allclose(rho, rho.conj().T) and abs(np.trace(rho) - 1) < 1e-12 and np.linalg.eigvalsh(rho)[0] > -1e-12
Us, FN = S.setup(4)
ratio = np.linalg.eigvalsh(S.M_of(rho, Us, FN)[0])[-1] / np.trace(rho @ rho).real
assert ratio >= 5.39
print(f"4-qubit state: ratio {ratio:.5f}, exponent of the tensor powers {np.log2(ratio) / 4:.4f}")

# multiplicativity of the state ratio: rho_a (x) rho_b on 1 + 2 = 3 qubits, random states
rng = np.random.default_rng(5)
U1, F1 = S.setup(1); U2, F2 = S.setup(2); U3, F3 = S.setup(3)
r = lambda R: np.linalg.eigvalsh(S.M_of(R, *{1: (U1, F1), 2: (U2, F2), 3: (U3, F3)}[int(np.log2(len(R)))])[0])[-1] / np.trace(R @ R).real
for _ in range(20):
    a = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2)); A = a @ a.conj().T; A /= np.trace(A)
    b = rng.normal(size=(4, 4)) + 1j * rng.normal(size=(4, 4)); B = b @ b.conj().T; B /= np.trace(B)
    assert abs(r(np.kron(A, B)) - r(A) * r(B)) < 1e-9 * r(A) * r(B)
print("state ratio multiplicative under tensor products: ok")
