# Dilation of a Gaussian channel (X, Y) with A = Omega - X Omega X^T invertible (Theorem 3):
#   S = [[X, M], [C, D]],  M = |A|^{1/2} O_A,  C = O_B^T |B|^{-1/2},  D = C Omega X^T M^{-T} Omega,
#   B = Omega - Omega X^T A^{-1} X Omega^T,  environment state with covariance V_E = M^{-1} Y M^{-T}.
# For a nearby X2 the orthogonal factors are transported by the polar factor of (1 - J2 J1)/2.
# Checks with asserts: S symplectic; output covariance X V X^T + M V_E M^T = X V X^T + Y; V_E + i Omega >= 0;
# B^{-1} = -(Omega - X^T Omega X); the norm bound ||S|| <= 4 Z / sqrt(a) and the bound
# ||S1 - S2|| <= 104 Z^{7/2} K^{9/2} ||X1 - X2||, Z = 1 + z^2, K = Z / a, whenever ||X1 - X2|| <= 1/(10 Z^3 K^4).
import numpy as np
from scipy.linalg import sqrtm, polar
from teleport import Om
rng = np.random.default_rng(13)

def absm(A):
    return np.real(sqrtm(A.T @ A))

def J_of(A):
    return A @ np.linalg.inv(absm(A))

def O_for(J, m):
    """Orthogonal O with O Omega O^T = J (J orthogonal, antisymmetric)."""
    # real normal form of the normal matrix J: J = Q T Q^T with 2x2 blocks [[0, b], [-b, 0]], b = +-1
    from scipy.linalg import schur
    T, Q = schur(J, output="real")
    O = Q.copy()
    for k in range(m):
        if T[2 * k, 2 * k + 1] < 0:             # block [[0, -1], [1, 0]]: swap the two columns
            O[:, [2 * k, 2 * k + 1]] = O[:, [2 * k + 1, 2 * k]]
    assert np.allclose(O @ Om(m) @ O.T, J, atol=1e-6)
    return O

def transport(O1, J1, J2):
    T = (np.eye(len(J1)) - J2 @ J1) / 2
    P, _ = polar(T)
    O2 = P @ O1
    return O2

def build(X, m, OA=None, OB=None):
    W = Om(m)
    A = W - X @ W @ X.T
    aA = absm(A); JA = J_of(A)
    if OA is None: OA = O_for(JA, m)
    M = np.real(sqrtm(aA)) @ OA
    B = W - W @ X.T @ np.linalg.inv(A) @ X @ W.T
    JB = J_of(B)
    if OB is None: OB = O_for(JB, m)
    C = OB.T @ np.linalg.inv(np.real(sqrtm(absm(B))))
    D = C @ W @ X.T @ np.linalg.inv(M).T @ W
    S = np.block([[X, M], [C, D]])
    return S, M, A, B, JA, JB, OA, OB

worst = 0; tested = 0
for m in (1, 2, 3):
    W2 = np.kron(np.eye(2), Om(m))
    for t in range(200):
        X = rng.normal(size=(2 * m, 2 * m)) * rng.uniform(0.2, 1.2)
        S, M, A, B, JA, JB, OA, OB = build(X, m)
        assert np.allclose(S @ W2 @ S.T, W2, atol=1e-8)
        assert np.allclose(np.linalg.inv(B), -(Om(m) - X.T @ Om(m) @ X), atol=1e-8)
        z = max(1.0, np.linalg.norm(X, 2)); Z = 1 + z ** 2
        a = np.linalg.svd(A, compute_uv=False).min(); K = Z / a
        assert np.linalg.norm(S, 2) <= 4 * Z / np.sqrt(a)
        # a valid noise matrix: Y = |iA| + G G^T
        w, U = np.linalg.eigh(1j * A); Y = ((U * np.abs(w)) @ U.conj().T).real
        G = rng.normal(size=(2 * m, 2 * m)) * 0.3; Y = Y + G @ G.T
        VE = np.linalg.inv(M) @ Y @ np.linalg.inv(M).T
        assert np.linalg.eigvalsh(VE + 1j * Om(m)).min() > -1e-8
        V = np.eye(2 * m) * 1.3
        Vin = np.block([[V, np.zeros((2 * m, 2 * m))], [np.zeros((2 * m, 2 * m)), VE]])
        Vout = (S @ Vin @ S.T)[:2 * m, :2 * m]
        assert np.allclose(Vout, X @ V @ X.T + Y, atol=1e-8)
        # difference bound along a nearby X2 (z, a taken over both)
        for scale in (1e-2, 1e-4, 1e-6):
            E = rng.normal(size=(2 * m, 2 * m)); X2 = X + scale * E / np.linalg.norm(E, 2)
            A2 = Om(m) - X2 @ Om(m) @ X2.T
            z2 = max(z, np.linalg.norm(X2, 2)); Z2 = 1 + z2 ** 2
            a2 = min(a, np.linalg.svd(A2, compute_uv=False).min()); K2 = Z2 / a2
            dX = np.linalg.norm(X2 - X, 2)
            if dX > 1 / (10 * Z2 ** 3 * K2 ** 4):
                continue
            JA2 = J_of(A2)
            B2 = Om(m) - Om(m) @ X2.T @ np.linalg.inv(A2) @ X2 @ Om(m).T
            OA2 = transport(OA, JA, JA2); OB2 = transport(OB, JB, J_of(B2))
            S2 = build(X2, m, OA2, OB2)[0]
            assert np.allclose(S2 @ W2 @ S2.T, W2, atol=1e-8)
            ratio = np.linalg.norm(S2 - S, 2) / (104 * Z2 ** 3.5 * K2 ** 4.5 * dX)
            assert ratio <= 1, ratio
            tested += 1
            worst = max(worst, np.linalg.norm(S2 - S, 2) / dX / (Z2 ** 3.5 * K2 ** 4.5))
assert tested >= 300, tested
print(f"dilation: symplectic, reproduces (X, Y), valid environment state on 600 channels; on {tested} nearby pairs ||S1 - S2|| / (Z^3.5 K^4.5 ||X1 - X2||) <= {worst:.3f} (bound 104)")
