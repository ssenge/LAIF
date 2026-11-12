# Moment-level checks for the teleportation simulation of Gaussian channels (convention: R = (x1,p1,...),
# [x,p] = i, V = 2 Cov, vacuum V = I, channel (X, Y, d): mu -> X mu + d, V -> X V X^T + Y).
#  (1) Teleporting through the state omega = (id_R (x) Phi')(TMSV_r), with homodyne of x_A - x_R, p_A + p_R
#      (outcome z) and correction D_{X z}, realizes Phi' o N_xi with xi = 2 e^{-2r} on Gaussian inputs
#      (first and second moments, all outcomes averaged).
#  (2) ||V_omega|| <= max(1, ||X||^2) e^{2r} + ||Y|| and the trace-norm bound on V_omega1 - V_omega2.
#  (3) E|z|^2 = <R_A^T R_A> + m cosh 2r.
import numpy as np
rng = np.random.default_rng(7)

def Om(m):
    return np.kron(np.eye(m), np.array([[0., 1.], [-1., 0.]]))

def rand_channel(m, margin=0.0):
    """Random valid (X, Y): Y = |i(Omega - X Omega X^T)| + PSD + margin * X X^T."""
    X = rng.normal(size=(2 * m, 2 * m)) * 0.7
    A = Om(m) - X @ Om(m) @ X.T                     # real antisymmetric
    H = 1j * A                                      # Hermitian
    w, U = np.linalg.eigh(H)
    absH = (U * np.abs(w)) @ U.conj().T
    G = rng.normal(size=(2 * m, 2 * m)) * 0.3
    Y = absH.real + G @ G.T + margin * X @ X.T
    lam = np.linalg.eigvalsh(Y - margin * X @ X.T + 1j * A).min()
    assert lam > -1e-9, lam
    return X, Y

def tmsv(m, r):
    c, s = np.cosh(2 * r), np.sinh(2 * r)
    Z = np.kron(np.eye(m), np.diag([1., -1.]))
    return np.block([[c * np.eye(2 * m), s * Z], [s * Z, c * np.eye(2 * m)]])

def teleport_moments(VA, muA, X, Y, r):
    m = VA.shape[0] // 2
    Vw = tmsv(m, r)
    T = np.block([[np.eye(2 * m), np.zeros((2 * m, 2 * m))], [np.zeros((2 * m, 2 * m)), X]])
    Vw = T @ Vw @ T.T + np.block([[np.zeros((2 * m, 2 * m)), np.zeros((2 * m, 2 * m))], [np.zeros((2 * m, 2 * m)), Y]])
    # joint (A, R, B), covariance in the Var convention C = V / 2
    C = np.zeros((6 * m, 6 * m)); C[:2 * m, :2 * m] = VA / 2; C[2 * m:, 2 * m:] = Vw / 2
    mu = np.concatenate([muA, np.zeros(4 * m)])
    # z = (x_A - x_R, p_A + p_R) per mode
    L = np.zeros((2 * m, 6 * m))
    for k in range(m):
        L[2 * k, 2 * k] = 1; L[2 * k, 2 * m + 2 * k] = -1
        L[2 * k + 1, 2 * k + 1] = 1; L[2 * k + 1, 2 * m + 2 * k + 1] = 1
    B = np.zeros((2 * m, 6 * m)); B[:, 4 * m:] = np.eye(2 * m)
    Czz, Cbz, Cbb = L @ C @ L.T, B @ C @ L.T, B @ C @ B.T
    K = Cbz @ np.linalg.inv(Czz)
    Ccond = Cbb - K @ Czz @ K.T                     # conditional covariance of B given z
    # output b + X z with b | z ~ N(mu_b + K (z - mu_z), Ccond): affine in z, so
    G = K + X
    mu_out = B @ mu - K @ (L @ mu) + G @ (L @ mu)
    C_out = Ccond + G @ Czz @ G.T
    Ez2 = np.trace(Czz) + (L @ mu) @ (L @ mu)
    return mu_out, 2 * C_out, Ez2

def main():
  for m in (1, 2, 3):
    for trial in range(20):
        X, Y = rand_channel(m)
        r = rng.uniform(0.1, 2.0); xi = 2 * np.exp(-2 * r)
        S = rng.normal(size=(2 * m, 2 * m)) * 0.4
        VA = (np.eye(2 * m) + S @ S.T)
        VA = VA + 1j * 0                            # any V with V + i Omega >= 0 (enlarge if needed)
        VA = VA.real + np.eye(2 * m) * max(0, -np.linalg.eigvalsh(VA.real + 1j * Om(m)).min())
        muA = rng.normal(size=2 * m)
        mu_out, V_out, Ez2 = teleport_moments(VA, muA, X, Y, r)
        assert np.allclose(mu_out, X @ muA), (mu_out, X @ muA)                                   # (1)
        assert np.allclose(V_out, X @ (VA + xi * np.eye(2 * m)) @ X.T + Y, atol=1e-8)              # (1)
        RA2 = np.trace(VA) / 2 + muA @ muA
        assert np.isclose(Ez2, RA2 + m * np.cosh(2 * r))                                          # (3)
        # (2)
        X2, Y2 = rand_channel(m)
        c, s = np.cosh(2 * r), np.sinh(2 * r)
        Z = np.kron(np.eye(m), np.diag([1., -1.]))
        def Vom(X, Y):
            return np.block([[c * np.eye(2 * m), s * Z @ X.T], [s * X @ Z, c * X @ X.T + Y]])
        V1, V2 = Vom(X, Y), Vom(X2, Y2)
        z = max(np.linalg.norm(X, 2), np.linalg.norm(X2, 2))
        for V, YY in ((V1, Y), (V2, Y2)):
            assert np.linalg.norm(V, 2) <= max(1, z ** 2) * np.exp(2 * r) + np.linalg.norm(YY, 2) + 1e-9
        tn = lambda M: np.abs(np.linalg.eigvalsh((M + M.T) / 2)).sum()
        dX1 = np.linalg.svd(X - X2, compute_uv=False).sum()
        assert tn(V1 - V2) <= np.exp(2 * r) * (1 + 2 * z) * dX1 + tn(Y - Y2) + 1e-9
  print("teleportation moments, Choi covariance bounds and E|z|^2: all asserts passed")

if __name__ == "__main__":
    main()
