# Explicit bounds of the perturbation lemma and the learning theorem (README notation).
import numpy as np
C3 = (1 + np.sqrt(3)) / 8

def e_out(E, m, z, y):
    """Output energy bound z^2 (E + m/2) + m y/2 for a channel with d = 0 (Lemma 3)."""
    return z ** 2 * (E + m / 2) + m * y / 2

def sim_bound(E, m, z, y, xi, dX, dX1, dY1):
    """Lemma 3: both channels equal Phi_i' o N_xi, with ||X_i|| <= z, ||Y_i'|| <= y; dX operator norm,
    dX1 = ||X1 - X2||_1, dY1 = ||Y1' - Y2'||_1."""
    e2r = 2 / xi
    c = (e2r + 1 / e2r) / 2
    choi = C3 * (max(1, z ** 2) * e2r + y) * (e2r * (1 + 2 * z) * dX1 + dY1)
    corr = dX * np.sqrt(2 * E + m * (1 + c)) * np.sqrt(2 * e_out(E, m, z, y + xi * z ** 2) + 1)
    return choi + corr

def general_bound(E, m, z, y, xi, dX, dY, dd):
    """Theorem 1(b): any two channels, ||X_i|| <= z, ||Y_i|| <= y, operator-norm errors dX, dY, |d1 - d2| = dd."""
    return (2 * np.sqrt(m * xi * (2 * E + 1)) + sim_bound(E, m, z, y, xi, dX, 2 * m * dX, 2 * m * dY)
            + dd * np.sqrt(2 * e_out(E, m, z, y) + 1))

def margin_bound(E, m, z, y, xi, dX, dY, dd):
    """Theorem 1(a): both channels have noise margin xi."""
    dY1 = 2 * m * (dY + xi * 2 * z * dX)
    return sim_bound(E, m, z, y, xi, dX, 2 * m * dX, dY1) + dd * np.sqrt(2 * e_out(E, m, z, y) + 1)

def dil_bound(E, m, z, y, a, dX, dY, dd):
    """Theorem 3: both channels with sigma_min(Omega - X_i Omega X_i^T) >= a, ||X_i|| <= z (z >= 1), ||Y_i|| <= y."""
    Z = 1 + z ** 2; K = Z / a
    return (382 * Z ** 2 * K ** 2.5 * np.sqrt(m * (E + m * y / (2 * a) + 1) * dX)
            + 0.7 * m * y / a ** 2 * (18 * y * K ** 3.5 * dX + dY)
            + dd * np.sqrt(2 * e_out(E, m, z, y) + 1))
