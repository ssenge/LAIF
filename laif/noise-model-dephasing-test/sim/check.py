"""Checks for the tester that decides between E_{p,U} = (1-p) id + p Delta_U (dephasing in an unknown fixed basis)
and M_p = (1-p) id + p Lambda, Lambda = (id + d Omega)/(d+1).
1. Block composition: E^m = (1-p)^m id + (1-(1-p)^m) Delta_U, M^m = a^m id + (1-a^m) Omega, a = 1 - p d/(d+1).
2. For uniformly random psi, w_k = |<u_k|psi>|^2 is uniform on the simplex; X = sum w_k^2 - 1/d has
   E X = (d-1)/(d(d+1)), E X^2 = E S^2 - 2 E S/d + 1/d^2 with E S^2 = 4(d+5)/((d+1)(d+2)(d+3)).
   Second-moment inequality: P(X >= E X/2) >= (E X)^2/(4 E X^2) >= c0 for all d >= 2.
3. With eta = 1/(4 sqrt(6 d)) the HS distance of the two block outputs is at least 1/(2 sqrt(6 d)) when X >= E X/2."""
from fractions import Fraction as F
import numpy as np
rng = np.random.default_rng(0)
def dephase(U, rho): P = U.conj().T @ rho @ U; return U @ np.diag(np.diag(P)) @ U.conj().T
def haar(d):
    Z = (rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))) / np.sqrt(2); Q, R = np.linalg.qr(Z)
    return Q * (np.diag(R) / abs(np.diag(R)))
def apply_E(U, p, rho): return (1 - p) * rho + p * dephase(U, rho)
def apply_M(p, rho): d = len(rho); return (1 - p) * rho + p * (rho + np.trace(rho) * np.eye(d)) / (d + 1)
# 1. block composition
for d in (2, 3, 5):
    U = haar(d); p = 0.3; m = 7; v = rng.standard_normal(d) + 1j * rng.standard_normal(d); rho = np.outer(v, v.conj()); rho /= np.trace(rho)
    r1, r2 = rho.copy(), rho.copy()
    for _ in range(m): r1 = apply_E(U, p, r1); r2 = apply_M(p, r2)
    a = 1 - p * d / (d + 1)
    assert np.allclose(r1, (1 - p) ** m * rho + (1 - (1 - p) ** m) * dephase(U, rho))
    assert np.allclose(r2, a ** m * rho + (1 - a ** m) * np.eye(d) / d)
# 2. exact moments of the weights and the second-moment constant
c0 = None
for d in range(2, 2001):
    ES = F(2, d + 1); ES2 = F(4 * (d + 5), (d + 1) * (d + 2) * (d + 3))
    EX = ES - F(1, d); EX2 = ES2 - 2 * ES / d + F(1, d * d)
    assert EX == F(d - 1, d * (d + 1)) and EX / 2 >= F(1, 6 * d)
    pz = EX * EX / (4 * EX2); c0 = pz if c0 is None or pz < c0 else c0
print("min PZ constant over 2 <= d <= 2000:", float(c0))
assert c0 >= F(1, 8)
# monte carlo check of the moments
for d in (2, 7, 30):
    W = rng.dirichlet(np.ones(d), 200000); S = (W ** 2).sum(1)
    assert abs(S.mean() - 2 / (d + 1)) < 4e-3 * 2 / (d + 1) + 1e-4
    assert abs((S ** 2).mean() - 4 * (d + 5) / ((d + 1) * (d + 2) * (d + 3))) < 0.02 * 4 * (d + 5) / ((d + 1) * (d + 2) * (d + 3))
# 3. HS gap of the block outputs on random instances
for d in (2, 4, 16, 64):
    eta = 1 / (4 * np.sqrt(6 * d)); bad = 0; trials = 400
    for _ in range(trials):
        U = haar(d); v = haar(d)[:, 0]; psi = np.outer(v, v.conj())
        w = abs(U.conj().T @ v) ** 2; X = (w ** 2).sum() - 1 / d
        q, qp = eta * rng.random(), eta * rng.random()      # any contamination weights up to eta
        sE = (1 - q) * dephase(U, psi) + q * psi; sM = (1 - qp) * np.eye(d) / d + qp * psi
        hs = np.linalg.norm(sE - sM)
        if X >= (d - 1) / (2 * d * (d + 1)): assert hs >= 1 / (2 * np.sqrt(6 * d)) - 1e-12
        else: bad += 1
    print(f"d={d}: fraction of psi with X < E X/2: {bad / trials:.3f}")
print("all checks passed")
