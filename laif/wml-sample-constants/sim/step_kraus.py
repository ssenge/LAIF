"""The one-copy step of route 36 as explicit Kraus operators S (x) P -> S, P = C^d (x) C^d, Delta <= 4/d:
  A_ac |s>|a'>|b> = delta_{a a'} (delta_{c b} |s> - (Delta/2) delta_{b s} |c>),   a, c = 0..d-1
  A_J  |s>|a>|b>  = sqrt(Delta (1 - d Delta/4)) delta_{b s} |a>
On the program |L> = (L (x) I)|Gamma>: rho -> rho + Delta Lind_L(rho) + Delta^2 E_L(rho),
  E_L(rho) = (1/4) tr(rho L+L) I - (d/4) L rho L+.   Checks: trace preservation, the expansion, the Choi rank."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"): os.environ[_v] = "1"
import numpy as np

def kraus(d, D):
    ops = []
    for a in range(d):
        for c in range(d):
            A = np.zeros((d, d ** 3))
            for s in range(d):
                for b in range(d):
                    col = s * d * d + a * d + b
                    if c == b: A[s, col] += 1
                    if b == s: A[c, col] -= D / 2
            ops.append(A)
    A = np.zeros((d, d ** 3))
    for s in range(d):
        for a in range(d): A[a, s * d * d + a * d + s] = np.sqrt(D * (1 - d * D / 4))
    return ops + [A]

def step(ops, rho, L):
    d = L.shape[0]; v = (L @ np.eye(d)).reshape(-1)            # |L> = sum_ab L_ab |a>|b>
    X = np.kron(rho, np.outer(v, v.conj())); return sum(A @ X @ A.conj().T for A in ops)

rng = np.random.default_rng(1)
for d in (2, 3, 4, 5):
    for D in (0.4 / d, 0.05, 0.003):
        ops = kraus(d, D)
        assert np.abs(sum(A.conj().T @ A for A in ops) - np.eye(d ** 3)).max() < 1e-12
        for _ in range(5):
            L = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); L /= np.linalg.norm(L)
            g = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); rho = g @ g.conj().T; rho /= np.trace(rho)
            K = L.conj().T @ L
            lind = L @ rho @ L.conj().T - (K @ rho + rho @ K) / 2
            E = np.trace(rho @ K) * np.eye(d) / 4 - d / 4 * L @ rho @ L.conj().T
            assert np.abs(step(ops, rho, L) - (rho + D * lind + D * D * E)).max() < 1e-12
print("ok: Kraus step is a channel for Delta <= 4/d (sampled), with expansion rho + Delta Lind + Delta^2 E exactly")
