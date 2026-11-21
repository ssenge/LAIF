"""Example (6) of arXiv:2212.03319: P = [[0.1, 0.9], [0.9, 0.1]], k = 1. Exact ODE (5) by RK4, no re-orthonormalization.
Claim checked: started near the bottom eigenvector (eigenvalue -0.8), phi converges to the bottom eigenvector, and
f = (phi^T P phi)^2 never decreases, so the q = 0 critical points (f = 0) are never reached from there."""
import numpy as np
P = np.array([[0.1, 0.9], [0.9, 0.1]])
u1, u2 = np.array([1, 1]) / np.sqrt(2), np.array([1, -1]) / np.sqrt(2)   # eigenvalues 1, -0.8
F = lambda p: (np.eye(2) - np.outer(p, p)) @ P @ p * (p @ P @ p)        # eq. (5), k = 1, P_t = p^T P p
def rk4(p, dt=0.01, n=40000):
    fs = []
    for _ in range(n):
        k1 = F(p); k2 = F(p + dt / 2 * k1); k3 = F(p + dt / 2 * k2); k4 = F(p + dt * k3)
        p = p + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4); fs.append((p @ P @ p) ** 2)
    return p, np.array(fs)
for eps in (0.05, 0.2, 0.5):
    p0 = np.cos(eps) * u2 + np.sin(eps) * u1
    p, fs = rk4(p0)
    q = p @ P @ p
    print(f"start {eps} rad from bottom: q0 {p0 @ P @ p0:+.4f} -> q {q:+.6f}, |<p,u2>| {abs(p @ u2):.6f}, |p| {np.linalg.norm(p):.6f}, "
          f"min df {np.diff(fs).min():.2e}")
    assert abs(abs(p @ u2) - 1) < 1e-6 and abs(q + 0.8) < 1e-6 and np.diff(fs).min() > -1e-12
print("bottom eigenvector attracts its neighbourhood; the q = 0 points (f = 0) are not limits from there")
