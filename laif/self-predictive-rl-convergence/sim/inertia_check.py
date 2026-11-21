"""Checks of Theorems 1 to 3 of README.md on ODE (5) of arXiv:2212.03319, symmetric T, exact RK4 (no re-orthonormalization).
Theorem 1: inertia of Q conserved and every ordered |eigenvalue| of Q non-decreasing along the flow;
Theorems 2 and 3: the limit spans the top-p positive + bottom-(k-p) negative eigen-directions, p = #positive eigenvalues of Q_0;
also with repeated eigenvalues of T (multiplicity), and the global-max rate."""
import numpy as np

def flow(T, Phi, dt=0.02, n=30000, every=50):
    F = lambda P: (np.eye(len(T)) - P @ P.T) @ T @ P @ (P.T @ T @ P)
    lams = []
    for i in range(n):
        k1 = F(Phi); k2 = F(Phi + dt / 2 * k1); k3 = F(Phi + dt / 2 * k2); k4 = F(Phi + dt * k3)
        Phi = Phi + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
        if i % every == 0: lams.append(np.linalg.eigvalsh(Phi.T @ T @ Phi))
    return Phi, np.array(lams)

def predicted(lam, U, p, k):
    pos = [i for i in np.argsort(-lam) if lam[i] > 0][:p]; neg = [i for i in np.argsort(lam) if lam[i] < 0][:k - p]
    return U[:, pos + neg], lam[pos + neg]

rng = np.random.default_rng(1); n, k = 10, 3; stats = dict(runs=0, limit_ok=0, globmax=0, worst_orth=0.0, worst_mono=0.0)
cases = []
for t in range(30):                                   # generic spectra
    A = rng.standard_normal((n, n)); cases.append(('generic', (A + A.T) / (2 * np.sqrt(n))))
for t in range(10):                                   # repeated eigenvalues (multiplicity 2 and 3)
    V, _ = np.linalg.qr(rng.standard_normal((n, n)))
    ev = np.array([0.9, 0.9, 0.5, 0.2, -0.1, -0.6, -0.6, -0.6, 0.0, 0.3])
    cases.append(('multiplicity', V @ np.diag(ev) @ V.T))
for kind, T in cases:
    lam, U = np.linalg.eigh(T)
    Phi0, _ = np.linalg.qr(rng.standard_normal((n, k)))
    q0 = np.linalg.eigvalsh(Phi0.T @ T @ Phi0); p = int((q0 > 0).sum())
    Phi, L = flow(T, Phi0)
    orth = np.abs(Phi.T @ Phi - np.eye(k)).max(); stats['worst_orth'] = max(stats['worst_orth'], orth)
    # (b): sorted eigenvalues of Q keep their signs and |.| never decreases (tolerance for RK4 drift)
    assert ((L > 0).sum(1) == p).all(), (kind, 'inertia changed')
    neg_part, pos_part = -L[:, :k - p], L[:, k - p:]
    mono = max(0.0, -np.diff(np.abs(L[:, :k - p][:, ::-1]), axis=0).min() if k - p else 0.0,
               -np.diff(pos_part, axis=0).min() if p else 0.0)
    stats['worst_mono'] = max(stats['worst_mono'], mono); assert mono < 1e-9, (kind, mono)
    # (d)/(e): limit subspace = predicted one (projector distance), eigenvalues of Q_inf = predicted eigenvalues
    S, lp = predicted(lam, U, p, k)
    Qinf = np.linalg.eigvalsh(Phi.T @ T @ Phi)
    ok = np.allclose(np.sort(Qinf), np.sort(lp), atol=1e-6)
    if kind == 'generic': ok &= np.linalg.norm(Phi @ Phi.T - S @ S.T) < 1e-4
    assert ok, (kind, Qinf, lp)
    stats['runs'] += 1; stats['limit_ok'] += ok
    stats['globmax'] += np.isclose(np.sum(Qinf ** 2), np.sort(lam ** 2)[-k:].sum(), atol=1e-6)
print(stats)
assert stats['worst_orth'] < 1e-8
