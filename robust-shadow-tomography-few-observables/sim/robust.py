# Robust shadow tomography with random linear combinations, simulated. Checks with asserts:
#  (1) X_i = M a_i lambda is unbiased for tr(O_i rho), where a is uniform on the unit sphere and lambda is the outcome of the
#      eigenbasis measurement of A_a = sum_i a_i O_i;
#  (2) the moment bound ||X_i - mu||_h <= 2 kappa sqrt(h M) for h = 2, 4, 6 (with kappa replaced by the largest sampled ||A_a||,
#      which is at most kappa, so the check is stronger than the lemma);
#  (3) under corruption of a gamma-fraction of the records, the truncated mean of X_i has error of order gamma sqrt(M) kappa,
#      at most 4 gamma sqrt(M ln(1/gamma)) kappa, and for gamma >= 0.02
#      below that of classical shadows with the truncated mean, whose error scales with ||O_i||_HS = sqrt(d).
# Families: four random observables U^dag Z U in dimension d = 128, and ten anticommuting Pauli observables on 5 qubits (kappa = 1).
# python -I robust.py
import sys
import numpy as np


def haar(d, rng):
    z = (rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))


def haar_family(d, M, rng):
    Z = np.diag([1.0] * (d // 2) + [-1.0] * (d // 2))
    return [u.conj().T @ Z @ u for u in (haar(d, rng) for _ in range(M))]


def majorana(n):
    X = np.array([[0, 1], [1, 0]], complex); Y = np.array([[0, -1j], [1j, 0]]); Zm = np.diag([1.0, -1.0]).astype(complex)
    I = np.eye(2, dtype=complex)
    out = []
    for k in range(n):
        for P in (X, Y):
            ops = [Zm] * k + [P] + [I] * (n - k - 1)
            m = ops[0]
            for o in ops[1:]:
                m = np.kron(m, o)
            out.append(m)
    return out


def random_state(d, rng):
    v = rng.standard_normal(d) + 1j * rng.standard_normal(d)
    v /= np.linalg.norm(v)
    return np.outer(v, v.conj())


def combo_records(O, rho, n, rng):
    """n records (a, lambda) of the random-combination scheme; returns X (n, M) and the largest ||A_a|| seen."""
    M = len(O)
    X = np.empty((n, M)); kmax = 0.0
    for t in range(n):
        a = rng.standard_normal(M); a /= np.linalg.norm(a)
        A = sum(ai * Oi for ai, Oi in zip(a, O))
        w, V = np.linalg.eigh(A)
        p = np.real(np.einsum("ij,jk,ki->i", V.conj().T, rho, V)); p = np.clip(p, 0, None); p /= p.sum()
        lam = w[rng.choice(len(w), p=p)]
        kmax = max(kmax, np.abs(w).max())
        X[t] = M * a * lam
    return X, kmax


def shadow_records(O, rho, n, rng):
    """Classical shadows with uniformly random bases: X'_i = (d + 1) <v|O_i|v> - tr O_i."""
    d = rho.shape[0]
    X = np.empty((n, len(O)))
    for t in range(n):
        U = haar(d, rng)
        p = np.real(np.einsum("ij,jk,ki->i", U.conj().T, rho, U)); p = np.clip(p, 0, None); p /= p.sum()
        v = U[:, rng.choice(d, p=p)]
        X[t] = [(d + 1) * np.real(v.conj() @ Oi @ v) - np.real(np.trace(Oi)) for Oi in O]
    return X


def truncated_mean(x, g):
    x = np.sort(x); k = int(np.ceil(g * len(x)))
    return x[k:len(x) - k].mean()


def attack(x, gamma, rng):
    """Replace the gamma-fraction of smallest samples by the value just inside the upper trimming boundary (a strong
    one-sided shift against the truncated mean with trimming 2 gamma)."""
    y = x.copy(); n = len(x); k = int(gamma * n)
    q = np.sort(x)[n - 1 - int(np.ceil(2 * gamma * n))]
    y[np.argsort(x)[:k]] = q
    return y


def run(name, O, rng, n=8000, gammas=(0.01, 0.02, 0.05)):
    d = O[0].shape[0]; M = len(O)
    rho = random_state(d, rng)
    mu = np.array([np.real(np.trace(Oi @ rho)) for Oi in O])
    X, kmax = combo_records(O, rho, n, rng)
    se = X.std(axis=0) / np.sqrt(n)
    assert np.all(np.abs(X.mean(axis=0) - mu) <= 5 * se), (name, X.mean(axis=0) - mu, se)
    for h in (2, 4, 6):
        mom = (np.abs(X - mu) ** h).mean(axis=0) ** (1 / h)
        assert np.all(mom <= 2 * kmax * np.sqrt(h * M)), (name, h, mom, kmax)
    S = shadow_records(O, rho, n, rng)
    hs = max(np.sqrt(np.real(np.trace(Oi @ Oi))) for Oi in O)
    print(f"{name}: d = {d}, M = {M}, sampled kappa >= {kmax:.3f}, max ||O_i||_HS = {hs:.1f}; unbiased, moment bound ok")
    for g in gammas:
        ec = max(abs(truncated_mean(attack(X[:, i], g, rng), 2 * g) - mu[i]) for i in range(M))
        es = max(abs(truncated_mean(attack(S[:, i], g, rng), 2 * g) - mu[i]) for i in range(M))
        scale = g * np.sqrt(M * np.log(1 / g)) * kmax
        print(f"  gamma = {g:.2f}: error {ec:.4f} (combination), {es:.4f} (classical shadows); "
              f"error/(gamma sqrt(M ln(1/gamma)) kappa) = {ec / scale:.2f}", flush=True)
        assert ec / scale <= 4.0, (name, g, ec, scale)
        if g >= 0.02:
            assert ec < es, (name, g, ec, es)


if __name__ == "__main__":
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
    run("random observables", haar_family(128, 4, rng), rng)
    run("anticommuting Paulis", majorana(5), rng)
    print("robust checks: ok")
