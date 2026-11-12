"""Checks for the sharpened agnostic process tomography bounds.
(a) For a pure state phi and any state sigma: d_tr^2 <= ||phi - sigma||_F^2 <= 2 d_tr^2, and
    ||phi - sigma||_F^2 = 1 - 2 <phi|sigma|phi> + tr sigma^2.
(b) Frobenius selection on Choi states: maximizing the fidelity with a pure Choi state minimizes the Frobenius distance.
(c) Finite classes, d_avg: on an empirical input distribution the minimizer of the average infidelity
    also minimizes H(U) = E||U psi U^+ - E(psi)||_F^2 = 2 I(U) - 1 + P, and d(U_sel) <= sqrt(2) opt."""
import numpy as np

rng = np.random.default_rng(11)


def haar_u(d):
    z = (rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))


def rand_channel(d, k, near=None, eps=0.3):
    """Kraus operators: a unitary 'near' mixed with random Kraus noise of weight about eps."""
    G = rng.normal(size=(k * d, d)) + 1j * rng.normal(size=(k * d, d))
    if near is not None:
        G = eps * G / np.linalg.norm(G)
        G[:d] += near
    q, _ = np.linalg.qr(G)
    return [q[i * d:(i + 1) * d] for i in range(k)]


def apply(K, rho):
    return sum(A @ rho @ A.conj().T for A in K)


def dtr(a, b):
    return 0.5 * np.abs(np.linalg.eigvalsh(a - b)).sum()


def rand_state(d):
    v = rng.normal(size=d) + 1j * rng.normal(size=d)
    return v / np.linalg.norm(v)


def main():
    # (a)
    worst = [np.inf, 0]
    for _ in range(3000):
        d = rng.integers(2, 9)
        phi = rand_state(d); P = np.outer(phi, phi.conj())
        r = rng.integers(1, d + 1)
        M = rng.normal(size=(d, r)) + 1j * rng.normal(size=(d, r))
        if rng.random() < 0.5:
            M[:, 0] += rng.uniform(0, 10) * phi
        s = M @ M.conj().T; s /= np.trace(s).real
        t = dtr(P, s); f2 = np.linalg.norm(P - s) ** 2
        assert t ** 2 <= f2 + 1e-12 and f2 <= 2 * t ** 2 + 1e-12
        assert abs(f2 - (1 - 2 * (phi.conj() @ s @ phi).real + np.trace(s @ s).real)) < 1e-12
        worst = [min(worst[0], f2 / t ** 2), max(worst[1], f2 / t ** 2)]
    print(f"(a) ||phi - sigma||_F^2 / d_tr^2 in [{worst[0]:.4f}, {worst[1]:.4f}] within [1, 2]")
    # (b) Choi states of a noisy channel against a class of unitaries
    d = 3
    for _ in range(200):
        Us = [haar_u(d) for _ in range(6)]
        K = rand_channel(d, 3, near=Us[0], eps=rng.uniform(0, 1))
        Om = np.eye(d).reshape(d * d) / np.sqrt(d)
        v = sum(np.kron(np.eye(d), A) @ np.outer(Om, Om) @ np.kron(np.eye(d), A).conj().T for A in K)
        chois = [np.kron(np.eye(d), U) @ Om for U in Us]
        F = [(c.conj() @ v @ c).real for c in chois]
        dF = [np.linalg.norm(v - np.outer(c, c.conj())) / np.sqrt(2) for c in chois]
        assert np.argmax(F) == np.argmin(dF)
        assert all(abs(2 * x ** 2 - (np.trace(v @ v).real + 1 - 2 * f)) < 1e-12 for x, f in zip(dF, F))
    print("(b) fidelity maximizer = Frobenius minimizer on 200 instances")
    # (c)
    ratio = 0
    for _ in range(300):
        d = rng.integers(2, 6)
        Us = [haar_u(d) for _ in range(5)]
        base = Us[rng.integers(5)] if rng.random() < 0.7 else haar_u(d)
        K = rand_channel(d, rng.integers(1, 4), near=base, eps=rng.uniform(0, 1.5))
        psis = [rand_state(d) for _ in range(400)]
        I, H, D = np.zeros(5), np.zeros(5), np.zeros(5)
        for p in psis:
            rho = np.outer(p, p.conj()); out = apply(K, rho)
            for i, U in enumerate(Us):
                q = U @ p; Q = np.outer(q, q.conj())
                I[i] += 1 - (q.conj() @ out @ q).real
                H[i] += np.linalg.norm(Q - out) ** 2
                D[i] += dtr(Q, out) ** 2
        I, H, D = I / 400, H / 400, D / 400
        Pur = np.mean([np.trace(apply(K, np.outer(p, p.conj())) @ apply(K, np.outer(p, p.conj()))).real for p in psis])
        assert np.allclose(H, 2 * I - 1 + Pur)
        sel = np.argmin(I)
        assert sel == np.argmin(H)
        opt = np.sqrt(D.min()); got = np.sqrt(D[sel])
        assert got <= np.sqrt(2) * opt + 1e-12
        if opt > 1e-9:
            ratio = max(ratio, got / opt)
    print(f"(c) H = 2I - 1 + P, same minimizer, d(U_sel) <= sqrt2 opt on 300 instances; largest ratio {ratio:.4f}")
    # (d) one qubit: ||phi - sigma||_F^2 = 2 d_tr^2 exactly, so the infidelity minimizer attains opt
    for _ in range(200):
        Us = [haar_u(2) for _ in range(5)]
        K = rand_channel(2, rng.integers(1, 4), near=Us[0], eps=rng.uniform(0, 1.5))
        I, D = np.zeros(5), np.zeros(5)
        for p in [rand_state(2) for _ in range(200)]:
            out = apply(K, np.outer(p, p.conj()))
            for i, U in enumerate(Us):
                q = U @ p; Q = np.outer(q, q.conj())
                assert abs(np.linalg.norm(Q - out) ** 2 - 2 * dtr(Q, out) ** 2) < 1e-12
                I[i] += 1 - (q.conj() @ out @ q).real
                D[i] += dtr(Q, out) ** 2
        assert D[np.argmin(I)] <= D.min() + 1e-12
    print("(d) one qubit: ||phi - sigma||^2 = 2 d_tr^2 and the infidelity minimizer attains opt on 200 instances")
    print("check: all asserts passed")


if __name__ == "__main__":
    main()
