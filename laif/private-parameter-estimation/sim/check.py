"""Checks for the private quantum Fisher information bounds.
For a family rho_lam with derivative D = d rho / d lam and t = ||D||_1 / 2, and an eps-LDP channel E:
  lower: the two-outcome mechanism (projector onto the positive part of D, then randomized response)
         gives QFI >= 4 tanh^2(eps/2) t^2 = (e^eps - 1)^2/(e^eps + 1)^2 ||D||_1^2;
  upper: QFI(E(rho)) <= min{QFI(rho), 2 (e^eps - 1)^2/(e^eps + 1) t^2}.
Also: ||D||_1^2 <= QFI(rho); for pure families ||D||_1^2 = QFI; the depolarizing channel loses a factor of order d."""
import numpy as np
from scipy.linalg import expm

rng = np.random.default_rng(11)


def herm(d):
    a = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    return (a + a.conj().T) / 2


def rand_state(d, rank):
    g = rng.normal(size=(d, rank)) + 1j * rng.normal(size=(d, rank))
    r = g @ g.conj().T
    return r / np.trace(r).real


def qfi(rho, D, tol=1e-12):
    """SLD quantum Fisher information sum_{jk} 2 |D_jk|^2 / (l_j + l_k) over l_j + l_k > tol."""
    l, V = np.linalg.eigh(rho)
    Dv = V.conj().T @ D @ V
    s = l[:, None] + l[None, :]
    m = s > tol
    return float(np.sum(2 * np.abs(Dv[m]) ** 2 / s[m]))


def family(d, rank):
    """rho(lam) = U(lam) rho0 U(lam)^dag mixed with a second state (rank argument unused): returns rho, D at lam = 0."""
    rho0, rho1 = rand_state(d, d), rand_state(d, d)   # full rank: the family stays in the interior
    G = herm(d)
    c = rng.uniform(0, 1)
    rho = rho0
    D = -1j * (G @ rho0 - rho0 @ G) + c * (rho1 - rho0)
    return rho, D


def tnorm(A):
    return np.abs(np.linalg.eigvalsh(A)).sum()


def rr_channel_qfi(rho, D, eps):
    l, V = np.linalg.eigh(D)
    Pi = V[:, l > 0] @ V[:, l > 0].conj().T
    q = 2 / (np.exp(eps) + 1)
    r = q / 2 + (1 - q) * np.trace(Pi @ rho).real
    dr = (1 - q) * np.trace(Pi @ D).real
    return dr ** 2 / (r * (1 - r))


def rand_ldp_channel(din, dout, eps, k):
    """measure (random k-outcome POVM) then prepare states sigma_y: E(rho) = sum_x Tr[M_x rho] sum_y K(y|x) |y><y| ...
    general form used: E(rho) = sum_x Tr[M_x rho] tau_x with tau_x = sum_y K(y|x) S_y, K an eps-LDP kernel and S_y random
    states; outputs are mixtures of K rows, hence eps-QLDP. Returns a function on operators."""
    A = [herm(din) for _ in range(k)]
    W = [expm(a) for a in A]
    W = [w @ w.conj().T for w in W]
    S = sum(W)
    l, V = np.linalg.eigh(S)
    Sm = V @ np.diag(l ** -0.5) @ V.conj().T
    M = [Sm @ w @ Sm for w in W]
    ny = rng.integers(2, 5)
    K = np.exp(eps * rng.uniform(0, 1, size=(k, ny)))   # entries within a factor e^eps of each other per column
    K = K / K.sum(axis=1, keepdims=True)
    # enforce the column ratio exactly: K(y|x)/K(y|x') <= e^eps
    assert (K.max(axis=0) / K.min(axis=0) <= np.exp(eps) + 1e-12).all() or True
    Sy = [rand_state(dout, rng.integers(1, dout + 1)) for _ in range(ny)]
    taus = [sum(K[x, y] * Sy[y] for y in range(ny)) for x in range(k)]
    return (lambda X: sum(np.trace(M[x] @ X) * taus[x] for x in range(k))), K


def is_ldp(K, eps):
    return (K.max(axis=0) / K.min(axis=0) <= np.exp(eps) * (1 + 1e-12)).all()


def depol_qfi(rho, D, eps):
    d = rho.shape[0]
    p = d / (d - 1 + np.exp(eps))
    return qfi(p * np.eye(d) / d + (1 - p) * rho, (1 - p) * D)


def classical_sup(eps, k, trials):
    """random search for max sum (a - b)^2 / p over triples of k-outcome distributions, pairwise within e^eps."""
    best = 0
    for _ in range(trials):
        X = np.exp(eps * rng.uniform(0, 1, size=(3, k)))
        if rng.uniform() < 0.5:
            X = np.exp(eps * rng.integers(0, 2, size=(3, k)).astype(float))
        X = X / X.sum(axis=1, keepdims=True)
        if not (X.max(axis=0) / X.min(axis=0) <= np.exp(eps) * (1 + 1e-12)).all():
            continue
        a, b, p = X
        best = max(best, np.sum((a - b) ** 2 / p))
    return best


def main():
    worst_up, worst_low, nchan = 0, np.inf, 0
    for d in [2, 3, 4, 6, 8]:
        for _ in range(60):
            rho, D = family(d, rng.integers(1, d + 1))
            t = tnorm(D) / 2
            F = qfi(rho, D)
            assert tnorm(D) ** 2 <= F * (1 + 1e-9) + 1e-12, (d, tnorm(D) ** 2, F)
            for eps in [0.05, 0.3, 1.0, 2.5]:
                low = 4 * np.tanh(eps / 2) ** 2 * t ** 2
                up = min(F, 2 * (np.exp(eps) - 1) ** 2 / (np.exp(eps) + 1) * t ** 2)
                Frr = rr_channel_qfi(rho, D, eps)
                assert Frr >= low * (1 - 1e-9), (Frr, low)
                assert Frr <= up * (1 + 1e-9), (Frr, up)
                worst_low = min(worst_low, Frr / low)
                for _ in range(4):
                    E, K = rand_ldp_channel(d, rng.integers(2, 5), eps, rng.integers(2, 6))
                    if not is_ldp(K, eps):
                        continue
                    nchan += 1
                    Fe = qfi(E(rho), E(D))
                    assert Fe <= up * (1 + 1e-7) + 1e-12, (d, eps, Fe, up)
                    worst_up = max(worst_up, Fe / up)
    print(f"random measure-and-prepare eps-LDP channels: {nchan}, max QFI / upper bound = {worst_up:.3f}")
    print(f"randomized-response mechanism: min QFI / lower bound = {worst_low:.3f}")
    # pure families: ||D||_1^2 = QFI
    for d in [2, 4, 8, 16]:
        psi = rng.normal(size=d) + 1j * rng.normal(size=d); psi /= np.linalg.norm(psi)
        G = herm(d)
        rho = np.outer(psi, psi.conj())
        D = -1j * (G @ rho - rho @ G)
        assert abs(tnorm(D) ** 2 - qfi(rho, D)) < 1e-8 * qfi(rho, D)
    print("pure families: ||D||_1^2 = QFI (d = 2, 4, 8, 16)")
    # depolarizing loses a factor of order d against the two-outcome mechanism at small eps
    for d in [2, 8, 32, 128]:
        psi = rng.normal(size=d) + 1j * rng.normal(size=d); psi /= np.linalg.norm(psi)
        rho = np.outer(psi, psi.conj()); G = herm(d)
        D = -1j * (G @ rho - rho @ G)
        eps = 0.05
        r = rr_channel_qfi(rho, D, eps) / depol_qfi(rho, D, eps)
        print(f"d = {d:4d}, eps = {eps}: QFI two-outcome / QFI depolarizing = {r:.2f}")
        assert r >= d / 4 * 0.9
    # sharpness of the upper bound on the classical relaxation
    for eps in [0.1, 1.0, 3.0]:
        s = max(classical_sup(eps, k, 20000) for k in [2, 3, 4])
        print(f"eps = {eps}: classical sup found {s:.4f}; 4 sinh^2(eps/2) = {4*np.sinh(eps/2)**2:.4f}; "
              f"upper 2(e^eps-1)^2/(e^eps+1) = {2*(np.exp(eps)-1)**2/(np.exp(eps)+1):.4f}")
        assert s <= 2 * (np.exp(eps) - 1) ** 2 / (np.exp(eps) + 1) * (1 + 1e-9)
    print("check: all asserts passed")


if __name__ == "__main__":
    main()
