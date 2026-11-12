# Checks for the shadow norm of degree-1 observables O = dGamma(h) = sum h_ij a_i^dag a_j under photonic classical shadows
# (uniformly random passive linear optics on n photons in m modes, photon counting), with asserts.
#  (1) the inverse of the measurement channel on the degree-1 part: M(O_0) = O_0/(m+1), by Monte Carlo of the channel;
#  (2) for every sampled U, the operator inequality behind the upper bound:
#      sum_s <s|w X w^dag|s>^2 w^dag|s><s|w  <=  n (m+1)^2 w^dag (sum_i x_i^2 n_i) w,   X = (m+1) O_0, x = diag(U h0 U^dag);
#  (3) the third-moment identity E sum_i x_i^2 (U g U^dag)_ii = (tr g ||h0||_2^2 + 2 tr(g h0^2)) / ((m+1)(m+2));
#  (4) the lower bound: for sigma = n photons in the top eigenmode of h0 the second moment is at least
#      n (m+1)/(m+2) (||h0||_2^2 + 2||h0||^2) + n(n-1) ||h0||^2 (Monte Carlo, within four standard errors);
#  (5) the exact shadow norm, the largest eigenvalue of A = (m+1)^2 E_U dGamma(K_U)^2 with K_U = U^dag diag(U h0 U^dag) U,
#      from the exact fourth moments of a uniformly random unitary (inverse Gram matrix of the permutations), checked against Monte Carlo,
#      lies between the lower bound of (4) and n^2 (m+1)/(m+2) (||h0||_2^2 + 2||h0||^2), with equality for n = 1;
#  (6) the comparison constant (m^2 - 1)(m + 1) of the general bound for degree 1.
# python -I deg1.py
import itertools, math
import numpy as np
rng = np.random.default_rng(5)


def occ_basis(n, m):
    return [s for s in itertools.product(range(n, -1, -1), repeat=m) if sum(s) == n]


def rand_unitary(m):
    A = rng.normal(size=(m, m)) + 1j * rng.normal(size=(m, m))
    Q, R = np.linalg.qr(A)
    return Q * (np.diag(R) / abs(np.diag(R)))


def omega(U, B, n):
    """Action of the single-photon unitary U on the n-photon occupation-number basis B (permanents)."""
    occ = lambda s: [i for i, c in enumerate(s) for _ in range(c)]
    W = np.zeros((len(B), len(B)), dtype=complex)
    for a, s in enumerate(B):
        ls = occ(s)
        for b, t in enumerate(B):
            lt = occ(t)
            M = U[np.ix_(ls, lt)]
            per = sum(np.prod([M[i, p[i]] for i in range(n)]) for p in itertools.permutations(range(n)))
            W[a, b] = per / math.sqrt(np.prod([math.factorial(c) for c in s]) * np.prod([math.factorial(c) for c in t]))
    return W


def dgamma(h, B):
    """Matrix of sum_ij h_ij a_i^dag a_j on the occupation-number basis B."""
    idx = {s: i for i, s in enumerate(B)}
    D = np.zeros((len(B), len(B)), dtype=complex)
    for b, t in enumerate(B):
        for i in range(len(t)):
            for j in range(len(t)):
                if t[j] == 0:
                    continue
                u = list(t); amp = math.sqrt(u[j]); u[j] -= 1; amp *= math.sqrt(u[i] + 1); u[i] += 1
                D[idx[tuple(u)], b] += h[i, j] * amp
    return D

P4 = list(itertools.permutations(range(4)))


def ncyc(p):
    seen, c = set(), 0
    for a in range(len(p)):
        if a not in seen:
            c += 1; j = a
            while j not in seen:
                seen.add(j); j = p[j]
    return c


def weingarten(m):
    """Moment matrix of U(m) for four copies: pseudo-inverse of the Gram matrix m^{#cycles(s^-1 t)}."""
    inv = lambda p: tuple(sorted(range(4), key=lambda i: p[i]))
    comp = lambda p, q: tuple(p[q[i]] for i in range(4))
    return np.linalg.pinv(np.array([[m ** ncyc(comp(inv(a), b)) for b in P4] for a in P4], float))


def T_exact(h0):
    """E_U K_U (x) K_U as a 4-index tensor, K_U = U^dag diag(U h0 U^dag) U, by exact fourth moments."""
    m = h0.shape[0]; W = weingarten(m); I = np.eye(m)
    R = []
    for p in P4:
        terms = ['ab', 'cd'] + ['ibkd'[k] + 'jalc'[p[k]] for k in range(4)]
        R.append(np.einsum(','.join(terms) + '->ijkl', h0, h0, I, I, I, I, optimize=True))
    C = [m * m if set(p[:2]) == {0, 1} else m for p in P4]
    T = np.zeros((m,) * 4, complex)
    for a in range(24):
        for b in range(24):
            T += W[a, b] * C[b] * R[a]
    return T


def T_mc(h0, N):
    m = h0.shape[0]; T = np.zeros((m,) * 4, complex)
    for _ in range(N):
        V = rand_unitary(m).conj().T
        x = np.real(np.einsum('ar,ab,br->r', V.conj(), h0, V))
        K = (V * x) @ V.conj().T
        T += np.einsum('ij,kl->ijkl', K, K)
    return T / N


def exact_norm(n, h0):
    m = h0.shape[0]; B = occ_basis(n, m); idx = {t: i for i, t in enumerate(B)}
    E = np.zeros((m, m, len(B), len(B)))
    for b, t in enumerate(B):
        for i in range(m):
            for j in range(m):
                if t[j] == 0:
                    continue
                u = list(t); amp = math.sqrt(u[j]); u[j] -= 1; amp *= math.sqrt(u[i] + 1); u[i] += 1
                E[i, j, idx[tuple(u)], b] += amp
    T = T_exact(h0)
    A = (m + 1) ** 2 * np.einsum('ijkl,ijab,klbc->ac', T, E, E, optimize=True)
    return np.linalg.eigvalsh((A + A.conj().T) / 2).max(), T


def check(n, m, h, samples):
    B = occ_basis(n, m); D = len(B)
    h0 = h - np.trace(h) / m * np.eye(m)
    O0 = dgamma(h0, B)
    assert np.allclose(O0, O0.conj().T) and abs(np.trace(O0)) < 1e-9
    opn = np.abs(np.linalg.eigvalsh(O0)).max()
    nh = np.abs(np.linalg.eigvalsh(h0)).max()
    assert abs(opn - n * nh) < 1e-9                                  # ||O_0|| = n ||h0||
    hs = np.linalg.norm(h0) ** 2
    upper = n * n * (m + 1) / (m + 2) * (hs + 2 * nh ** 2)
    lower = n * (m + 1) / (m + 2) * (hs + 2 * nh ** 2) + n * (n - 1) * nh ** 2
    ev, V = np.linalg.eigh(h0)
    v = V[:, np.argmax(np.abs(ev))]
    # sigma = n photons in mode v: the state (a_v^dag)^n |0> / sqrt(n!), via omega of a unitary with first column v
    Q, _ = np.linalg.qr(np.column_stack([v, rng.normal(size=(m, m - 1)) + 1j * rng.normal(size=(m, m - 1))]))
    Q[:, 0] = v
    psi = omega(Q, B, n)[:, 0]
    sig = np.outer(psi, psi.conj())
    g = rng.normal(size=(m, m)) + 1j * rng.normal(size=(m, m)); g = g @ g.conj().T
    MC = np.zeros((D, D), dtype=complex)
    vals = []; third = []
    for _ in range(samples):
        U = rand_unitary(m)
        W = omega(U, B, n)
        assert np.allclose(W @ O0 @ W.conj().T, dgamma(U @ h0 @ U.conj().T, B))
        x = np.real(np.diag(U @ h0 @ U.conj().T))
        f = np.array([(m + 1) * sum(si * xi for si, xi in zip(s, x)) for s in B])
        A = sum(f[i] ** 2 * np.outer(W[i].conj(), W[i]) for i in range(D))
        R = n * (m + 1) ** 2 * W.conj().T @ np.diag([sum(si * xi ** 2 for si, xi in zip(s, x)) for s in B]) @ W
        assert np.linalg.eigvalsh(R - A).min() > -1e-9                 # (2)
        vals.append(np.real(np.trace(sig @ A)))
        third.append(sum(x[i] ** 2 * np.real((U @ g @ U.conj().T)[i, i]) for i in range(m)))
        # channel: M(O_0) = E_U sum_s <s|W O_0 W^dag|s> W^dag|s><s|W
        MC += sum(np.real((W @ O0 @ W.conj().T)[i, i]) * np.outer(W[i].conj(), W[i]) for i in range(D))
    MC /= samples
    t_exact = (np.trace(g).real * hs + 2 * np.trace(g @ h0 @ h0).real) / ((m + 1) * (m + 2))
    t_mc, t_se = np.mean(third), np.std(third) / math.sqrt(samples)
    assert abs(t_mc - t_exact) <= 4 * t_se + 1e-12, (t_mc, t_exact, t_se)                                   # (3)
    assert np.linalg.norm(MC - O0 / (m + 1)) <= 0.15 * np.linalg.norm(O0) / (m + 1) * max(1, 30 / math.sqrt(samples)) # (1)
    lv, lse = np.mean(vals), np.std(vals) / math.sqrt(samples)
    assert lv + 4 * lse >= lower                                                                                # (4)
    top, T = exact_norm(n, h0)                                                                                  # (5)
    Tm = T_mc(h0, 20000)
    assert np.linalg.norm(Tm - T) <= 0.05 * np.linalg.norm(T), np.linalg.norm(Tm - T) / np.linalg.norm(T)
    assert lower * (1 - 1e-9) <= top <= upper * (1 + 1e-9)
    if n == 1:
        assert abs(top - upper) <= 1e-9 * upper
    old = (m * m - 1) * (m + 1)
    print(f"n = {n}, m = {m}: ||h0||_2^2/||h0||^2 = {hs / nh ** 2:.2f}; ||O0||_P^2/||O0||^2 = {top / opn ** 2:.3f} exactly, "
          f"bounds [{lower / opn ** 2:.3f}, {upper / opn ** 2:.3f}]; sigma = |n> in top mode {lv / opn ** 2:.3f} +- {lse / opn ** 2:.3f}; "
          f"general bound for degree 1: {old}")

for n, m, samples in ((1, 3, 1500), (2, 2, 1500), (2, 3, 1500), (2, 4, 1200), (3, 3, 800), (2, 6, 600)):
    e1 = np.zeros((m, m)); e1[0, 0] = 1
    hop = np.zeros((m, m)); hop[0, 1] = hop[1, 0] = 1
    flat = np.diag([1.0 if i % 2 == 0 else -1.0 for i in range(m)])
    for h in (e1, hop, flat):
        check(n, m, h, samples)
print("degree-1 photonic shadow checks: ok")
