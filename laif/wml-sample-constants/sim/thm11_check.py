"""Checks for Theorem 11 (K jump operators, one program state per operator, rounds in uniformly random order).
Each round applies the one-copy step of Theorem 9 once for every operator, with step time D = t/m, in a uniformly random order.
(a) Second order: the round R satisfies ||R - e^{D A} - D^2 F||_dia <= D^3 [K(K-1) b(2a + D b)/2 + (e/6) K^3 ((a + D b)^3 + a^3)]
    with A = sum_k L_k, F = sum_k (E_k - L_k^2/2), a = 2, b = d/2 (full diamond norm), when K D (a + D b) <= 1.
(b) The m-round error (half diamond norm) is at most phi t^2/m + g t^3/m^2, phi = ||F||_dia/2, g = 0.57 d K^2 + 5.4 K^3,
    for m >= max(2.5 K t, d t).
(c) phi <= ((d+1)/4 + 1/d) kappa, kappa = ||sum_k L_k^+ L_k||, through the split F = P - N with P, N completely positive and
    P*(I) <= ((d+1)/4 + 1/d) kappa I (one shared term in G = sum_k K_k^2), and phi <= sum_k e_{L_k}.
(d) N err/t^2 -> K phi (N = K m copies), and for the decay family L_k = |0><k| at d = 5, phi stays 3/4 for K = 1..4."""
import os, itertools
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"): os.environ[_v] = "1"
import numpy as np, cvxpy as cp
from scipy.linalg import expm
from step_kraus import kraus, step

def superop(f, d):
    M = np.zeros((d * d, d * d), complex)
    for i in range(d):
        for j in range(d):
            E = np.zeros((d, d), complex); E[i, j] = 1; M[:, i * d + j] = f(E).reshape(-1)
    return M

def choi(M, d):
    J = np.zeros((d * d, d * d), complex)
    for i in range(d):
        for j in range(d):
            E = np.zeros(d * d, complex); E[i * d + j] = 1
            J += np.kron(np.outer(np.eye(d)[i], np.eye(d)[j]), (M @ E).reshape(d, d))
    return J

def half_dia(M, d):
    J = choi(M, d); J = (J + J.conj().T) / 2; Z = cp.Variable((d * d, d * d), hermitian=True); s = cp.Variable()
    cp.Problem(cp.Minimize(s), [Z >> 0, Z - J >> 0, s * np.eye(d) - cp.partial_trace(Z, [d, d], axis=1) >> 0]).solve(solver="CLARABEL")
    return s.value

def lind(L, d):
    K = L.conj().T @ L
    return superop(lambda r: L @ r @ L.conj().T - (K @ r + r @ K) / 2, d)

def sandwich(X, Y, d):                      # rho -> X rho Y^+
    return superop(lambda r: X @ r @ Y.conj().T, d)

def steps(Ls, d, D):
    ops = kraus(d, D); return [superop(lambda r, L=L: step(ops, r, L), d) for L in Ls]

def round_map(S):
    orders = list(itertools.permutations(range(len(S))))
    return sum(np.linalg.multi_dot([S[k] for k in reversed(o)] + [np.eye(S[0].shape[0])]) for o in orders) / len(orders)

def F_of(Ls, d):
    out = 0
    for L in Ls:
        D = 0.01; S = superop(lambda r: step(kraus(d, D), r, L), d); A = lind(L, d)
        E = (S - np.eye(d * d) - D * A) / D ** 2
        S2 = superop(lambda r: step(kraus(d, 2 * D), r, L), d)
        assert np.abs(S2 - np.eye(d * d) - 2 * D * A - 4 * D * D * E).max() < 1e-9      # the step is exactly quadratic in D
        out = out + E - A @ A / 2
    return out

def split(Ls, d):
    """P and N of (c): F = P - N."""
    Id = np.eye(d); P = 0; N = 0; G = sum((L.conj().T @ L) @ (L.conj().T @ L) for L in Ls); g = np.linalg.norm(G, 2); y = g / 8
    for L in Ls:
        K = L.conj().T @ L; Z = L @ K + K @ L; a, b = np.sqrt(d) / 2, 1 / (2 * np.sqrt(d))
        P = P + superop(lambda r, K=K: 0.25 * np.trace(r @ K) * Id, d) + sandwich(Z, Z, d) / (4 * d)
        N = N + sandwich(a * L - b * Z, a * L - b * Z, d) + 0.5 * sandwich(L @ L, L @ L, d) + 0.25 * sandwich(K, K, d)
    W = np.sqrt(y) * Id + G / (8 * np.sqrt(y))
    P = P + y * np.eye(d * d) + sandwich(G, G, d) / (64 * y); N = N + sandwich(W, W, d)
    return P, N

def adjoint_unit(M, d):                     # M*(I) from the superoperator matrix (row-major vec)
    v = M.conj().T @ np.eye(d).reshape(-1); return v.reshape(d, d)

rng = np.random.default_rng(21)
def rand_op(d, rank):
    L = sum(np.outer(rng.normal(size=d) + 1j * rng.normal(size=d), rng.normal(size=d) + 1j * rng.normal(size=d)) for _ in range(rank))
    return L / np.linalg.norm(L)
def decay(d, K):
    out = []
    for k in range(1, K + 1):
        L = np.zeros((d, d)); L[0, k] = 1; out.append(L)
    return out

cases = [("identical rank one, d=3, K=3", 3, [rand_op(3, 1)] * 3), ("random rank one, d=3, K=2", 3, [rand_op(3, 1) for _ in range(2)]),
         ("random full rank, d=3, K=3", 3, [rand_op(3, 3) for _ in range(3)]), ("random rank two, d=4, K=2", 4, [rand_op(4, 2) for _ in range(2)]),
         ("decay, d=4, K=3", 4, decay(4, 3))]

for name, d, Ls in cases:
    K = len(Ls); F = F_of(Ls, d); phi = half_dia(F, d)
    kappa = np.linalg.norm(sum(L.conj().T @ L for L in Ls), 2)
    # (c)
    P, N = split(Ls, d)
    assert np.abs(P - N - F).max() < 1e-8
    for M in (P, N):
        assert np.linalg.eigvalsh((choi(M, d) + choi(M, d).conj().T) / 2).min() > -1e-10
    PI = adjoint_unit(P, d)
    assert np.linalg.eigvalsh(((d + 1) / 4 + 1 / d) * kappa * np.eye(d) - (PI + PI.conj().T) / 2).min() > -1e-10
    e_single = [half_dia(F_of([L], d), d) for L in Ls]
    assert phi <= ((d + 1) / 4 + 1 / d) * kappa + 1e-7 and phi <= sum(e_single) + 1e-7
    # (a)
    a, b = 2.0, d / 2
    A = sum(lind(L, d) for L in Ls)
    for D in (0.02, 0.1):
        if K * D * (a + D * b) > 1: continue
        R = round_map(steps(Ls, d, D))
        r = 2 * half_dia(R - expm(D * A) - D * D * F, d)
        assert r <= D ** 3 * (K * (K - 1) * b * (2 * a + D * b) / 2 + np.e / 6 * K ** 3 * ((a + D * b) ** 3 + a ** 3)) + 1e-9, (name, D, r)
    # (b)
    g = 0.57 * d * K * K + 5.4 * K ** 3
    for t in (0.05, 0.3, 1.0):
        for m in sorted({int(np.ceil(max(2.5 * K * t, d * t))), 16}):
            R = round_map(steps(Ls, d, t / m))
            err = half_dia(np.linalg.matrix_power(R, m) - expm(t * A), d)
            assert err <= phi * t * t / m + g * t ** 3 / m ** 2 + 1e-8, (name, t, m, err)
    # (d)
    t, m = 0.02, 32
    lead = K * m * half_dia(np.linalg.matrix_power(round_map(steps(Ls, d, t / m)), m) - expm(t * A), d) / t ** 2
    assert abs(lead - K * phi) <= 0.03 * K * phi, (name, lead, K * phi)
    print("%-30s phi = %.4f, sum e_L = %.4f, ((d+1)/4+1/d) kappa = %.4f, N err/t^2 at t=0.02 = %.4f vs K phi = %.4f"
          % (name, phi, sum(e_single), ((d + 1) / 4 + 1 / d) * kappa, lead, K * phi), flush=True)
for K in (1, 2, 3, 4):
    phi = half_dia(F_of(decay(5, K), 5), 5); assert abs(phi - 0.75) < 1e-5, (K, phi)
print("(d) decay family d=5: phi = 3/4 for K = 1, 2, 3, 4")
print("ok")
