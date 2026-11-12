"""Theorem 4 instances: P0 = c I + (1-c)(S/2 + J/(2N)) and P_j = P0 + 2 L eps u_j u_j^T, u_j = Pi w_j / |Pi w_j|.
Checks: symmetric, nonnegative, doubly stochastic, second singular values, frame sum_j u_j u_j^T = N/(N-2) Pi_sym,
||U_j - U_0|| <= 2 sqrt(2) eps sqrt(L) for the reflection block-encoding, and the threshold weights of Theorem 2."""
import numpy as np
from scipy.linalg import sqrtm
from filter import filt
from numpy.polynomial import chebyshev as C


def instances(N, L, eps):
    c = 1 - 2 * L * (1 + eps)
    S = np.zeros((N, N))
    for i in range(0, N, 2):
        S[i, i + 1] = S[i + 1, i] = 1
    P0 = c * np.eye(N) + (1 - c) * (S / 2 + np.ones((N, N)) / (2 * N))
    Pi = np.eye(N) - np.ones((N, N)) / N
    us = []
    for j in range(0, N, 2):
        w = np.zeros(N); w[j] = w[j + 1] = 1
        v = Pi @ w
        us.append(v / np.linalg.norm(v))
    return P0, [P0 + 2 * L * eps * np.outer(u, u) for u in us], us


def benc(P):
    B = np.real(sqrtm(np.eye(len(P)) - P @ P))
    return np.block([[P, B], [B, -P]])


def sv2(P):
    return np.sort(np.linalg.svd(P, compute_uv=False))[-2]


def main():
    for N, L, eps in [(8, 0.2, 0.5), (16, 0.05, 0.2), (32, 0.01, 0.1), (64, 0.1, 1.0)]:
        P0, Ps, us = instances(N, L, eps)
        U0 = benc(P0)
        assert np.allclose(U0 @ U0.T, np.eye(2 * N))
        assert abs(sv2(P0) - (1 - L * (1 + eps))) < 1e-10
        F = sum(np.outer(u, u) for u in us)
        sym = np.zeros((N, N))
        for i in range(0, N, 2):
            sym[i:i + 2, i:i + 2] = 0.5
        assert np.allclose(F, N / (N - 2) * (sym - np.ones((N, N)) / N))
        dmax = 0
        for P in Ps:
            assert np.allclose(P, P.T) and P.min() >= -1e-12
            assert np.allclose(P.sum(0), 1) and np.allclose(P.sum(1), 1)
            assert abs(sv2(P) - (1 - L * (1 - eps))) < 1e-10
            Uj = benc(P)
            assert np.allclose(Uj @ Uj.T, np.eye(2 * N)) and np.allclose(Uj[:N, :N], P)
            dmax = max(dmax, np.linalg.norm(Uj - U0, 2))
        bound = 2 * np.sqrt(2) * eps * np.sqrt(L)
        assert dmax <= bound
        # Theorem 2 weights: filter with Delta = L, t = eps, alpha = 1/(8 sqrt N)
        c, D, _ = filt(L, eps, 1 / (8 * np.sqrt(N)))
        f1 = C.chebval(1.0, c)
        wt = lambda P: np.sum(C.chebval(np.linalg.svd(P, compute_uv=False), c) ** 2) / N
        assert wt(P0) <= (f1 ** 2 + 1 / 64) / N and wt(Ps[0]) >= (f1 ** 2 + 9 / 16) / N
        print(f"N = {N:3d}, L = {L}, eps = {eps}: ||U_j - U_0|| max {dmax:.4f} <= {bound:.4f}; "
              f"weights N*W: no {N * wt(P0):.4f} <= {f1 ** 2 + 1 / 64:.4f}, yes {N * wt(Ps[0]):.4f} >= {f1 ** 2 + 9 / 16:.4f}")
    print("lower: all asserts passed")


if __name__ == "__main__":
    main()
