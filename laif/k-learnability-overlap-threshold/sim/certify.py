"""Exact certificate that n pure states with all overlaps |<psi_i|psi_j>| <= t0 need not be k-learnable.

Input: a numerical Gram matrix G (non-k-incoherent) and a witness X (k-locally PSD, Tr(XG) < 0).
Output: Gaussian-rational G', X' with, in exact arithmetic,
  G' Hermitian PSD, diag(G') = 1, |G'_ij|^2 <= t0^2 for i != j,
  every k x k principal submatrix of X' positive definite, Tr(X'G') < 0.
By [2609.17411, Prop. 10] a multiset of pure states is k-learnable iff its Gram matrix is k-incoherent, and
k-incoherent matrices have Tr(XG) >= 0 for every k-locally PSD X, so the states with Gram G' are not k-learnable.
"""
import itertools, json, sys
from fractions import Fraction as Fr
import numpy as np

DEN = 10 ** 12


def rat(z):
    return (Fr(round(z.real * DEN), DEN), Fr(round(z.imag * DEN), DEN))


def herm_rat(M):
    n = M.shape[0]; R = [[None] * n for _ in range(n)]
    for i in range(n):
        R[i][i] = (rat(M[i, i])[0], Fr(0))
        for j in range(i + 1, n):
            a, b = rat(M[i, j]); R[i][j] = (a, b); R[j][i] = (a, -b)
    return R


def pd_exact(H):
    """Hermitian H (list of (re, im)) is positive definite: LDL^T of the real embedding [[A, -B], [B, A]]."""
    n = len(H); m = 2 * n
    M = [[Fr(0)] * m for _ in range(m)]
    for i in range(n):
        for j in range(n):
            a, b = H[i][j]
            M[i][j] = a; M[i + n][j + n] = a; M[i][j + n] = -b; M[i + n][j] = b
    for p in range(m):
        if M[p][p] <= 0: return False
        for r in range(p + 1, m):
            if M[r][p]:
                f = M[r][p] / M[p][p]
                for c in range(p, m): M[r][c] -= f * M[p][c]
    return True


def tr_prod(X, G):
    n = len(G); s = Fr(0)
    for i in range(n):
        for j in range(n):
            a, b = X[i][j]; c, d = G[j][i]
            s += a * c - b * d
    return s


def certify(G, X, k, eta=Fr(1, 10 ** 8), mu=Fr(1, 10 ** 8)):
    n = G.shape[0]
    Gr = herm_rat(G)
    # G' = (G_r + eta I)/(1 + eta) has unit diagonal; it must be positive definite exactly
    Gp = [[((Gr[i][j][0] + (eta if i == j else 0)) / (1 + eta), Gr[i][j][1] / (1 + eta)) for j in range(n)] for i in range(n)]
    for i in range(n): Gp[i][i] = (Fr(1), Fr(0))
    assert pd_exact(Gp), "G' not PSD"
    t2 = max(Gp[i][j][0] ** 2 + Gp[i][j][1] ** 2 for i in range(n) for j in range(n) if i != j)
    Xr = herm_rat(X)
    Xp = [[(Xr[i][j][0] + (mu if i == j else 0), Xr[i][j][1]) for j in range(n)] for i in range(n)]
    for S in itertools.combinations(range(n), k):
        assert pd_exact([[Xp[i][j] for j in S] for i in S]), ("X' block not PD", S)
    tr = tr_prod(Xp, Gp)
    assert tr < 0, ("Tr(X'G') >= 0", float(tr))
    return Gp, Xp, t2, tr


if __name__ == "__main__":
    n, k, gf, xf, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4], sys.argv[5]
    G, X = np.load(gf), np.load(xf)
    sh = Fr(1, int(sys.argv[6])) if len(sys.argv) > 6 else Fr(1, 10 ** 8)
    Gp, Xp, t2, tr = certify(G, X, k, sh, sh)
    # rational upper bound t0 >= sqrt(t2), rounded up at 1e-9
    t0 = Fr(int(float(t2) ** 0.5 * 10 ** 9) + 1, 10 ** 9)
    assert t0 * t0 >= t2
    W = ((k - 1) / ((n - 1) * (n - k + 1))) ** 0.5
    print(f"n={n} k={k}: certified non-k-learnable Gram with max overlap <= t0 = {float(t0):.9f}; (4) = {W:.9f}; "
          f"t0 - W = {float(t0) - W:.3e}; (6) = {(k - 1) / (n - 1):.6f}; Tr(X'G') = {float(tr):.3e}")
    enc = lambda M: [[[str(a), str(b)] for a, b in row] for row in M]
    json.dump({"n": n, "k": k, "t0": str(t0), "G": enc(Gp), "X": enc(Xp)}, open(out, "w"))
