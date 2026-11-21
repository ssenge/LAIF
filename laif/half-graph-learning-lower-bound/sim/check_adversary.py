"""Spectral adversary for learning a column-permuted half graph (threshold queries [pi(j) <= i]).

Gamma[pi, pi o (j j')] = 1/|pi(j) - pi(j')|. Checks:
  * ||Gamma|| equals the row sum n H_{n-1} - (n-1);
  * for every query (i, j), ||Gamma o D_(i,j)|| <= ||K_i|| < pi, where K_i[a, b] = 1/(b - a), a <= i < b;
  * the block-norm bound ||Gamma o D_q|| <= ||K_i|| holds with the exact matrices.
"""
import itertools, math
import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as sla

def norm_sym(M):
    if M.shape[0] <= 800:
        return float(np.max(np.abs(np.linalg.eigvalsh(M.toarray()))))
    v = sla.eigsh(M, k=1, which='LM', return_eigenvectors=False, tol=1e-10)
    return float(abs(v[0]))

def hilbert_block(n, i):
    K = np.array([[1.0 / (b - a) for b in range(i + 1, n + 1)] for a in range(1, i + 1)])
    return float(np.linalg.norm(K, 2))

for n in range(2, 8):
    perms = list(itertools.permutations(range(1, n + 1)))
    idx = {p: k for k, p in enumerate(perms)}
    rows, cols, vals = [], [], []
    for p in perms:
        for j in range(n):
            for jj in range(j + 1, n):
                q = list(p); q[j], q[jj] = q[jj], q[j]
                rows.append(idx[p]); cols.append(idx[tuple(q)]); vals.append(1.0 / abs(p[j] - p[jj]))
    N = len(perms)
    G = sp.csr_matrix((vals, (rows, cols)), shape=(N, N))
    assert abs(G - G.T).max() < 1e-12
    R = n * sum(1.0 / d for d in range(1, n)) - (n - 1)
    rs = np.asarray(G.sum(axis=1)).ravel()
    assert np.allclose(rs, R)
    gn = norm_sym(G)
    assert abs(gn - R) < 1e-8, (n, gn, R)
    worst = 0.0
    for j in range(n):
        for i in range(1, n):
            r2, c2, v2 = [], [], []
            Gc = G.tocoo()
            for a, b, w in zip(Gc.row, Gc.col, Gc.data):
                if (perms[a][j] <= i) != (perms[b][j] <= i):
                    r2.append(a); c2.append(b); v2.append(w)
            Gq = sp.csr_matrix((v2, (r2, c2)), shape=(N, N))
            qn = norm_sym(Gq)
            hb = hilbert_block(n, i)
            assert qn <= hb + 1e-9 and hb < math.pi, (n, i, j, qn, hb)
            worst = max(worst, qn)
    print(f"n = {n}: ||Gamma|| = {gn:.4f} = n H_(n-1) - (n-1), max_q ||Gamma_q|| = {worst:.4f} < pi, ratio {gn / worst:.3f}")

# Hilbert-block norms stay below pi for larger n
for n in (50, 200, 800):
    m = max(hilbert_block(n, i) for i in range(1, n, max(1, n // 40)))
    assert m < math.pi
    print(f"n = {n}: max_i ||K_i|| = {m:.4f} < pi")
