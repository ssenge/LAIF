"""Check the stored certificates cert_{n}{k}.json in exact rational arithmetic.

For each file: G is Hermitian, positive definite, with unit diagonal and |G_ij|^2 <= t0^2 for i != j;
every k x k principal submatrix of X is positive definite; Tr(XG) < 0.
"""
import itertools, json, sys
from fractions import Fraction as Fr
from certify import pd_exact, tr_prod

files = sys.argv[1:] or [f"cert_{nk}.json" for nk in ("54", "53", "63", "64", "65")]
for f in files:
    d = json.load(open(f)); n, k, t0 = d["n"], d["k"], Fr(d["t0"])
    dec = lambda M: [[(Fr(a), Fr(b)) for a, b in row] for row in M]
    G, X = dec(d["G"]), dec(d["X"])
    for M in (G, X):
        assert all(M[i][j] == (M[j][i][0], -M[j][i][1]) for i in range(n) for j in range(n))
    assert all(G[i][i] == (1, 0) for i in range(n))
    assert all(G[i][j][0] ** 2 + G[i][j][1] ** 2 <= t0 * t0 for i in range(n) for j in range(n) if i != j)
    assert pd_exact(G)
    for S in itertools.combinations(range(n), k):
        assert pd_exact([[X[i][j] for j in S] for i in S])
    tr = tr_prod(X, G); assert tr < 0
    W = ((k - 1) / ((n - 1) * (n - k + 1))) ** 0.5
    print(f"{f}: n = {n}, k = {k}, max overlap <= {t0} = {float(t0):.9f}, threshold (4) = {W:.9f}, "
          f"bound of [1, Thm 3] = {(k - 1) / (n - 1):.6f}, Tr(XG) = {float(tr):.3e}: not {k}-learnable")
