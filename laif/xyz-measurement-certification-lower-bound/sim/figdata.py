"""Data for the paper figure: one-copy H^2 of the pair of Theorem 4 at lam = 0.2, n = 1..14:
the bound lam^2 (2/3)^n/(1 - lam), the largest value over fixed settings, and the optimum over adaptive trees.
Writes h2.csv (or the path given as argument). Same formulas as mixedpair.py."""
import itertools, sys, numpy as np
from math import comb
from functools import lru_cache
s3 = 1 / np.sqrt(3); th = np.arccos(s3)
a = np.array([np.cos(th / 2), np.exp(1j * np.pi / 4) * np.sin(th / 2)]); ab = np.array([-a[1].conj(), a[0].conj()])
AX = {'X': np.array([[1, 1], [1, -1]]) / np.sqrt(2), 'Y': np.array([[1, 1], [1j, -1j]]) / np.sqrt(2), 'Z': np.eye(2)}
amps = [(AX[c][:, x].conj() @ a, AX[c][:, x].conj() @ ab) for c in 'XYZ' for x in (0, 1)]
def leaf(cnt, n, lam):
    A = np.prod([amps[k][0] ** cnt[k] for k in range(6)]); B = np.prod([amps[k][1] ** cnt[k] for k in range(6)])
    d = 2 ** n
    return np.sqrt(((1 - lam) / d + lam * abs(A + B) ** 2 / 2) * ((1 - lam) / d + lam * abs(A - B) ** 2 / 2))
def fixed(n, lam):
    best = 0
    for nX in range(n + 1):
        for nY in range(n + 1 - nX):
            nZ = n - nX - nY; aff = 0
            for kX, kY, kZ in itertools.product(range(nX + 1), range(nY + 1), range(nZ + 1)):
                cnt = (nX - kX, kX, nY - kY, kY, nZ - kZ, kZ)
                aff += comb(nX, kX) * comb(nY, kY) * comb(nZ, kZ) * leaf(cnt, n, lam)
            best = max(best, 1 - aff)
    return best
def adaptive(n, lam):
    @lru_cache(None)
    def f(cnt):
        if sum(cnt) == n: return leaf(cnt, n, lam)
        return min(sum(f(tuple(c + (1 if k == 2 * ax + x else 0) for k, c in enumerate(cnt))) for x in (0, 1)) for ax in range(3))
    return 1 - f((0,) * 6)
lam = 0.2
out_path = sys.argv[1] if len(sys.argv) > 1 else 'h2.csv'
with open(out_path, 'w') as out:
    out.write('n,bound,fixed,adaptive\n')
    for n in range(1, 15):
        b, fx, ad = lam ** 2 * (2 / 3) ** n / (1 - lam), fixed(n, lam), adaptive(n, lam)
        assert ad <= b * (1 + 1e-9) and fx <= ad * (1 + 1e-9)
        out.write(f'{n},{b:.6e},{fx:.6e},{ad:.6e}\n')
print(open(out_path).read())
