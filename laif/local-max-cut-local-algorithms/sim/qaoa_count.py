"""Depth-1 QAOA for LocalMaxCut on the d-regular tree by counting: the value of qaoa_tree.value, with every sum over
neighbour or child assignments replaced by a sum over the number of disagreeing vertices. Children and grandchildren
enter through binomial sums; the d neighbours of the root are i.i.d. types (a_u, b_u, z_u) and enter through a
dynamic program over the capped counts (min(n_a, k), min(n_b, k), min(n_z, k)). Works in mpmath or float."""
import sys
from math import comb
import numpy as np

def value(d, g, b, mp=None):
    k = -(-d // 2)
    if mp is None:
        exp = lambda x: np.exp(1j * x); cos, sin, one = np.cos(b), np.sin(b), 1.0
        U = [[cos, -1j * sin], [-1j * sin, cos]]; conj = np.conj
    else:
        exp = lambda x: mp.expj(x); cos, sin, one = mp.cos(b), mp.sin(b), mp.mpf(1)
        U = [[cos, -1j * sin], [-1j * sin, cos]]; conj = mp.conj
    sat = lambda c: 1 if c >= k else 0
    half = one / 2
    def binavg(n, f):                      # average of f(m) over m ~ Bin(n, 1/2)
        return sum(comb(n, m) * f(m) for m in range(n + 1)) * half ** n
    CF = {(ux, uy, rc): binavg(d - 1, lambda m: exp(g * (sat((ux != rc) + m) - sat((uy != rc) + m))))
          for ux in (0, 1) for uy in (0, 1) for rc in (0, 1)}
    def BR(vx, vy, ux, uy):
        c0, c1 = CF[(ux, uy, 0)], CF[(ux, uy, 1)]; n = d - 1
        tot = 0
        for m in range(n + 1):             # m children with r_c = 1
            dx = m if ux == 0 else n - m; dy = m if uy == 0 else n - m
            tot += comb(n, m) * c1 ** m * c0 ** (n - m) * exp(g * (sat((vx != ux) + dx) - sat((vy != uy) + dy)))
        return tot * half ** n
    BRt = {key: BR(*key) for key in np.ndindex(2, 2, 2, 2)}
    total = 0
    for av in (0, 1):
        for bv in (0, 1):
            for zv in (0, 1):
                wv = conj(U[zv][av]) * U[zv][bv] * half
                types = [(int(au != av), int(bu != bv), int(zu != zv), conj(U[zu][au]) * U[zu][bu] * BRt[(av, bv, au, bu)] * half)
                         for au in (0, 1) for bu in (0, 1) for zu in (0, 1)]
                if mp is None:                       # vectorized DP over capped counts
                    D = np.zeros((k + 1,) * 3, complex); D[0, 0, 0] = 1
                    for _ in range(d):
                        N = np.zeros((k + 2,) * 3, complex)
                        for al, be, ze, w in types:
                            N[al:al + k + 1, be:be + k + 1, ze:ze + k + 1] += w * D
                        N[k] += N[k + 1]; N[:, k] += N[:, k + 1]; N[:, :, k] += N[:, :, k + 1]
                        D = N[:k + 1, :k + 1, :k + 1]
                    x = np.arange(k + 1); ph = np.exp(1j * g * ((x[:, None] >= k).astype(float) - (x[None, :] >= k)))
                    total += wv * np.sum(D[:, :, k] * ph)
                    continue
                D = {(0, 0, 0): one}
                for _ in range(d):
                    N = {}
                    for (x, y, z), c in D.items():
                        for al, be, ze, w in types:
                            key = (min(x + al, k), min(y + be, k), min(z + ze, k))
                            N[key] = N.get(key, 0) + c * w
                    D = N
                for (x, y, z), c in D.items():
                    if z >= k: total += wv * c * exp(g * (sat(x) - sat(y)))
    return float(total.real) if mp is None else total.real

if __name__ == "__main__":
    import qaoa_tree
    for d, g, b in [(3, 0.6358477, 0.34595259), (4, 5.6978232, 1.27641089), (5, 0.61, 0.33), (6, 1.3, 0.9)]:
        a, c = value(d, g, b), qaoa_tree.value(d, g, b)
        print(d, a, c); assert abs(a - c) < 1e-10
