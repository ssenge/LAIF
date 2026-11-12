"""QAOA at depth 1 for LocalMaxCut on d-regular graphs of large girth (vertex satisfied when at least ceil(d/2) of its
d neighbours lie on the other side), exact on the d-regular tree by factorizing over branches.

<O> = 2^-N sum_{x,y} e^{i g C(x)} A_{xy} e^{-i g C(y)}, A = U_M^dag O U_M on S = {v} u N(v), x = y outside S. Only the
vertex terms H_w with B(w) meeting S differ between x and y: w = v, its neighbours u, and the children c of each u.
Given (a, b) on S, the sum over the rest factorizes over the d branches, and inside a branch over the d-1 children of u
(each with d-1 grandchildren)."""
import itertools, sys
import numpy as np

def value(d, g, b):
    k = -(-d // 2)
    sat = lambda own, nbrs: float(sum(o != own for o in nbrs) >= k)
    S = list(itertools.product([0, 1], repeat=d + 1))              # (v, u_1..u_d)
    # A_{ab} = sum_z O(z) prod_j <a_j|U^dag|z_j><z_j|U|b_j>, <z|e^{-ibX}|b> = cos b (z = b), -i sin b otherwise
    U = np.array([[np.cos(b), -1j * np.sin(b)], [-1j * np.sin(b), np.cos(b)]])
    O = np.array([sat(z[0], z[1:]) for z in S])
    Z = np.array(S)
    # amplitude tensor M[z, b] = prod_j U[z_j, b_j]
    M = np.prod(U[Z[:, None, :], Z[None, :, :]], axis=2)             # (z, b)
    A = (M.conj().T * O) @ M                                        # A[a, b] = sum_z conj(M[z,a]) O[z] M[z,b]
    # child factor: for a child c of u (values uc_x, uc_y of u in x and y), sum over r_c and its d-1 grandchildren of
    # e^{ig(H_c(x) - H_c(y))}, normalized; H_c depends on r_c, u, grandchildren (same in x and y)
    gc = list(itertools.product([0, 1], repeat=d - 1))
    def child_factor(ux, uy):
        tot = {}
        for rc in (0, 1):
            s = 0
            for q in gc:
                s += np.exp(1j * g * (sat(rc, (ux,) + q) - sat(rc, (uy,) + q)))
            tot[rc] = s / len(gc)
        return tot                                                   # dict r_c -> averaged factor
    CF = {(ux, uy): child_factor(ux, uy) for ux in (0, 1) for uy in (0, 1)}
    ch = list(itertools.product([0, 1], repeat=d - 1))
    def branch(vx, vy, ux, uy):
        """Average over the d-1 children values of e^{ig(H_u(x) - H_u(y))} times the child factors."""
        cf = CF[(ux, uy)]
        s = 0
        for r in ch:
            ph = np.exp(1j * g * (sat(ux, (vx,) + r) - sat(uy, (vy,) + r)))
            s += ph * np.prod([cf[rc] for rc in r])
        return s / len(ch)
    BR = {key: branch(*key) for key in itertools.product([0, 1], repeat=4)}
    Hs = O                                                           # H_v on S equals the observable
    ph = np.exp(1j * g * (Hs[:, None] - Hs[None, :]))
    BRa = np.array([[[[BR[(p, q, r, t)] for t in (0, 1)] for r in (0, 1)] for q in (0, 1)] for p in (0, 1)])
    F = np.prod(BRa[Z[:, None, 0:1], Z[None, :, 0:1], Z[:, None, 1:], Z[None, :, 1:]], axis=2)
    tot = np.sum(A * ph * F)
    return float(np.real(tot)) / 2 ** (d + 1)

if __name__ == "__main__":
    assert abs(value(3, 0.0, 0.3) - 0.5) < 1e-12
    import time; t = time.time(); v4 = value(4, 5.6978232, 1.27641089); print("d=4", v4, time.time() - t); assert abs(v4 - 0.8913470553604836) < 1e-10
    v3 = value(3, 0.6358477, 0.34595259)
    print("d=3 check", v3); assert abs(v3 - 0.8192921) < 1e-6
