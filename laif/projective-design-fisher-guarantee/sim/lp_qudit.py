"""Design Fisher guarantee in dimension d as an LP in (a, b, c): a = |phi_1|^2, b = |phi_2|^2, c = cos^2 of the relative
phase. Minimise E_mu[d b c] over measures with E_mu[a^i b^j (abc)^l] = Haar value for i + j + 2l <= t.
Haar: (a, b) ~ Dirichlet(1, 1, d - 2), c = cos^2(theta), theta uniform, independent."""
import sys, numpy as np
from math import gamma, comb
from scipy.optimize import linprog

def dir_mom(p, q, d):        # E[a^p b^q] for Dirichlet(1,1,d-2) (for d = 2: b = 1 - a)
    if d == 2:
        return gamma(p + 1) * gamma(q + 1) / gamma(p + q + 2)
    return gamma(d) * gamma(p + 1) * gamma(q + 1) / gamma(d + p + q)
def c_mom(l):                # E[cos^{2l} theta]
    return comb(2 * l, l) / 4 ** l
def basis(t):
    return [(i, j, l) for i in range(t + 1) for j in range(t + 1) for l in range(t // 2 + 1) if i + j + 2 * l <= t]
def haar(i, j, l, d):
    return dir_mom(i + l, j + l, d) * c_mom(l)

def grid(d, M):
    a = np.linspace(0, 1, M); c = np.linspace(0, 1, M)
    pts = []
    for x in a:
        bs = [1 - x] if d == 2 else np.linspace(0, 1 - x, M)
        for y in bs:
            for z in c:
                pts.append((x, y, z))
    return np.array(pts)

def solve(d, t, M):
    P = grid(d, M); A_, B_, C_ = P.T
    f = np.where(A_ > 0, d * B_ * C_, 0.0)          # outcomes with probability 0 are omitted
    Bs = basis(t)
    rows = np.array([A_ ** i * B_ ** j * (A_ * B_ * C_) ** l for i, j, l in Bs])
    rhs = np.array([haar(i, j, l, d) for i, j, l in Bs])
    # drop dependent rows for d = 2 (b = 1 - a)
    res = linprog(f, A_eq=rows, b_eq=rhs, bounds=(0, None), method="highs")
    return res.fun if res.status == 0 else None, res

if __name__ == "__main__":
    d, M = int(sys.argv[1]), int(sys.argv[2])
    for t in map(int, sys.argv[3:]):
        v, res = solve(d, t, M)
        print(f"d={d} t={t}: LP {v}")
        x = res.x; P = grid(d, M); keep = x > 1e-7
        for (a_, b_, c_), w_ in sorted(zip(map(tuple, P[keep]), x[keep])):
            print(f"   a={a_:.3f} b={b_:.3f} c={c_:.3f} w={w_:.4f}")
    c2 = 1 / (d + 1 + (d + 1) ** 0.5); c3 = 0.5 * (1 - d / (2 * (d + 1)))
    k = 2; c4 = 0.5 * (1 - d / (k * (d + k)) + (d + 1) / (8 * k * k * (d + k) ** 2)); u4 = 0.5 * (1 - d / ((k + 1) * (d + k - 1)))
    c5 = 0.5 * (1 - d / (3 * (d + 2)))
    print(f"ref c2={c2:.6f} c3={c3:.6f} t=4 in [{c4:.6f}, {u4:.6f}] c5={c5:.6f}")
