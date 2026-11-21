"""Optimality system for eta_des(2,t), any t: LP on a grid of the reduced region gives the support orbits, then the
KKT system (touching conditions of the dual polynomial plus moment equations) is solved in high precision."""
import sys, json
import numpy as np, mpmath as mp
from scipy.optimize import linprog

def basis(t): return [(a, c) for a in range(t // 2 + 1) for c in range(t + 1) if 2 * a + c <= t]
def hm(a, c):
    if c % 2: return mp.mpf(0)
    return 2 * mp.gamma(a + mp.mpf(1) / 2) * mp.gamma(mp.mpf(1) / 2) * mp.gamma(mp.mpf(c + 1) / 2) / mp.gamma(mp.mpf(2 * a + c + 3) / 2) / (4 * mp.pi)

def grid_lp(t, Mz=500, Ms=250):
    B = basis(t)
    zs = np.cos(np.linspace(0, np.pi, Mz))[1:-1]; ss = np.linspace(0, 1, Ms)
    Z, S = np.meshgrid(zs, ss); Z = Z.ravel(); S = S.ravel(); U = S * (1 - Z ** 2)
    A = np.array([U ** a * Z ** c for a, c in B]); b = np.array([float(hm(a, c)) for a, c in B])
    res = linprog(U / (1 + Z), A_eq=A, b_eq=b, bounds=(0, None), method="highs")
    dual = -res.eqlin.marginals if hasattr(res, "eqlin") else None
    keep = res.x > 1e-9
    return res.fun, Z[keep], S[keep], res.x[keep], res.eqlin.marginals

def clusters(Z, S, W, tol=0.03):
    pts = sorted(zip(Z, S, W)); out = []
    for z, s, w in pts:
        for c in out:
            if abs(c[0] / c[2] - z) < tol and abs(c[1] / c[2] - s) < 0.08:
                c[0] += z * w; c[1] += s * w; c[2] += w; break
        else:
            out.append([z * w, s * w, w])
    return [(z / w, s / w, w) for z, s, w in out]

def solve(t, dps=60):
    mp.mp.dps = dps
    B = basis(t)
    val, Z, S, W, marg = grid_lp(t)
    cl = clusters(Z, S, W)
    kinds = ['b0' if s < 0.02 else ('b1' if s > 0.98 else 'in') for z, s, w in cl]
    q0 = list(marg)
    def q(co, z, u): return sum(c * u ** a * z ** b for c, (a, b) in zip(co, B))
    def g(co, z, u): return u - (1 + z) * q(co, z, u)
    nB = len(B)
    def unpack(v):
        co = v[:nB]; pts = []; k = nB
        for kind in kinds:
            if kind == 'in': pts.append((v[k], v[k + 1])); k += 2
            elif kind == 'b0': pts.append((v[k], mp.mpf(0))); k += 1
            else: pts.append((v[k], 1 - v[k] ** 2)); k += 1
        ws = list(v[k:k + len(kinds) - 1]); ws.append(1 - sum(ws))
        return co, pts, ws
    def F(*v):
        co, pts, ws = unpack(v)
        eqs = []
        for (z, u), kind in zip(pts, kinds):
            gz = mp.diff(lambda s: g(co, s, u), z); gu = mp.diff(lambda s: g(co, z, s), u)
            eqs.append(g(co, z, u))
            if kind == 'in': eqs += [gz, gu]
            elif kind == 'b0': eqs.append(gz)
            else: eqs.append(gz - 2 * z * gu)
        eqs += [sum(w * u ** a * z ** b for (z, u), w in zip(pts, ws)) - hm(a, b) for a, b in B]
        return eqs
    x0 = q0[:]
    for (z, s, w), kind in zip(cl, kinds):
        if kind == 'in': x0 += [z, s * (1 - z * z)]
        else: x0 += [z]
    x0 += [w for z, s, w in cl[:-1]]
    sol = mp.findroot(F, [mp.mpf(x) for x in x0], tol=mp.mpf(10) ** (-dps + 10), maxsteps=200)
    co, pts, ws = unpack(sol)
    dual = sum(c * hm(a, b) for c, (a, b) in zip(co, B))
    prim = sum(w * u / (1 + z) for (z, u), w in zip(pts, ws))
    return val, dual, prim, co, pts, ws, kinds

if __name__ == "__main__":
    t = int(sys.argv[1])
    val, dual, prim, co, pts, ws, kinds = solve(t)
    print(f"t={t}: grid LP {val:.8f}; dual {mp.nstr(dual, 30)}; primal {mp.nstr(prim, 30)}")
    assert abs(dual - prim) < mp.mpf(10) ** -30
    assert min(ws) > 0 and all(0 <= u <= 1 - z * z + mp.mpf(10) ** -40 for z, u in pts)
    for (z, u), w, k in zip(pts, ws, kinds): print(f"  {k} z={mp.nstr(z, 12)} u={mp.nstr(u, 12)} w={mp.nstr(w, 12)}")
    # global check of the dual inequality on a fine grid
    B = basis(t); cf = [float(c) for c in co]; worst = 1
    for z in np.cos(np.linspace(0, np.pi, 4001)):
        s = np.linspace(0, 1, 1001)
        hv = s * (1 - z) - sum(c * (s * (1 - z * z)) ** a * z ** b for c, (a, b) in zip(cf, B))
        worst = min(worst, hv.min())
    print("  min h on grid", worst)
    assert worst > -1e-9
    json.dump({"t": t, "basis": B, "sol_co": [mp.nstr(c, 55) for c in co],
               "pts": [[mp.nstr(z, 55), mp.nstr(u, 55)] for z, u in pts], "kinds": kinds}, open(f"sol_t{t}.json", "w"))
