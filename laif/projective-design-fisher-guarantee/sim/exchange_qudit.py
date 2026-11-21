"""Cutting-plane solution of the qudit LP in (a, s, c), b = s(1 - a): alternately solve the dual LP on a finite point
set and add the points where the dual inequality is most violated."""
import sys, json, numpy as np
from scipy.optimize import linprog, minimize
from cert_qudit import basis, haar

def mono3(a, s, c, Bs):
    b = s * (1 - a)
    return np.array([a ** i * b ** j * (a * b * c) ** l for i, j, l in Bs])

def fval(a, s, c, d):
    return np.where(a > 0, d * s * (1 - a) * c, 0.0)

def run(d, t, iters=60, tol=1e-11):
    Bs = basis(t); m = np.array([float(haar(i, j, l, d)) for i, j, l in Bs])
    g = np.linspace(0, 1, 21)
    P = np.array([(x, y, z) for x in g for y in g for z in g])
    for it in range(iters):
        A = mono3(*P.T, Bs); f = fval(*P.T, d)
        res = linprog(-m, A_ub=A.T, b_ub=f, bounds=(None, None), method="highs")
        q = res.x
        H = lambda p: (fval(np.array(p[0]), np.array(p[1]), np.array(p[2]), d) - q @ mono3(np.array(p[0]), np.array(p[1]), np.array(p[2]), Bs)).item()
        # search: dense random sample + local refinement of the worst points
        R = np.random.default_rng(it).random((60000, 3)); R = np.vstack([R, np.c_[R[:, :2], np.zeros(len(R))], np.c_[R[:, :2], np.ones(len(R))]])
        R = np.vstack([R, np.c_[np.zeros(2000), np.random.default_rng(it).random((2000, 2))]])
        hv = fval(*R.T, d) - q @ mono3(*R.T, Bs)
        worst = R[np.argsort(hv)[:30]]; new = []
        for p in worst:
            r = minimize(H, p, method="L-BFGS-B", bounds=[(0, 1)] * 3)
            new.append(np.clip(r.x, 0, 1))
        new = np.array(new); hn = np.array([H(p) for p in new])
        viol = -min(hn.min(), hv.min())
        print(f"iter {it}: dual {-res.fun:.12f}, max violation {viol:.2e}, points {len(P)}", flush=True)
        if viol < tol: break
        P = np.vstack([P, new[hn < 0], R[np.argsort(hv)[:10]]])
    return -res.fun, q, P, viol

if __name__ == "__main__":
    d, t = int(sys.argv[1]), int(sys.argv[2])
    v, q, P, viol = run(d, t)
    np.save(f"exch_d{d}_t{t}_P.npy", P)
    json.dump({"d": d, "t": t, "q": list(q), "value": v, "viol": viol}, open(f"exch_d{d}_t{t}.json", "w"))
