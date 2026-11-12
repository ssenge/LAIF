"""High-precision worst case of min(7-SUM, labels) over the zero density p."""
import math
from scipy.optimize import minimize, minimize_scalar
from opt import H, seven_sum, scheme, inner, collide

def labels(p):
    def f(v):
        r = scheme(p, v[0], v[1])
        return 9.0 if r is None else r[0]/2 + inner(r[1], r[2])
    best = (9.0, None)
    for fa1 in (.2, .4, .6, .8):
        for fa0 in (.2, .4, .6, .8):
            start = [fa1*(1-p)/2, fa0*p]
            m = minimize(f, start, method="Nelder-Mead", options=dict(xatol=1e-9, fatol=1e-12, maxiter=4000))
            if m.fun < best[0]:
                best = (m.fun, tuple(m.x))
    return best

if __name__ == "__main__":
    r = minimize_scalar(lambda p: -min(seven_sum(p), labels(p)[0]), bounds=(.2, .3), method="bounded", options=dict(xatol=1e-7))
    p = r.x; c, (a1, a0) = labels(p); a, u, l = scheme(p, a1, a0); s = max(0, (4*u-10*l)/7)
    b1, b0 = (1-p-2*a1)/4, (p-a0)/2
    print(f"worst p={p:.6f} exponent={c:.6f}  7-SUM there {seven_sum(p):.6f}")
    print(f"Theta: a1={a1:.5f} a0={a0:.5f} b1={b1:.5f} b0={b0:.5f}; A share a0/ca={a0/(2*a1+a0):.4f}, B zero share {b0/(2*b1+b0):.4f}")
    print(f"a={a:.5f} u={u:.5f} l={l:.5f} sigma={s:.5f} table={l+s:.5f} walk={s/2+2*(u-l-s)/3:.5f}")
    print("crossover with 7-SUM:", [round(x,4) for x in (minimize_scalar(lambda q: abs(seven_sum(q)-labels(q)[0]), bounds=b, method='bounded').x for b in ((.1,.22),))])
    print("max of 7-SUM alone", 2/7*math.log2(3), " max(7-SUM, table outside only)", max(min(seven_sum(k/2000),collide(k/2000)) for k in range(1,1000)))
    for q in (.15,.18,.2,.22,.25,.28,.3,.35,.4,.45):
        print(f"p={q:.2f} labels={labels(q)[0]:.5f} 7sum={seven_sum(q):.5f}")
