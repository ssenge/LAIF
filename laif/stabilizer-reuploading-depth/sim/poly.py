"""Exact polynomials G(t) of the recursions (sympy), with s = sqrt(1 - t^2) eliminated."""
import sympy as sp
t = sp.symbols("t"); s = sp.sqrt(1 - t ** 2)
WA = [("n", 2), ("z", 1), ("n", 2), ("z", 3), ("n", 2), ("z", 3), ("n", 1), ("z", 3), ("n", 2)]   # expansion map, attractor 1/sqrt 2
WB = [("n", 1), ("z", 1), ("n", 2), ("z", 1), ("n", 2), ("z", 1), ("n", 3), ("z", 1), ("n", 1)]   # superattracting at 1/sqrt 2
WP = [("n", 1), ("z", 1), ("n", 2)]                                                             # map of the paper

def rot(n, k):
    K = sp.Matrix([[0, -n[2], n[1]], [n[2], 0, -n[0]], [-n[1], n[0], 0]])
    c, si = [(1, 0), (0, 1), (-1, 0), (0, -1)][k % 4]
    return sp.eye(3) + si * K + (1 - c) * K * K

def Gpoly(word):
    n = [s, 0, t]; SZ = rot([0, 0, 1], 1); M = sp.eye(3)
    for typ, k in word: M = M * (rot(n, k) if typ == "n" else SZ ** k)
    g = sp.expand((M * sp.Matrix([0, 0, 1]))[2])
    g = sp.expand(g.subs(s ** 2, 1 - t ** 2))
    return sp.Poly(sp.simplify(g), t)

if __name__ == "__main__":
    P = Gpoly(WP); assert sp.expand(P.as_expr() - (t + t * (1 - t) * (1 - 2 * t ** 2))) == 0
    for name, w in [("A", WA), ("B", WB)]:
        p = Gpoly(w); print(name, "degree", p.degree(), "coeffs", p.all_coeffs())
        print("   G(1) =", p.eval(1), " G'(1) =", sp.diff(p.as_expr(), t).subs(t, 1))
        if name == "B":
            ts = 1 / sp.sqrt(2); print("   G(1/sqrt2)-1/sqrt2 =", sp.simplify(p.as_expr().subs(t, ts) - ts),
                                       " G' =", sp.simplify(sp.diff(p.as_expr(), t).subs(t, ts)), " G''/2 =", sp.simplify(sp.diff(p.as_expr(), t, 2).subs(t, ts) / 2))
