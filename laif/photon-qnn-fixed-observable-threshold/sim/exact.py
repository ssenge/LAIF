"""Exact check of Proposition 1 (fixed observable of degree m - 1 reaches P_{(m-1)L}).

Simplex coordinates z_j = y_j - 1/m (j < m), curve z(x) = eps (cos Lx, sin Lx, 0, ..., 0).
G(z) = z_1^2 + z_2^2 + sum_{j=3}^{m-1} z_j T_{j-1}(z_1/eps), total degree m - 1 (T_k(cos t) = cos kt).
Asserts, with sympy in exact arithmetic:
  1. G is constant (= eps^2) on the curve, and deg G = m - 1;
  2. the gradient of G on the curve is (2 eps cos Lx, 2 eps sin Lx, cos 2Lx, ..., cos (m-2)Lx);
  3. the products M_j(x) p(x), p in the basis of P_L, span P_{(m-1)L} (rank 2(m-1)L + 1 over the rationals).
"""
import sympy as sp

x, eps = sp.symbols('x epsilon', positive=True)


def fourier_vec(expr, N):
    """Coefficients of a real trig polynomial of degree <= N in the basis 1, cos fx, sin fx."""
    e = sp.expand(sp.trigsimp(expr))
    e = sp.expand(e.rewrite(sp.exp))
    v = []
    c = {f: sp.simplify(e.coeff(sp.exp(sp.I * f * x))) if f else None for f in range(-N, N + 1)}
    const = sp.simplify(e.subs(x, 0) - sum(c[f] for f in range(-N, N + 1) if f))  # constant term
    v.append(const)
    for f in range(1, N + 1):
        a, b = c[f], c[-f]
        v.append(sp.simplify(a + b)); v.append(sp.simplify(sp.I * (a - b)))
    assert sp.simplify(sum(sp.Abs(sp.im(t)) for t in v)) == 0
    # reconstruct and compare
    rec = v[0] + sum(v[2 * f - 1] * sp.cos(f * x) + v[2 * f] * sp.sin(f * x) for f in range(1, N + 1))
    assert sp.simplify(sp.expand((rec - expr).rewrite(sp.exp))) == 0
    return v


def check(m, L):
    z = sp.symbols(f'z1:{m}')
    G = z[0] ** 2 + z[1] ** 2 + sum(z[j] * sp.chebyshevt(j, z[0] / eps) for j in range(2, m - 1))
    assert sp.Poly(sp.expand(G * eps ** (m - 2)), *z).total_degree() == m - 1
    curve = {z[0]: eps * sp.cos(L * x), z[1]: eps * sp.sin(L * x), **{z[j]: 0 for j in range(2, m - 1)}}
    assert sp.simplify(G.subs(curve) - eps ** 2) == 0
    M = [sp.simplify(sp.diff(G, z[j]).subs(curve)) for j in range(m - 1)]
    want = [2 * eps * sp.cos(L * x), 2 * eps * sp.sin(L * x)] + [sp.cos(j * L * x) for j in range(2, m - 1)]
    assert all(sp.simplify(sp.expand_trig(a - b)) == 0 for a, b in zip(M, want))
    N = (m - 1) * L
    basis = [sp.Integer(1)] + [f(w * x) for w in range(1, L + 1) for f in (sp.cos, sp.sin)]
    rows = [fourier_vec(sp.expand(w * p), N) for w in want for p in basis]
    r = sp.Matrix(rows).subs(eps, 1).rank()
    assert r == 2 * N + 1, (m, L, r)
    return r


for m in range(3, 7):
    for L in range(1, 4):
        r = check(m, L)
        print(f"m = {m}, L = {L}: G constant on the curve, rank {r} = dim P_{(m - 1) * L}; [1, Lemma 6] reaches P_{(m - 2) * L}")
print("all checks passed")
