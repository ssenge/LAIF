"""Exact check: a 5-CNOT circuit for the symmetric weight-2 state D(4,2), angles in closed form.
Circuit (search.py convention): Ry on q0..q3, then for each pair (a,b): CNOT(a->b), Ry on a, Ry on b.
t1 = arccos(sqrt(2/3)). Every Ry angle is t1*u + m*pi/2 with u in {0,1,2}, so every half-angle cosine and sine is a
polynomial in C = cos(t1/2), S = sin(t1/2), h = sqrt(2)/2. The amplitudes are reduced exactly, by symbolic elimination, modulo the relations
C^2 + S^2 = 1, 2CS = r, C^2 - S^2 = 2hr, 3 r^2 = 1, 2 h^2 = 1 (r = 1/sqrt(3)) and compared with D(4,2)."""
import math
import numpy as np
import sympy as sp
from search import dicke, gates, loss_grad

C, S, h, r = sp.symbols("C S h r")   # r = 1/sqrt(3) here
# relations that hold at C = cos(t1/2), S = sin(t1/2), h = 1/sqrt(2), r = 1/sqrt(3): sin t1 = r, cos t1 = 2 h r
# (membership of an amplitude difference in this ideal proves it is zero at the true values)
G = sp.groebner([C**2 + S**2 - 1, 2 * C * S - r, C**2 - S**2 - 2 * h * r, 3 * r**2 - 1, 2 * h**2 - 1], C, S, h, r, order="lex", domain="QQ")
# angle = u*t1 + m*pi/2, written as (u, m)
ang = [(0, 1), (1, 0), (0, 0), (0, 0),
       (0, 0), (1, 3), (0, 1), (0, 0), (1, 1), (2, 4), (1, 3), (0, 0), (1, 2), (1, -2)]
skel = [(0, 1), (0, 2), (0, 3), (0, 1), (1, 2)]
n = 4

def half(u, m):
    """(cos, sin) of (u t1 + m pi/2)/2 as polynomials in C, S, h"""
    c, s = sp.Integer(1), sp.Integer(0)
    for _ in range(u):                    # add t1/2
        c, s = c * C - s * S, s * C + c * S
    cm, sm = [(1, 0), (h, h), (0, 1), (-h, h), (-1, 0), (-h, -h), (0, -1), (h, -h)][m % 8]   # m pi/4
    return sp.expand(c * cm - s * sm), sp.expand(s * cm + c * sm)

def ry(psi, q, uv):
    c, s = half(*uv); out = list(psi)
    for i in range(2 ** n):
        if not (i >> (n - 1 - q)) & 1:
            j = i | (1 << (n - 1 - q)); a, b = psi[i], psi[j]
            out[i] = G.reduce(sp.expand(c * a - s * b))[1]; out[j] = G.reduce(sp.expand(s * a + c * b))[1]
    return out

def cx(psi, ctl, tgt):
    out = list(psi)
    for i in range(2 ** n):
        if (i >> (n - 1 - ctl)) & 1: out[i] = psi[i ^ (1 << (n - 1 - tgt))]
    return out

# float cross-check of the angle list first
t1 = math.acos(math.sqrt(2 / 3)); x = np.array([u * t1 + m * math.pi / 2 for u, m in ang])
fl = loss_grad(x, n, gates(n, skel), dicke(n, 2))[0]; print("float loss", fl); assert abs(fl) < 1e-12
psi = [sp.Integer(0)] * 2 ** n; psi[0] = sp.Integer(1); j = 0
for q in range(n): psi = ry(psi, q, ang[j]); j += 1
for (a, b) in skel:
    psi = cx(psi, a, b)
    psi = ry(psi, a, ang[j]); j += 1
    psi = ry(psi, b, ang[j]); j += 1
fval = {C: math.cos(t1 / 2), S: math.sin(t1 / 2), h: math.sqrt(0.5), r: 1 / math.sqrt(3)}
for rel in G.exprs: assert abs(float(rel.subs(fval))) < 1e-12
sign = 1 if float(sum(psi[i] for i in range(2 ** n) if bin(i).count("1") == 2).subs(fval)) > 0 else -1
for i in range(2 ** n):
    want = sign * h * r if bin(i).count("1") == 2 else 0       # 1/sqrt(6) = h r
    d = G.reduce(sp.expand(psi[i] - want))[1]
    assert d == 0, (i, d)
print("exact: the circuit prepares D(4,2) with global sign", sign)
