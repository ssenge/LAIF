"""Exact check: a 9-CNOT circuit for the symmetric weight-2 state D(5,2).
Circuit (search.py convention): Ry on q0..q4, then for each pair (a,b): CNOT(a->b), Ry on a, Ry on b.
Each angle is +-arccos(c) + m pi/4 with c in {sqrt(3/5), 1/sqrt(3), 1/sqrt(5)}, or a multiple of pi/4. The cosine and
sine of every half angle are polynomials in a few algebraic generators; every amplitude minus its target value
reduces to zero, by exact symbolic elimination, modulo relations that hold at the true values of the generators. Run: python exact_d52.py"""
import math
import numpy as np
import sympy as sp
from search import dicke, gates, loss_grad

skel = [(0, 1), (0, 4), (3, 1), (0, 1), (2, 0), (3, 4), (0, 4), (3, 4), (1, 0)]
n = 5
# (sign, c, m): angle = sign * arccos(c) + m * pi / 4
R = sp.sqrt
Q = sp.Rational
ANG = [(1, 0, -6), (-1, R(Q(3, 5)), -8), (1, 0, -6), (1, 1 / R(3), 0), (-1, 1 / R(5), -8),
       (1, 0, -8), (-1, R(Q(3, 5)), -6), (1, 0, -6), (1, 1 / R(5), -3), (1, 1 / R(3), -8),
       (1, 0, -6), (1, 0, -7), (1, 0, 3), (1, 0, -6), (1, 0, -8),
       (1, 0, -6), (1, 0, -1), (1, 0, -6), (1, 0, -6), (1, 0, -8),
       (1, 0, -8), (1, 0, -8), (1, 0, -4)]
# c = 0 marks a plain multiple of pi/4
def angle(sign, c, m):
    return (sign * sp.acos(c) if c != 0 else 0) + m * sp.pi / 4

# Generators: A_c, B_c = cos, sin of arccos(c)/2 for the three values of c; P, Q = cos, sin(pi/8); r2, r3, r5 = square
# roots. Every relation below holds at the true (positive) values, so an amplitude difference that reduces to zero
# modulo them is zero.
A1, B1, A2, B2, A3, B3, P, Qs, r2, r3, r5 = sp.symbols("A1 B1 A2 B2 A3 B3 P Q r2 r3 r5")
CV = {R(Q(3, 5)): (A1, B1, r3 * r5 / 5, r2 * r5 / 5), 1 / R(3): (A2, B2, r3 / 3, r2 * r3 / 3),
      1 / R(5): (A3, B3, r5 / 5, 2 * r5 / 5)}          # c in radicals -> (A, B, c, sqrt(1 - c^2)) in generators
REL = [r2**2 - 2, r3**2 - 3, r5**2 - 5, P**2 + Qs**2 - 1, P**2 - Qs**2 - r2 / 2, 2 * P * Qs - r2 / 2]
for (A, B, c, sn) in CV.values():
    REL += [A**2 + B**2 - 1, A**2 - B**2 - c, 2 * A * B - sn]
G = sp.groebner(REL, A1, B1, A2, B2, A3, B3, P, Qs, r2, r3, r5, order="grevlex", domain="QQ")
VAL = {A1: math.cos(math.acos(math.sqrt(.6)) / 2), B1: math.sin(math.acos(math.sqrt(.6)) / 2),
       A2: math.cos(math.acos(1 / math.sqrt(3)) / 2), B2: math.sin(math.acos(1 / math.sqrt(3)) / 2),
       A3: math.cos(math.acos(1 / math.sqrt(5)) / 2), B3: math.sin(math.acos(1 / math.sqrt(5)) / 2),
       P: math.cos(math.pi / 8), Qs: math.sin(math.pi / 8), r2: math.sqrt(2), r3: math.sqrt(3), r5: math.sqrt(5)}

def half(sign, c, m):
    """cos and sin of angle/2 as polynomials in the generators"""
    cm, sm = sp.Integer(1), sp.Integer(0)
    for _ in range(abs(m)):                                   # rotate by sign(m) pi/8
        cm, sm = cm * P - sp.sign(m) * sm * Qs, sm * P + sp.sign(m) * cm * Qs
    if c == 0:
        return sp.expand(cm), sp.expand(sm)
    A, B = CV[c][:2]; B = sign * B
    return sp.expand(A * cm - B * sm), sp.expand(B * cm + A * sm)

if __name__ == "__main__":
    xe = np.array([float(angle(*a)) for a in ANG])
    fl = loss_grad(xe, n, gates(n, skel), dicke(n, 2))[0]; print("float loss", fl); assert abs(fl) < 1e-12
    psi = [sp.Integer(0)] * 2 ** n; psi[0] = sp.Integer(1)
    bit = lambda i, q: (i >> (n - 1 - q)) & 1
    def ry(psi, q, cs):
        c, s = cs; out = list(psi)
        for i in range(2 ** n):
            if not bit(i, q):
                j = i | (1 << (n - 1 - q)); out[i] = G.reduce(sp.expand(c * psi[i] - s * psi[j]))[1]; out[j] = G.reduce(sp.expand(s * psi[i] + c * psi[j]))[1]
        return out
    cx = lambda psi, a, b: [psi[i ^ (1 << (n - 1 - b))] if bit(i, a) else psi[i] for i in range(2 ** n)]
    j = 0
    for q in range(n): psi = ry(psi, q, half(*ANG[j])); j += 1
    for (a, b) in skel:
        psi = cx(psi, a, b); psi = ry(psi, a, half(*ANG[j])); j += 1; psi = ry(psi, b, half(*ANG[j])); j += 1
    for rel in G.exprs: assert abs(float(rel.subs(VAL))) < 1e-12
    sign = 1 if sum(float(psi[i].subs(VAL)) for i in range(2 ** n) if bin(i).count("1") == 2) > 0 else -1
    for i in range(2 ** n):
        want = sign * r2 * r5 / 10 if bin(i).count("1") == 2 else 0          # 1/sqrt(10)
        assert G.reduce(sp.expand(psi[i] - want))[1] == 0, i
    print("exact: the circuit prepares D(5,2) with global sign", sign)
