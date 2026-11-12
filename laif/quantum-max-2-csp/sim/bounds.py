"""Exponents of the quantum bounds for Max 2-SAT and Max 2-CSP in terms of m, with asserts."""
from fractions import Fraction as F
from math import log2

# Max 2-SAT, light-edge weight of the general case (p small), as printed: we ~ 0.15820, i.e. m/6.321.
we = 0.15819  # [GS] Table 2, p = 0, degree >= 6
assert abs(we - 1 / 6.321) < 2e-5
assert we <= 22 / 139 and 2 ** 11 <= 1.0564 ** 139   # the Lean certificate maxtwosat_cert
base_2sat = 2 ** (we / 2)
print("Max 2-SAT: 2^(we/2) =", base_2sat)
# 1.0564 holds for every we below log2(1.0564)*2, with room for the last printed digit of we.
assert 2 * log2(1.0564) > 0.158205 + 1e-4
assert base_2sat < 1.0564

# Max 2-CSP general: r^((9/50+o(1))m) -> r^((9/100+o(1))m); for r = 2.
assert 2 ** 0.09 < 1.0644 and log2(1.0644) - 0.09 > 3e-5
print("Max 2-CSP: 2^0.09 =", 2 ** 0.09)
# degree <= 4: 7/40 -> 7/80; cubic: n/5 -> n/10.
print("deg 4: 2^(7/80) =", 2 ** (7 / 80), " cubic: 2^(1/10) =", 2 ** 0.1)
assert 2 ** (7 / 80) < 1.0626 and 2 ** 0.1 < 1.0718

# SMC weights (wr, ws, wb, wsd = ws,2, wc) = (0.2, 0.7, 0.2, 0.6, 0.1): check (8)-(24) at eps = 0 with r = 2.
wr, ws, wb, ws2, wc = F(1, 5), F(7, 10), F(1, 5), F(3, 5), F(1, 10)
cons = [-wb + wc, -ws + ws2, -wr + wc, -wr + wb - wc, F(1, 6) * ws + F(5, 12) * wr - wr,
        -ws2 + ws - wb + wc, -ws2 + ws - wr + wc, -ws2 + ws - wr + wb - wc, -ws + wr, -ws + wc, -ws + wb - wc,
        1 - 2 * ws + ws2 - wr, 1 - ws - wr - wb + wc, 1 - ws - wr - wc, -wr + wb, 1 - ws - 2 * wr - wc + wb,
        1 - ws - 2 * wr + wc]
assert all(c <= 0 for c in cons), cons
# Cubic: n vertices, m = 3n/2 edges, so wr n = (2/15) m; the 4-and-general bounds follow from [SS, Thm 22].
assert wr * F(2, 3) == F(2, 15)
assert F(1, 8) + F(3, 8) * F(2, 15) == F(7, 40)   # beta_4(alpha) of [SMC]

# Value calls at a Separation node: L is the smaller cubic side, so |L| <= (|L|+|R|)/2 and log B(L) <= log B(v).
# Nesting depth of value calls is at most log2(n) + 1.

# Implied quantum bounds from plain trees: [GS] p = 1 (0.19 m, 3m/16 at degree 4), cubic r^(n/4) of [SS].
imp = {"Max 2-CSP": 2 ** 0.095, "deg 4": 2 ** (3 / 32), "cubic": 2 ** (1 / 8)}
print("implied:", imp)
assert imp["Max 2-CSP"] < 1.0681 and imp["deg 4"] < 1.0672 and imp["cubic"] < 1.0906
assert 2 ** 0.09 < imp["Max 2-CSP"] and 2 ** (7 / 80) < imp["deg 4"] and 2 ** 0.1 < imp["cubic"]

# Crossover with Grover r^(n/2) after the reductions of degree <= 2 (every vertex has degree >= 3, m >= 3n/2).
print("Max 2-SAT below 2^(n/2) when m/n <", 0.5 / (we / 2))
print("Max 2-CSP below 2^(n/2) when m/n <", 0.5 / 0.09)
# Classical exponential-space bound 2^((7/48)m) from pathwidth <= 7m/48 + o(n).
print("exp-space classical 2^(7/48) =", 2 ** (7 / 48), " poly-space 2^(9/50) =", 2 ** 0.18, " 2^we =", 2 ** we)
assert 2 ** 0.09 < 2 ** (7 / 48) and 2 ** (we / 2) < 2 ** (7 / 48)
# Bisection and other cardinality constraints: implied plain-tree bounds count all branchings,
# at most m/5 in general ([SS] Lemma 4) and n/4 on cubic graphs, so 2^(m/10) and 2^(n/8).
assert 2 ** 0.1 < 1.0718 and 2 ** 0.09 < 2 ** 0.1 and 2 ** (1 / 10) < 2 ** (1 / 8)
print("bisection implied: 2^(m/10) =", 2 ** 0.1, " cubic 2^(n/8) =", 2 ** 0.125)
print("all asserts passed")
