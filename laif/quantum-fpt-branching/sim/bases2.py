"""Square roots of the classical search-tree bases of Theorem 3 (new) and of the simpler trees (implied baselines).
Each printed base b is the square root rounded up at the fourth decimal: checked exactly as b^2 >= c and (b - 1e-4)^2 < c."""
from fractions import Fraction as F
from math import ceil, isqrt
def up(c):                                   # smallest b = m / 10^4 with b^2 >= c, for c given as a decimal string
    c = F(c); m = isqrt(int(c * 10 ** 8)) 
    while F(m, 10 ** 4) ** 2 < c: m += 1
    assert F(m - 1, 10 ** 4) ** 2 < c <= F(m, 10 ** 4) ** 2
    return F(m, 10 ** 4)
ROWS = [  # problem, new classical base, implied baseline classical base
    ("Cluster Vertex Deletion", "1.811", "1.9102"),
    ("Edge Dominating Set", "2.2351", "2.3147"),
    # the generated bounds of [11] are printed with three decimals: add 0.0005 so that a value rounded to nearest is covered
    ("3-Path Vertex Cover", "1.7085", "1.713"),
    ("4-Path Vertex Cover", "2.1385", "2.619"),
    ("5-Path Vertex Cover", "2.6365", "3.945"),
    ("6-Path Vertex Cover", "3.3345", "4.947"),
    ("7-Path Vertex Cover", "3.9595", "5.951"),
]
for p, c, b in ROWS:
    q, qb = up(c), up(b)
    assert q < qb, p
    print(f"{p:26s} new {float(q):.4f}^k (sqrt {c})   implied {float(qb):.4f}^k (sqrt {b})")
# quantum hitting-set bounds for d = 3..6 of the earlier folder, and sqrt(6.0409) for d = 7 (P_d hitting sets are d-hitting sets): the new bases are below them
for d, hs in ((3, "1.4287"), (4, "1.7439"), (5, "2.0102"), (6, "2.2452"), (7, "2.4578")):  # d = 7: sqrt(6.0409) rounded down
    assert up(dict((r[0], r[1]) for r in ROWS)[f"{d}-Path Vertex Cover"]) < F(hs)
assert up("1.811") < F("1.4287")             # Cluster Vertex Deletion is hitting all induced P_3
print("all checks passed")
