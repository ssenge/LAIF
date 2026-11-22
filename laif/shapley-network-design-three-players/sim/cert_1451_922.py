"""Exact check: 3-player undirected network design game with equal cost sharing with PoS -> 1451/922 (> 1769/1126).

Same 5-vertex, 7-edge topology as arXiv 1211.2090 Fig. 2(b), reweighted.
Vertices 0 = t1 = t3, 1 = t2, 2 = s1, 3 = s2, 4 = s3. Weights w0 + eps*d.
For each eps tested, full enumeration in Fractions: unique NE = the three direct edges,
cost 1451 - 3718 eps; OPT = 922 (tree 0-1, 1-4, 4-3, 3-2).
"""
from fractions import Fraction as F
from game import Game

EDGES = [(0, 1), (0, 2), (0, 4), (1, 3), (1, 4), (2, 3), (3, 4)]
W0 = [260, 450, 545, 456, 342, 92, 228]
D = [48, -768, -2098, -852, 744, 556, -1348]
PAIRS = [(2, 0), (3, 1), (4, 0)]


def check(eps):
    w = [F(a) + eps * b for a, b in zip(W0, D)]
    assert all(x > 0 for x in w)
    g = Game(5, EDGES, PAIRS)
    opt, ne, pos, nes = g.exact(w)
    assert opt == 922, opt
    assert len(nes) == 1 and ne == 1451 - 3718 * eps, (len(nes), ne)
    return pos


if __name__ == "__main__":
    base = F(1769, 1126)
    for eps in [F(1, 10**4), F(1, 10**5), F(1, 10**6), F(1, 10**9)]:
        pos = check(eps)
        assert pos > base
        print(f"eps={eps}: PoS = {pos} = {float(pos):.9f}  (> 1769/1126 = {float(base):.9f})")
    # eps = 0: ties make cheap profiles equilibria, so the limit is a supremum only
    g = Game(5, EDGES, PAIRS)
    opt, ne, pos, nes = g.exact(W0)
    print("eps=0: OPT", opt, "best NE", ne, "#NE", len(nes), "(tie case)")
    # integer instance for eps = 1/10^4 (all weights times 10^4)
    wi = [a * 10**4 + b for a, b in zip(W0, D)]
    opt, ne, pos, nes = Game(5, EDGES, PAIRS).exact(wi)
    assert pos == F(14506282, 9220000) and len(nes) == 1
    print("integer weights", wi, "PoS", pos, float(pos))
    print("sup over eps -> 1451/922 =", float(F(1451, 922)))
