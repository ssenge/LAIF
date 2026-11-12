"""Certificate for the node bound of polynomial-space 4-colouring: every instance P = (G, I, S) of the branching of
[8] has a search tree with at most 1.69804^mu(P) terminal costs up to subexponential factors, with the terminal
algorithms of [9] that use no dynamic programming over decompositions: reduction to 3-colouring by [3] (Lemma 5.2),
(3,2)-CSP (Lemma 5.4), and list colouring of paths and cycles (Lemma 5.5).

The check is Lemma 5.8 of [9] in the original variables: all branching constraints sum alpha r^-beta <= 1 of Table 1
of [9] (Equations (6)-(21) of [8]), the linear constraints on the weights, and the terminal inequalities
ln(r) (w_c3, w_k3, w_k4) M >= eta R for multipliers eta >= 0 summing to one. All numbers are exact decimals, evaluated
with 60 digits and required to hold with a margin of 1e-9. It also checks the parameters of Table 2 of [8] at 1.7159,
with the single terminal algorithm of [8]. References are those of the folder README."""
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from math import factorial

getcontext().prec = 60
MARGIN = D("1e-9")


def lam():
    """Largest root of x^5 = 2x + 2, the base of (3,2)-CSP in [3], rounded up in the last digits."""
    a, b = D(1), D(2)
    for _ in range(190):
        m = (a + b) / 2
        a, b = (m, b) if m ** 5 < 2 * m + 2 else (a, m)
    return b


LAM = lam()
BETA = ((D(2) ** 3 * D(3) ** 4 * LAM ** 24).ln() / 49).exp()           # Theorem 2 of [3]
MJ = {4: 2, 5: 5, 6: 5, 7: 7, 8: 10}                                   # maximal independent sets of the cycle C_j
M = [[1, 1, 0, 3, 6, 9, 0, 3, 6, 9, 12], [0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1]]

R_CERT = D("1.69804")
WEIGHTS = dict(k3=D("2.9704494860"), k4=D("3.5579545637"), c=D("0.5593776725"), w1=D("0.9342533916"), w2=D(1))
ETA = [D("0.0822508347"), D("0.8778792406"), D("0.0398699247")]


def pairs(w1, w2, c, k3, k4):
    """Table 1 of [9]: each row is a list of pairs (alpha, beta), meaning sum alpha r^-beta <= 1."""
    d = w2 - c
    T = [[(2, 2 * w1 - c)]] + [[(MJ[j], j * d + ((j + 2) // 3) * c)] for j in MJ]
    T += [[(1, 3 * d + c), (1, 4 * d + c), (1, 5 * d + c)],
          [(1, 1 + 2 * d), (2, 1 + 3 * d)], [(2, 1 + 2 * d), (1, 1 + 4 * d)],
          [(1, 2 + d - c), (1, 1 + 3 * d), (1, 2 + 3 * d - c)], [(1, 2 + d - c), (1, 1 + 3 * d), (1, 2 + 2 * d - c)],
          [(1, 2 + 5 * d + c - 2 * w1), (1, 2 + 2 * d + c - k3)],
          [(1, 2 + 4 * d + c - 2 * w1), (2, 2 + 4 * d + 2 * c - k3)],
          [(1, 4 + 2 * d - c - 2 * w1), (1, 2 + 2 * d - c), (2, 3 + 4 * d - 2 * w1)],
          [(1, 1 + 5 * d), (1, 1 - c)],
          [(1, 4 - 3 * c), (3, 5 - 4 * c)], [(1, 4 - 3 * c), (1, 5 - c - k4)], [(2, 5 - 4 * c), (1, 6 - 2 * c - k4)],
          [(2, 4 - 3 * c), (1, 5 - 4 * c), (1, 6 - 4 * c)], [(2, 4 - 3 * c), (1, 5 - 4 * c), (2, 8 - 6 * c)],
          [(3, 4 - 3 * c)], [(3, 4 - 3 * c), (1, 7 - 5 * c)],
          [(2, 4 - 3 * c + 6 * (1 - w2)), (1, 5 - 4 * c + 3 * (1 - w2)), (1, 6 - 5 * c)],
          [(3, 5 - 4 * c), (1, 6 - 5 * c), (1, 7 - 5 * c)], [(2, 5 - 4 * c), (2, 6 - 5 * c), (1, 7 - 6 * c)]]
    return T


def linear_ok(w1, w2, c, k3, k4):
    return 0 <= c <= w1 <= w2 <= 1 and 1 - w2 <= w2 - w1 <= w1 and 3 * w2 >= k3 and 4 >= k4


def g(m, i):
    """Branch cost of a clique with m vertices and i centres, Lemma 5.4 of [9]."""
    if i == 0:
        return D(9) / 2 if m == 3 else D(6)
    if i == 1:
        return LAM ** (m - 1) * (3 + LAM ** 3)
    return D(6) / factorial(4 - i) * (4 - i + i * LAM ** 3)


def rows(beta=BETA):
    """Coefficients of the three terminal algorithms on x = (s1, s', a0..a3, b0..b4), natural logarithms."""
    B = lambda m, i: D(m).ln() + (m - 1 + 3 * i) * beta.ln()
    col = [beta.ln(), beta.ln()] + [B(3, i) for i in range(4)] + [B(4, i) for i in range(5)]
    csp = [D(3).ln() / 4, LAM.ln()] + [g(3, i).ln() for i in range(4)] + [g(4, i).ln() for i in range(5)]
    tree = [D(24).ln() / 4, D(0)] + [D(18).ln()] * 4 + [D(24).ln()] * 5
    return [col, csp, tree]


def largest_sum(r, w):
    return max(sum(a * (-b * r.ln()).exp() for a, b in row) for row in pairs(**w))


if __name__ == "__main__":
    W = WEIGHTS
    assert linear_ok(**W)
    s = largest_sum(R_CERT, W)
    assert s <= 1 - MARGIN, s
    print(f"branching constraints at r = {R_CERT}: largest sum {s:.9f}")
    R = rows()
    weights = [W["c"], W["k3"], W["k4"]]
    slack = min(R_CERT.ln() * sum(weights[i] * M[i][j] for i in range(3)) - sum(ETA[a] * R[a][j] for a in range(3)) for j in range(11))
    assert sum(ETA) == 1 and min(ETA) >= 0 and slack >= MARGIN, slack
    print(f"terminal inequalities with eta = {[str(e) for e in ETA]}: smallest slack {slack:.9f}")
    print(f"3-colouring base used: {BETA:.7f}, (3,2)-CSP base: {LAM:.8f}")
    r = D("1.6981")
    print(f"r = 1.69804 < {r}, so the subexponential factors fit below 1.6981^n; sqrt(1.6981) = {r.sqrt():.6f} <= 1.3032")
    assert r.sqrt() <= D("1.3032")

    # Parameters of Table 2 of [8], single terminal algorithm Lambda^|S| 4.837^n3 6^n4
    W8 = dict(k3=D("2.96427205"), k4=D("3.43996139"), c=D("0.57560002"), w1=D("0.92972213"), w2=D("0.99787746"))
    r8 = D("1.7159")
    assert linear_ok(**W8)
    s = largest_sum(r8, W8)
    assert s <= 1
    t = min(W8["c"] * r8.ln() - D("1.3645").ln(), W8["k3"] * r8.ln() - D("4.837").ln(), W8["k4"] * r8.ln() - D(6).ln())
    assert t >= 0
    print(f"Table 2 of [8] at r = 1.7159: largest sum {s:.9f}, terminal slack {t:.9f}; sqrt(1.7159) = {r8.sqrt():.6f} <= 1.3100")
    assert r8.sqrt() <= D("1.3100")
    # The largest value of the sum over i for the leaves of [8], attained at beta = 1/3, is below 4.837
    b = D(1) / 3
    v = (b ** b * (1 - b) ** (1 - b)) ** -1 * D(3) ** (1 - b) * D("1.3645") ** (2 * b)
    assert v < D("4.837")
    print(f"leaf factor of [8] at beta = 1/3: {v:.6f} < 4.837")
    # Lemma 5.3 of [9], the local claim: each colouring of a triangle with colour 4 is compatible with two of nine lists
    import itertools as it
    good = [c for c in it.product([1, 2, 3, 4], repeat=3) if len(set(c)) == 3 and 4 in c]
    lists = [[({1, 2, 3} - {cc} if v == xx else {cc, 4}) for v in range(3)] for cc in (1, 2, 3) for xx in range(3)]
    assert len(good) == 18 and len(lists) == 9 and all(sum(all(c[v] in L[v] for v in range(3)) for L in lists) == 2 for c in good)
    print("triangle lists: 18 colourings, 9 list assignments, each colouring compatible with exactly 2, factor 9/2 = " + str(F(9, 2)))
