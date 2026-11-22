"""Checks the dual certificates of the proof that the better of the orders A and B costs at most 4/3 OPT.
Every case is an LP  max z  s.t.  M x <= h, x >= 0  (rows built from scratch below, OPT = 1). A certificate is
y >= 0 with (M^T y)_j >= [j = z] for every variable j, so z <= h . y. Exact arithmetic throughout."""
from fractions import Fraction as F


def check(name, nv, rows, cert, bound):
    names = [nm for nm, _, _ in rows]
    assert set(cert) <= set(names), name
    y = {nm: F(cert.get(nm, 0)) for nm in names}
    assert all(v >= 0 for v in y.values())
    for j in range(nv):
        col = sum(y[nm] * F(r[j]) for nm, r, _ in rows)
        assert col >= (1 if j == nv - 1 else 0), (name, j, col)
    val = sum(y[nm] * F(hh) for nm, _, hh in rows)
    assert val == F(bound) and val <= F(1, 3), (name, val)
    print(f"{name}: z <= {val}")


h = F(1, 2)
# Case q >= p.  x = (a_p, P' = sum_{k<p} a_k, a_{q+1}, s, z)
low1 = [("A_p", [-1, -h, 0, 1, 0], 0), ("B_q", [1 + h, 1 + h, -1 + h, -h, 0], h),
        ("cap_p", [1, 0, 0, -1, 0], 0), ("cap_q1", [0, 0, 1, -1, 0], 0), ("mass", [1, 1, 1, 0, 0], 1),
        ("zA", [1, 0, 0, -1, 1], 0), ("zB", [0, 0, 1, -1, 1], 0)]
# Case q + 1 = p >= 1.  x = (a_p, L_p = sum_{k<p} a_k, s, z)
low2 = [("A_p", [-1, -h, 1, 0], 0), ("B_q", [-1 + h, 1 + h, -h, 0], h),
        ("cap_p", [1, 0, -1, 0], 0), ("mass", [1, 1, 0, 0], 1), ("zA", [1, 0, -1, 1], 0)]


def rows_dm(d, m):
    """Case d = p - q >= 2 with m kept edges left of q: x = (U, c_0..c_{m-1}, b_1..b_d, s, z)."""
    Ui = 0; C = lambda t: 1 + t; B = lambda i: m + i; S = m + d + 1; Z = m + d + 2; nv = Z + 1; R = []
    row = lambda: [F(0)] * nv
    r = row(); r[S] = F(1); r[Ui] = -F(1, d + m + 1)
    for t in range(m): r[C(t)] -= F(1, d + t + 1)
    for i in range(1, d + 1): r[B(i)] -= F(1, d - i + 1)
    R.append(("A_p", r, 0))
    r = row(); r[Ui] = F(1); r[S] = -F(1)
    for t in range(m): r[C(t)] += F(1, d + t) + 1
    for i in range(1, d): r[B(i)] += F(1, d - i) + 1
    R.append(("AL", r, 1))
    c = F(1, d + 1); r = row(); r[Ui] = 1 + c; r[S] = -c
    for t in range(m): r[C(t)] = 1 + c
    for i in range(1, d + 1): r[B(i)] += c - F(1, i)
    R.append(("B_q", r, c))
    for j in range(1, d):
        r = row(); r[Ui] = -F(1)
        for t in range(m): r[C(t)] = -F(1)
        for i in range(1, j + 1): r[B(i)] -= 1
        for i in range(j + 1, d + 1): r[B(i)] += F(1, i - j)
        R.append((f"BR{j}", r, 0))
    for v in [C(t) for t in range(m)] + [B(i) for i in range(1, d + 1)]:
        r = row(); r[v] = F(1); r[S] = -F(1); R.append((f"cap{v}", r, 0))
    r = row(); r[Ui] = F(1)
    for v in [C(t) for t in range(m)] + [B(i) for i in range(1, d + 1)]: r[v] = F(1)
    R.append(("Q>=0", r, 1))
    for nm, e in (("zA", B(d)), ("zB", B(1))):
        r = row(); r[Z] = F(1); r[S] = -F(1); r[e] += 1; R.append((nm, r, 0))
    return nv, R


def rows_window(K):
    """Case d >= K: x = (e_0..e_{K-1} with e_t = a_{p-t}, V = sum_{k<=p-K} a_k, s, z)."""
    V, S, Z = K, K + 1, K + 2; nv = K + 3; R = []
    row = lambda: [F(0)] * nv
    r = row(); r[S] = F(1); r[V] = -F(1, K + 1)
    for t in range(K): r[t] -= F(1, t + 1)
    R.append(("A_p", r, 0))
    r = row(); r[V] = F(1); r[S] = -F(1)
    for t in range(1, K): r[t] = F(1, t) + 1
    R.append(("AL", r, 1))
    for rr in range(1, K):
        r = row(); r[V] = -F(1)
        for t in range(rr): r[t] += F(1, rr - t)
        for t in range(rr, K): r[t] -= 1
        R.append((f"BR-{rr}", r, 0))
    for t in range(K):
        r = row(); r[t] = F(1); r[S] = -F(1); R.append((f"cap{t}", r, 0))
    r = row(); r[V] = F(1)
    for t in range(K): r[t] = F(1)
    R.append(("Q>=0", r, 1))
    r = row(); r[Z] = F(1); r[S] = -F(1); r[0] = F(1); R.append(("zA", r, 0))
    return nv, R


if __name__ == "__main__":
    check("q >= p", 5, low1, {"A_p": "6/5", "B_q": "2/5", "zA": "3/5", "zB": "2/5"}, "1/5")
    check("q + 1 = p", 4, low2, {"A_p": "10/9", "B_q": "2/9", "mass": "2/9", "zA": "1"}, "1/3")
    nv, R = rows_dm(2, 0)
    check("d = 2, q >= 0", nv, R, {"A_p": "69/68", "B_q": "3/68", "Q>=0": "19/68", "zA": "101/136", "zB": "35/136"}, "5/17")
    check("d = 2, q = -1", nv, [r for r in R if r[0] != "B_q"], {"A_p": "1", "Q>=0": "1/3", "zA": "2/3", "zB": "1/3"}, "1/3")
    nv, R = rows_dm(3, 1)
    c3 = {"A_p": "128/111", "AL": "17/111", "BR1": "31/333", "Q>=0": "59/333", "zA": "619/666", "zB": "47/666"}
    check("d = 3, q >= 0", nv, R, c3, "110/333")
    check("d = 3, q = -1", nv, [r for r in R if r[0] != "B_q"], c3, "110/333")
    nv, R = rows_window(4)
    check("d >= 4", nv, R, {"A_p": "10080/8461", "AL": "1512/8461", "BR-2": "482/8461", "BR-3": "294/8461",
                            "cap1": "107/8461", "Q>=0": "1280/8461", "zA": "1"}, "2792/8461")
    print("all certificates verified: min(cost_A, cost_B) <= 4/3 OPT in every case")
