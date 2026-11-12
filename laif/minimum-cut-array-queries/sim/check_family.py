"""Brute-force checks of the graph family on small cases.

Classes A, B, D, C of t vertices. Each class carries a circulant of degree d_base and weight tau (a clique when
d_base = t - 1). For each cell (i, j) with j in J, one bit selects a perfect matching of the 4-cycle
A_i, B_{i+j}, D_i, C_j. Optionally a fifth class E is joined to A by exactly e fixed edges of weight 1.
"""
import itertools
import random


def base_edges(t, d_base):
    """A circulant with edge connectivity d_base: the d_base / 2 nearest offsets, or a clique."""
    if d_base == t - 1:
        return list(itertools.combinations(range(t), 2))
    assert d_base % 2 == 0
    return sorted({tuple(sorted((i, (i + s) % t))) for i in range(t) for s in range(1, d_base // 2 + 1)})


def graph(t, tau, J, d_base, ones, e=0):
    w = {}

    def add(u, v, wt):
        edge = frozenset((u, v))
        assert len(edge) == 2 and edge not in w, "not simple"
        w[edge] = wt

    for c in "ABDC" + ("E" if e else ""):
        for i, j in base_edges(t, d_base):
            add((c, i), (c, j), tau)
    for i in range(t):
        for j in J:
            a, b, d, c = ("A", i), ("B", (i + j) % t), ("D", i), ("C", j)
            if (i, j) in ones:
                add(a, b, 1)
                add(d, c, 1)
            else:
                add(a, c, 1)
                add(b, d, 1)
    for n, (i, j) in enumerate(itertools.product(range(t), repeat=2)):
        if n < e:
            add(("A", i), ("E", j), 1)
    return w


def min_cuts(w, verts):
    r, rest = verts[0], verts[1:]
    index = {v: b for b, v in enumerate(rest)}
    masks = [(sum(1 << index[v] for v in edge if v != r), r in edge, wt) for edge, wt in w.items()]
    best, shores = None, []
    for mask in range(2 ** len(rest) - 1):
        val = 0
        for m, has_r, wt in masks:
            inside = bin(mask & m).count("1") + (1 if has_r else 0)
            if inside == 1:
                val += wt
        if best is None or val < best:
            best, shores = val, [mask]
        elif val == best:
            shores.append(mask)
    return best, [{r} | {rest[b] for b in range(len(rest)) if mask >> b & 1} for mask in shores]


def check_value(t, tau, J, d_base, cases):
    verts = [(c, i) for c in "ABDC" for i in range(t)]
    cells = list(itertools.product(range(t), J))
    limit = min(tau * d_base // 2, len(cells) // 2)
    degree = lambda w: {v: sum(1 for e in w if v in e) for v in verts}
    fixed = degree(graph(t, tau, J, d_base, set()))
    for _ in range(cases):
        wt = random.randint(0, limit)
        ones = set(random.sample(cells, wt))
        w = graph(t, tau, J, d_base, ones)
        assert degree(w) == fixed
        lam, _ = min_cuts(w, verts)
        assert lam == 2 * wt, (t, tau, J, d_base, wt, lam)
    print(f"t={t} tau={tau} |J|={len(J)} base degree {d_base}: minimum cut 2|x| for |x| <= {limit}")


def check_shore(t, tau, k):
    """With E joined by 2k edges, the shore of the unique minimum cut tells |x| = k - 1 from |x| = k + 1."""
    verts = [(c, i) for c in "ABDCE" for i in range(t)]
    cells = list(itertools.product(range(t), range(t)))
    for wt, expect in ((k - 1, "ACE"), (k + 1, "E")):
        ones = set(random.sample(cells, wt))
        w = graph(t, tau, range(t), t - 1, ones, e=2 * k)
        lam, shores = min_cuts(w, verts)
        classes = {"".join(sorted({v[0] for v in s})) for s in shores}
        comp = {"".join(sorted(set("ABCDE") - set(c))) for c in classes}
        assert lam == min(2 * wt, 2 * k) and len(shores) == 1, (lam, shores)
        assert "".join(sorted(expect)) in classes | comp, (classes, comp)
    print(f"t={t} tau={tau} k={k}: the shore separates |x| = k - 1 from |x| = k + 1")


if __name__ == "__main__":
    random.seed(1)
    for t, tau, cases in [(2, 1, 20), (3, 1, 30), (3, 2, 30), (3, 3, 30), (4, 1, 6), (4, 2, 6)]:
        check_value(t, tau, list(range(t)), t - 1, cases)
    check_value(4, 1, [0, 1], 2, 6)
    check_value(4, 2, [0, 1], 2, 6)
    check_shore(3, 2, 1)
    check_shore(3, 3, 1)
