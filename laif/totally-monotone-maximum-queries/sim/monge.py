"""Global maximum of a totally monotone matrix by nested quantum search, and convex polygon diameter.

The algorithm of ../README.md, section 2. solve(M, d) returns (value, cost). The value comes from reading
only the windows the algorithm would search, so a wrong window shows up as a wrong value.

cost is the bound the theorem sums: sqrt(c) per row maximum on a window of c columns, sqrt(cells) for a
flat search, and C*sqrt(sum of squares) for a search over subproblems (variable-time search), with C the
overhead of one nesting level. No circuit runs here; see grover_law.py and qiskit_check.py.
Limits: costs are evaluated on instances and carry no worst-case guarantee beyond the theorem itself.
"""
import math
import numpy as np


def rowmax(M, i, l, u):
    """Leftmost maximum of row i on columns l..u."""
    return l + int(np.argmax(M[i, l:u + 1]))


def _bisect(M, a, b, l, u, k, segs, stats):
    """Row maxima at k rows of a..b in bisection order, sharing windows. Adds the leftover segments."""
    if a > b:
        return 0.0, -np.inf
    if k <= 0:
        segs.append((a, b, l, u))
        return 0.0, -np.inf
    i = (a + b) // 2
    p = rowmax(M, i, l, u)
    cost = math.sqrt(u - l + 1)
    c1, v1 = _bisect(M, a, i - 1, l, p, (k - 1) // 2, segs, stats)
    c2, v2 = _bisect(M, i + 1, b, p, u, k - 1 - (k - 1) // 2, segs, stats)
    return cost + c1 + c2, max(M[i, p], v1, v2)


def solve_rect(M, a, b, l, u, d, C):
    r, c = b - a + 1, u - l + 1
    if r <= 0:
        return -np.inf, 0.0
    if d == 0 or r <= 2:
        return M[a:b + 1, l:u + 1].max(), math.sqrt(r * c)
    k = max(1, round(r ** (1 / (d + 1))))
    segs = []
    cost, v = _bisect(M, a, b, l, u, k, segs, None)
    sub = [solve_rect(M, *s, d - 1, C) for s in segs]
    if sub:
        v = max(v, max(x for x, _ in sub))
        cost += C * math.sqrt(sum(t * t for _, t in sub))
    return v, cost


def solve(M, d=1, C=1.0):
    return solve_rect(M, 0, M.shape[0] - 1, 0, M.shape[1] - 1, d, C)


def witness(M, a, b, l, u, b0=1.0):
    """The recursion of Theorem 3 evaluated on one input: 2*b0*sqrt(c) + sqrt(1 + D1^2 + D2^2) per mid row."""
    if a > b:
        return 0.0
    c = u - l + 1
    if a == b:
        return b0 * math.sqrt(c)
    i = (a + b) // 2
    p = rowmax(M, i, l, u)
    return 2 * b0 * math.sqrt(c) + math.sqrt(1 + witness(M, a, i - 1, l, p, b0) ** 2 + witness(M, i + 1, b, p, u, b0) ** 2)


def is_totally_monotone(M):
    """Leftmost row maxima nondecreasing on all row and column subsets of size 2 (O(rows^2 cols^2) checks)."""
    r, c = M.shape
    for i in range(r):
        for i2 in range(i + 1, r):
            for j in range(c):
                for j2 in range(j + 1, c):
                    if M[i, j] < M[i, j2] and M[i2, j] >= M[i2, j2]:
                        return False
    return True


def is_inverse_monge(M):
    return bool((M[:-1, :-1] + M[1:, 1:] - M[:-1, 1:] - M[1:, :-1] >= 0).all())


def random_monge(n, seed=0, m=None):
    """Inverse Monge: any row and column functions plus a nonnegative density."""
    r = np.random.default_rng(seed)
    m = m or n
    D = r.integers(0, 50, (n, m), dtype=np.int64)
    a = r.integers(-10 ** 6, 10 ** 6, n, dtype=np.int64)
    b = r.integers(-10 ** 6, 10 ** 6, m, dtype=np.int64)
    return np.cumsum(np.cumsum(D, 0), 1) + a[:, None] + b[None, :]


def hard(n, h):
    """Inverse Monge for every bit string h, with maximum equal to OR(h)."""
    i = np.arange(n)
    M = -np.subtract.outer(i, i) ** 2
    M[i, i] = h
    return M


def warped(n, seed=0):
    """Totally monotone and not Monge: an increasing function of each row of a Monge matrix."""
    r = np.random.default_rng(seed)
    M = random_monge(n, seed).astype(np.float64)
    M = (M - M.min()) / (M.max() - M.min() + 1) + 1
    return M ** r.uniform(0.5, 3, (n, 1))


def convex_polygon(n, seed=0):
    """Vertices of a strictly convex polygon with integer coordinates, counterclockwise (Valtr-style)."""
    r = np.random.default_rng(seed)
    vec = set()
    R = max(4, int(n ** 0.75))
    while len(vec) < n * 2:
        x, y = r.integers(-R, R + 1, 2)
        if (x or y) and math.gcd(int(x), int(y)) == 1:
            vec.add((int(x), int(y)))
    vec = list(vec)
    # opposite pairs close the polygon; the distinct primitive directions keep it strictly convex
    chosen, seen = [], set()
    for x, y in vec:
        if (x, y) in seen or (-x, -y) in seen:
            continue
        seen.add((x, y))
        chosen += [(x, y), (-x, -y)]
    chosen = chosen[:n - n % 2]
    chosen.sort(key=lambda v: math.atan2(v[1], v[0]))
    return np.cumsum(np.array(chosen, dtype=np.int64), axis=0)


def dist2(P, Q):
    d = P[:, None, :] - Q[None, :, :]
    return (d * d).sum(axis=2)


def diameter(P, d=1, C=1.0):
    """Squared diameter, and the cost: an OR over the O(n) chain pairs of the halving recursion."""
    n = len(P)
    costs, best = [], 0
    stack = [(0, n)]
    while stack:
        a, b = stack.pop()
        if b - a < 2:
            continue
        m = (a + b) // 2
        v, t = solve(dist2(P[a:m], P[m:b]), d, C)
        best = max(best, int(v))
        costs.append(t)
        stack += [(a, m), (m, b)]
    return best, C * math.sqrt(sum(t * t for t in costs))


def calipers(P):
    """Classical rotating calipers: the O(n) baseline, used here as an independent check."""
    n = len(P)
    if n < 3:
        return int(((P[0] - P[-1]) ** 2).sum())
    cross = lambda o, a, b: (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
    j, best = 1, 0
    for i in range(n):
        ni = (i + 1) % n
        while cross(P[i], P[ni], P[(j + 1) % n]) > cross(P[i], P[ni], P[j]):
            j = (j + 1) % n
        for q in (i, ni):
            best = max(best, int(((P[q] - P[j]) ** 2).sum()))
    return best
