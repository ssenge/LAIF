"""Lattice + window test for an empty d x h rectangle (d rows, h columns) in an n x m 0/1 grid.
Checks (1) exactly one lattice cell (row = 0 mod d, column = 0 mod h) in every d x h rectangle, (2) the window test
with four Pareto fronts agrees with brute force, (3) the divide-and-conquer front learner returns the Pareto front and
its OR-search cost sum(sqrt(area)) per level stays below sqrt(rows * cols)."""
import math, random

def brute(g, d, h):
    n, m = len(g), len(g[0])
    return any(all(g[i][j] == 0 for i in range(r, r + d) for j in range(c, c + h))
               for r in range(n - d + 1) for c in range(m - h + 1))

def front_dc(pts_in, r0, r1, c0, c1, cost, depth=0):
    """Pareto-minimal points (min row, min col) of the 1-entries in rows [r0,r1), cols [c0,c1); records OR costs."""
    if r0 >= r1 or c0 >= c1:
        return []
    cost.setdefault(depth, 0.0)
    cost[depth] += math.sqrt((r1 - r0) * (c1 - c0))          # OR over the region, then binary search on the column
    inside = [(x, y) for x, y in pts_in if r0 <= x < r1 and c0 <= y < c1]
    if not inside:
        return []
    if r1 - r0 == 1:
        return [(r0, min(y for _, y in inside))]
    mid = (r0 + r1) // 2
    top = [y for x, y in inside if x < mid]
    mtop = min(top) if top else c1
    return front_dc(inside, r0, mid, mtop, c1, cost, depth + 1) + front_dc(inside, mid, r1, c0, mtop, cost, depth + 1)

def pareto(pts):
    return sorted(p for p in pts if not any(q != p and q[0] <= p[0] and q[1] <= p[1] for q in pts))

def window_has_empty(g, cr, cc, d, h, cost):
    """Is there an empty d x h rectangle containing cell (cr, cc)? Offsets a in [0,d), b in [0,h): rows cr-a.."""
    n, m = len(g), len(g[0])
    a_ok = [a for a in range(d) if cr - a >= 0 and cr - a + d <= n]
    b_ok = [b for b in range(h) if cc - b >= 0 and cc - b + h <= m]
    if not a_ok or not b_ok:
        return False
    covered = set()
    for sx in (1, -1):
        for sy in (1, -1):
            # quadrant points as distances (x, y) >= 0 from the cell, x < d, y < h (cell itself in the (+,+) quadrant)
            pts = []
            for x in range(0 if sx == 1 else 1, d):
                for y in range(0 if sy == 1 else 1, h):
                    i, j = cr + sx * x, cc + sy * y
                    if 0 <= i < n and 0 <= j < m and g[i][j]:
                        pts.append((x, y))
            fr = front_dc(pts, 0, d, 0, h, cost)
            assert fr == pareto(pts), (fr, pareto(pts))
            for x, y in fr:   # a 1 at signed offset blocks offsets whose rectangle covers it: a box at one corner
                for a in a_ok:
                    if (sx == 1 and a <= d - 1 - x) or (sx == -1 and a >= x):
                        for b in b_ok:
                            if (sy == 1 and b <= h - 1 - y) or (sy == -1 and b >= y):
                                covered.add((a, b))
    return any((a, b) not in covered for a in a_ok for b in b_ok)

def lattice_test(g, d, h, cost):
    n, m = len(g), len(g[0])
    return any(window_has_empty(g, cr, cc, d, h, cost) for cr in range(0, n, d) for cc in range(0, m, h))

if __name__ == "__main__":
    rng = random.Random(1)
    for d in range(1, 9):
        for r in range(0, 40):
            assert sum(1 for x in range(r, r + d) if x % d == 0) == 1
    trials = 0
    worst = 0.0
    for _ in range(1500):
        n, m = rng.randint(2, 14), rng.randint(2, 14)
        p = rng.choice([0.02, 0.05, 0.1, 0.2, 0.4])
        g = [[1 if rng.random() < p else 0 for _ in range(m)] for _ in range(n)]
        d, h = rng.randint(1, n), rng.randint(1, m)
        cost = {}
        assert lattice_test(g, d, h, cost) == brute(g, d, h), (g, d, h)
        nwin = math.ceil(n / d) * math.ceil(m / h) * 4
        for lev, c in cost.items():
            worst = max(worst, c / (nwin * math.sqrt(d * h)))
        trials += 1
    assert worst <= 1.0 + 1e-9, worst
    print("windows agree with brute force on", trials, "grids; worst per-level cost ratio", round(worst, 3))

def largest_square(g, cost):
    """Binary search on the side with the lattice test (exact inner steps)."""
    lo, hi = 0, min(len(g), len(g[0]))
    while lo < hi:
        k = (lo + hi + 1) // 2
        if lattice_test(g, k, k, cost):
            lo = k
        else:
            hi = k - 1
    return lo

def lower_bound_instance(n, d, blocks_zero):
    """Rows: blocks of d rows separated by rows of ones; block t all zero iff blocks_zero[t], else one 1 in it."""
    g = [[1] * n for _ in range(n)]
    for t, z in enumerate(blocks_zero):
        for i in range(t * (d + 1), t * (d + 1) + d):
            g[i] = [0] * n
        if not z:
            g[t * (d + 1) + (t % d)][(3 * t) % n] = 1
    return g

def max_height(g, d):
    n, m = len(g), len(g[0])
    best = 0
    for r in range(n - d + 1):
        run = 0
        for j in range(m):
            run = run + 1 if all(g[i][j] == 0 for i in range(r, r + d)) else 0
            best = max(best, run)
    return best

def check_more(rng):
    for _ in range(400):
        n, m = rng.randint(1, 12), rng.randint(1, 12)
        p = rng.choice([0.03, 0.1, 0.25])
        g = [[1 if rng.random() < p else 0 for _ in range(m)] for _ in range(n)]
        best = max([k for k in range(0, min(n, m) + 1) if k == 0 or brute(g, k, k)])
        assert largest_square(g, {}) == best
    for n in range(2, 13):
        for d in range(1, n + 1):
            a = (n + 1) // (d + 1)
            for mask in range(1 << a):
                zs = [(mask >> t) & 1 == 1 for t in range(a)]
                g = lower_bound_instance(n, d, zs)
                assert (max_height(g, d) == n) == any(zs), (n, d, zs)
    return True

if __name__ == "__main__":
    assert check_more(random.Random(2))
    print("largest square by binary search agrees with brute force; lower-bound instances checked")
