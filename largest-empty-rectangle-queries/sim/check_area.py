"""Largest empty rectangle by area via dyadic shape classes.
For a class (D, H) of powers of two, every empty rectangle with D <= d < 2D rows and H <= h < 2H columns contains a
lattice cell of spacing (D, H). Around each lattice cell the four quadrant fronts of the 1-cells at distances below
(2D, 2H) determine every rectangle of the class through the cell. Checks that the maximum over classes and lattice
cells of the value computed from the fronts equals the brute-force optimum, with lower limits w on the rows and h0 on
the columns, and that the front learner costs at most sqrt(2D * 2H) per depth and quadrant."""
import math, random, sys
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from check_window import front_dc, pareto

def brute_area(g, w, h0):
    n, m = len(g), len(g[0])
    best = 0
    for r in range(n):
        for c in range(m):
            for d in range(w, n - r + 1):
                for h in range(h0, m - c + 1):
                    if d * h > best and all(g[i][j] == 0 for i in range(r, r + d) for j in range(c, c + h)):
                        best = d * h
    return best

def cell_value(g, cr, cc, D, H, w, h0, cost):
    """Largest area of an empty rectangle through (cr, cc) with D <= d < 2D, H <= h < 2H, d >= w, h >= h0,
    computed from the four fronts only."""
    n, m = len(g), len(g[0])
    fronts = {}
    for sx in (1, -1):
        for sy in (1, -1):
            pts = []
            for x in range(0 if sx == 1 else 1, 2 * D):
                for y in range(0 if sy == 1 else 1, 2 * H):
                    i, j = cr + sx * x, cc + sy * y
                    if 0 <= i < n and 0 <= j < m and g[i][j]:
                        pts.append((x, y))
            c = {}
            fr = front_dc(pts, 0, 2 * D, 0, 2 * H, c)
            assert fr == pareto(pts)
            for lev, v in c.items():
                assert v <= math.sqrt(4 * D * H) + 1e-9
                cost[lev] = max(cost.get(lev, 0.0), v)
            fronts[(sx, sy)] = fr
    best = 0
    for d in range(max(D, w), min(2 * D, n + 1)):
        for h in range(max(H, h0), min(2 * H, m + 1)):
            if d * h <= best:
                continue
            for a in range(d):
                if not (0 <= cr - a and cr - a + d <= n):
                    continue
                for b in range(h):
                    if not (0 <= cc - b and cc - b + h <= m):
                        continue
                    # rows cr-a .. cr-a+d-1, columns cc-b .. cc-b+h-1; a 1 at distance x below (sx=1) is inside iff x <= d-1-a
                    ok = all(not ((x <= d - 1 - a if sx == 1 else x <= a) and (y <= h - 1 - b if sy == 1 else y <= b))
                             for (sx, sy), fr in fronts.items() for x, y in fr)
                    if ok:
                        best = d * h
                        break
                if best == d * h:
                    break
    return best

def by_classes(g, w, h0):
    n, m = len(g), len(g[0])
    best, cost = 0, {}
    D = 1
    while D <= n:
        H = 1
        while H <= m:
            for cr in range(0, n, D):
                for cc in range(0, m, H):
                    best = max(best, cell_value(g, cr, cc, D, H, w, h0, cost))
            H *= 2
        D *= 2
    return best

if __name__ == "__main__":
    rng = random.Random(7)
    trials = 0
    for _ in range(1200):
        n, m = rng.randint(1, 13), rng.randint(1, 13)
        p = rng.choice([0.0, 0.02, 0.05, 0.1, 0.2, 0.4])
        g = [[1 if rng.random() < p else 0 for _ in range(m)] for _ in range(n)]
        if rng.random() < 0.3:          # structured: rows or columns of ones
            for i in rng.sample(range(n), rng.randint(0, n)):
                if rng.random() < 0.5:
                    g[i] = [1] * m
        w, h0 = rng.choice([1, 1, 2, 3]), rng.choice([1, 1, 2, 3])
        assert by_classes(g, w, h0) == brute_area(g, w, h0), (g, w, h0)
        trials += 1
    print("largest area by dyadic classes agrees with brute force on", trials, "grids")
