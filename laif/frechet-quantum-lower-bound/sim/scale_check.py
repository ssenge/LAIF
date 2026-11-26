"""Edge-model directed grid reachability (edges (x,y)->(x+1,y), (x,y)->(x,y+1)) equals cell-model monotone reachability with
moves right/up/diagonal on the 3x scaled grid: vertex (x,y) -> cell (3x,3y), always free; edge -> its two cells, free iff the edge
is present; all other cells blocked. Random and exhaustive small instances."""
import itertools, random

def edge_reach(n, k, H, V):            # H[(x,y)]: edge (x,y)->(x+1,y), V[(x,y)]: (x,y)->(x,y+1); grid 0..n x 0..k
    R = {(0, 0)}
    for x in range(n + 1):
        for y in range(k + 1):
            if (x, y) in R:
                if x < n and H[(x, y)]: R.add((x + 1, y))
                if y < k and V[(x, y)]: R.add((x, y + 1))
    return (n, k) in R

def cell_reach(n, k, H, V):
    X, Y = 3 * n, 3 * k
    free = set()
    for x in range(n + 1):
        for y in range(k + 1):
            free.add((3 * x, 3 * y))
            if x < n and H[(x, y)]: free |= {(3 * x + 1, 3 * y), (3 * x + 2, 3 * y)}
            if y < k and V[(x, y)]: free |= {(3 * x, 3 * y + 1), (3 * x, 3 * y + 2)}
    R = {(0, 0)}
    for x in range(X + 1):
        for y in range(Y + 1):
            if (x, y) in R:
                for d in ((1, 0), (0, 1), (1, 1)):
                    c = (x + d[0], y + d[1])
                    if c in free: R.add(c)
    return (X, Y) in R

def edges(n, k):
    return [(x, y) for x in range(n) for y in range(k + 1)], [(x, y) for x in range(n + 1) for y in range(k)]

if __name__ == "__main__":
    tot = 0
    for n, k in ((1, 1), (2, 1), (2, 2)):       # exhaustive
        he, ve = edges(n, k)
        for bits in itertools.product((0, 1), repeat=len(he) + len(ve)):
            H = dict(zip(he, bits[:len(he)])); V = dict(zip(ve, bits[len(he):]))
            assert edge_reach(n, k, H, V) == cell_reach(n, k, H, V); tot += 1
    rng = random.Random(1)
    for _ in range(3000):                        # random, larger
        n, k = rng.randint(2, 9), rng.randint(2, 9); p = rng.choice((0.5, 0.6, 0.7, 0.8))
        he, ve = edges(n, k)
        H = {e: int(rng.random() < p) for e in he}; V = {e: int(rng.random() < p) for e in ve}
        assert edge_reach(n, k, H, V) == cell_reach(n, k, H, V); tot += 1
    print(f"ok: {tot} instances, edge reachability = scaled cell reachability with diagonal moves")
