"""Connected planar bipartite instances. Sides come from a proper 2-colouring of the graph."""
import collections, random


def two_colour(V, E):
    adj = {v: [] for v in V}
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    side = {}
    for s in sorted(V):
        if s in side:
            continue
        side[s] = 0
        st = [s]
        while st:
            x = st.pop()
            for y in adj[x]:
                if y not in side:
                    side[y] = 1 - side[x]
                    st.append(y)
                elif side[y] == side[x]:
                    return None
    return side


def largest(V, E):
    adj = {v: [] for v in V}
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    seen, best = set(), set()
    for s in sorted(V):
        if s in seen:
            continue
        c, st = {s}, [s]
        seen.add(s)
        while st:
            x = st.pop()
            for y in adj[x]:
                if y not in seen:
                    seen.add(y)
                    c.add(y)
                    st.append(y)
        if len(c) > len(best):
            best = c
    es = [e for e in E if e[0] in best and e[1] in best]
    idx = {v: i for i, v in enumerate(sorted(best))}
    return set(idx.values()), [(min(idx[u], idx[v]), max(idx[u], idx[v])) for u, v in es]


def grid(a, b, rng, drop=0.0):
    E = []
    for i in range(a):
        for j in range(b):
            v = i * b + j
            if j + 1 < b and rng.random() >= drop:
                E.append((v, v + 1))
            if i + 1 < a and rng.random() >= drop:
                E.append((v, v + b))
    return largest(set(range(a * b)), E)


def stacked(n, rng, keep=None):
    """Random stacked triangulation; a random 2-colouring keeps the bichromatic edges."""
    faces = [(0, 1, 2), (0, 1, 2)]
    E = {(0, 1), (0, 2), (1, 2)}
    for v in range(3, n):
        i = rng.randrange(len(faces))
        a, b, c = faces[i]
        faces[i] = (a, b, v)
        faces += [(b, c, v), (a, c, v)]
        E |= {(a, v), (b, v), (c, v)}
    col = {v: rng.randrange(2) for v in range(n)}
    return largest(set(range(n)), [e for e in sorted(E) if col[e[0]] != col[e[1]]])


def tree(n, rng, branch=None):
    E = []
    for v in range(1, n):
        lo = 0 if branch is None else max(0, v - branch)
        E.append((rng.randrange(lo, v), v))
    return set(range(n)), [(min(e), max(e)) for e in E]


def biwheel(k, rng):
    """Two hubs joined through an even rim: small D, large degree."""
    k = k + k % 2
    E = []
    for i in range(k):
        E.append((2 + i, 2 + (i + 1) % k))
    for i in range(k):
        E.append(((i % 2), 2 + i))
    return largest(set(range(k + 2)), [(min(e), max(e)) for e in E])


def k2m(m, rng):
    return set(range(m + 2)), [(0, 2 + i) for i in range(m)] + [(1, 2 + i) for i in range(m)]


def ladder_comb(k, rng):
    """A spine with long teeth: the separator of a bag can be long compared with a local view."""
    E, nxt = [], k
    for i in range(k - 1):
        E.append((i, i + 1))
    for i in range(k):
        x = i
        for _ in range(rng.randrange(0, 5)):
            E.append((x, nxt))
            x = nxt
            nxt += 1
    return set(range(nxt)), [(min(e), max(e)) for e in E]


def concentric(r, s, rng, drop=0.1):
    """Even cycles of length s joined by spokes."""
    s = s + s % 2
    E = []
    for i in range(r):
        for j in range(s):
            v = i * s + j
            if rng.random() >= drop:
                E.append((v, i * s + (j + 1) % s))
            if i + 1 < r and j % 2 == i % 2 and rng.random() >= drop:
                E.append((v, (i + 1) * s + j))
    return largest(set(range(r * s)), E)


def sample(rng, big=False):
    k = rng.randrange(8)
    m = 14 if big else 8
    if k == 0:
        return 'grid', grid(rng.randrange(2, m), rng.randrange(2, m), rng, rng.choice([0, 0.1, 0.25]))
    if k == 1:
        return 'stacked', stacked(rng.randrange(6, 16 * m // 2), rng)
    if k == 2:
        return 'tree', tree(rng.randrange(4, 8 * m), rng, rng.choice([None, 1, 2, 5]))
    if k == 3:
        return 'biwheel', biwheel(rng.randrange(4, 5 * m), rng)
    if k == 4:
        return 'k2m', k2m(rng.randrange(2, 5 * m), rng)
    if k == 5:
        return 'comb', ladder_comb(rng.randrange(3, 3 * m), rng)
    if k == 6:
        return 'concentric', concentric(rng.randrange(2, m // 2 + 2), rng.randrange(4, m + 4), rng, rng.choice([0, 0.1, 0.3]))
    return 'stacked2', stacked(rng.randrange(6, 40), rng)


def orient(V, E, rng, how):
    """A digraph on a planar graph; every edge gets one direction or none."""
    arcs = collections.defaultdict(list)
    order = list(sorted(V))
    rng.shuffle(order)
    pos = {v: i for i, v in enumerate(order)}
    drop = rng.choice([0, 0.1, 0.3])
    for u, v in E:
        if rng.random() < drop:
            continue
        if how == 'dag':
            a, b = (u, v) if pos[u] < pos[v] else (v, u)
        else:
            a, b = (u, v) if rng.random() < 0.5 else (v, u)
        arcs[a].append(b)
    return arcs


def snake(a, b, rng):
    """Directed boustrophedon on an a x b grid with later-going rungs: the only long routes cross
    every separator many times."""
    def idx(i, j):
        return i * b + (j if i % 2 == 0 else b - 1 - j)

    V, E, arcs = set(range(a * b)), [], collections.defaultdict(list)
    p = rng.choice([0, 0, 0.1, 0.5])
    back = rng.choice([0, 0, 0.1])
    for i in range(a):
        for j in range(b):
            x = idx(i, j)
            if j + 1 < b:
                y = idx(i, j + 1)
                E.append((min(x, y), max(x, y)))
                arcs[min(x, y)].append(max(x, y))
            if i + 1 < a:
                y = idx(i + 1, j)
                E.append((min(x, y), max(x, y)))
                if abs(x - y) == 1 or rng.random() < p:
                    arcs[min(x, y)].append(max(x, y))
                elif rng.random() < back:
                    arcs[max(x, y)].append(min(x, y))
    return V, E, arcs, 0, a * b - 1


def spiral(k, rng):
    """Directed spiral on a k x k grid, from the outside to the centre."""
    pos, x, y, dx, dy = [], 0, 0, 0, 1
    seen = set()
    for _ in range(k * k):
        pos.append((x, y))
        seen.add((x, y))
        nx_, ny = x + dx, y + dy
        if not (0 <= nx_ < k and 0 <= ny < k) or (nx_, ny) in seen:
            dx, dy = dy, -dx
            nx_, ny = x + dx, y + dy
        x, y = nx_, ny
    id_ = {c: i for i, c in enumerate(pos)}
    V, E, arcs = set(range(k * k)), [], collections.defaultdict(list)
    p = rng.choice([0, 0, 0.1])
    for (i, j), u in id_.items():
        for c in ((i + 1, j), (i, j + 1)):
            if c in id_:
                v = id_[c]
                E.append((min(u, v), max(u, v)))
                if abs(u - v) == 1:
                    arcs[min(u, v)].append(max(u, v))
                elif rng.random() < p:
                    arcs[max(u, v)].append(min(u, v))
    return V, E, arcs, 0, k * k - 1


def griddag(a, b, rng):
    """All edges of a grid go right or down: many parallel routes, so many ties in J."""
    V, E, arcs = set(range(a * b)), [], collections.defaultdict(list)
    drop = rng.choice([0, 0, 0.1, 0.25])
    for i in range(a):
        for j in range(b):
            x = i * b + j
            for y, ok in ((x + 1, j + 1 < b), (x + b, i + 1 < a)):
                if ok:
                    E.append((x, y))
                    if rng.random() >= drop:
                        arcs[x].append(y)
    return V, E, arcs, 0, a * b - 1


def manhattan(a, b, rng):
    """Rows and columns alternate in direction: strongly connected, full of directed cycles and ties."""
    V, E, arcs = set(range(a * b)), [], collections.defaultdict(list)
    drop = rng.choice([0, 0, 0.05, 0.15])
    flip = rng.choice([0, 0, 0.1])
    for i in range(a):
        for j in range(b):
            x = i * b + j
            if j + 1 < b:
                y = x + 1
                E.append((x, y))
                f, g = (x, y) if (i % 2 == 0) != (rng.random() < flip) else (y, x)
                if rng.random() >= drop:
                    arcs[f].append(g)
            if i + 1 < a:
                y = x + b
                E.append((x, y))
                f, g = (x, y) if (j % 2 == 0) != (rng.random() < flip) else (y, x)
                if rng.random() >= drop:
                    arcs[f].append(g)
    return V, E, arcs
