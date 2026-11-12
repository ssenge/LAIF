"""Max 2-CSP with a cardinality constraint: scores as count tables, checked against brute force.

A score is a table over the number c of variables set to 1, in the semiring with pointwise max as sum
and max-plus convolution as product. The procedure mirrors Section 2b: reductions of degree 0, 1 and 2,
branching on a vertex, and at a split into components a table for every component but the largest,
obtained from one value per count (the value calls), multiplied into the nullary score of the tail.
"""
import itertools
import random

NEG = float("-inf")


def unit(N):
    return [0] + [NEG] * N


def conv(a, b):
    N = len(a) - 1
    out = [NEG] * (N + 1)
    for i, x in enumerate(a):
        if x == NEG:
            continue
        for j, y in enumerate(b[: N + 1 - i]):
            if y != NEG and x + y > out[i + j]:
                out[i + j] = x + y
    return out


def tmax(a, b):
    return [max(x, y) for x, y in zip(a, b)]


def const(v, N):
    return [v] + [NEG] * N


class Inst:
    def __init__(self, N, verts, un, ed, tau):
        self.N, self.verts, self.un, self.ed, self.tau = N, set(verts), un, ed, tau

    def copy(self):
        return Inst(self.N, self.verts, {v: [t[:] for t in self.un[v]] for v in self.verts},
                    {k: [[t[:] for t in row] for row in tab] for k, tab in self.ed.items()}, self.tau[:])

    def nbrs(self, v):
        return [y if x == v else x for (x, y) in self.ed if v in (x, y)]

    def e(self, x, y):  # table indexed [phi(x)][phi(y)]
        if (x, y) in self.ed:
            return self.ed[(x, y)]
        t = self.ed[(y, x)]
        return [[t[b][a] for b in range(2)] for a in range(2)]

    def put(self, x, y, tab):  # multiply into the edge xy
        if (y, x) in self.ed:
            x, y, tab = y, x, [[tab[b][a] for b in range(2)] for a in range(2)]
        old = self.ed.get((x, y))
        self.ed[(x, y)] = tab if old is None else [[conv(old[a][b], tab[a][b]) for b in range(2)] for a in range(2)]

    def drop(self, v):
        self.verts.discard(v)
        self.un.pop(v)
        for k in [k for k in self.ed if v in k]:
            del self.ed[k]


def reduce_once(I):
    for v in sorted(I.verts):
        nb = I.nbrs(v)
        if len(nb) == 0:
            I.tau = conv(I.tau, tmax(I.un[v][0], I.un[v][1]))
            I.drop(v)
            return True
        if len(nb) == 1:
            x = nb[0]
            ex = I.e(x, v)
            for c in range(2):
                I.un[x][c] = conv(I.un[x][c], tmax(conv(ex[c][0], I.un[v][0]), conv(ex[c][1], I.un[v][1])))
            I.drop(v)
            return True
        if len(nb) == 2:
            x, z = nb
            ex, ez = I.e(x, v), I.e(v, z)
            tab = [[tmax(*[conv(conv(ex[a][b], I.un[v][b]), ez[b][c]) for b in range(2)]) for c in range(2)]
                   for a in range(2)]
            I.drop(v)
            I.put(x, z, tab)
            return True
    return False


def components(I):
    seen, comps = set(), []
    for s in sorted(I.verts):
        if s in seen:
            continue
        comp, stack = set(), [s]
        while stack:
            v = stack.pop()
            if v in comp:
                continue
            comp.add(v)
            stack.extend(I.nbrs(v))
        seen |= comp
        comps.append(comp)
    return comps


def restrict(I, comp, tau):
    return Inst(I.N, comp, {v: I.un[v] for v in comp},
                {k: t for k, t in I.ed.items() if k[0] in comp}, tau)


def solve(I, stats):
    """The table of I: for every count c, the largest score of an assignment with c ones."""
    I = I.copy()
    while stats.get("reduce", True) and reduce_once(I):
        pass
    if not I.verts:
        return I.tau
    comps = components(I)
    if len(comps) > 1:
        comps.sort(key=len)
        tail = comps[-1]
        tau = I.tau
        for comp in comps[:-1]:
            assert 2 * len(comp) <= len(I.verts)          # (H2): a value call has at most half the size
            sub = solve(restrict(I, comp, unit(I.N)), stats)
            stats["calls"] += len(comp) + 1                # one value per count 0..|comp|
            tab = [sub[c] if c <= len(comp) else NEG for c in range(I.N + 1)]
            tau = conv(tau, tab)
        return solve(restrict(I, tail, tau), stats)       # tail with the tables in its nullary score
    v = max(sorted(I.verts), key=lambda u: len(I.nbrs(u)))
    out = [NEG] * (I.N + 1)
    for a in range(2):                                     # OR over the value of v
        J = I.copy()
        for x in J.nbrs(v):
            ex = J.e(x, v)
            for c in range(2):
                J.un[x][c] = conv(J.un[x][c], ex[c][a])
        J.tau = conv(J.tau, J.un[v][a])
        J.drop(v)
        out = tmax(out, solve(J, stats))
    return out


def build(n, edges, score):
    N = n
    un = {v: [unit(N), [NEG, 0] + [NEG] * (N - 1)] for v in range(n)}
    ed = {}
    for (x, y) in edges:
        ed[(x, y)] = [[const(score(x, y, a, b), N) for b in range(2)] for a in range(2)]
    return Inst(N, range(n), un, ed, unit(N))


def brute(n, edges, score):
    best = [NEG] * (n + 1)
    for phi in itertools.product(range(2), repeat=n):
        s = sum(score(x, y, phi[x], phi[y]) for (x, y) in edges)
        c = sum(phi)
        best[c] = max(best[c], s)
    return best


def random_graph(rng, n, p):
    return [(x, y) for x in range(n) for y in range(x + 1, n) if rng.random() < p]


if __name__ == "__main__":
    rng = random.Random(7)
    checks = 0
    calls = 0
    for trial in range(300):
        n = rng.randint(1, 11)
        edges = random_graph(rng, n, rng.choice([0.15, 0.3, 0.5]))
        kind = trial % 4
        if kind == 0:   # Max Bisection and Min Bisection read off the cut table at c = n/2
            score = lambda x, y, a, b: int(a != b)
        elif kind == 1:  # Densest k-Subgraph
            score = lambda x, y, a, b: int(a == 1 and b == 1)
        elif kind == 2:  # Max k-Vertex Cover
            score = lambda x, y, a, b: int(a == 1 or b == 1)
        else:           # arbitrary integer scores, including negative ones (Min Bisection is a case)
            w = {(x, y): [[rng.randint(-5, 5) for _ in range(2)] for _ in range(2)] for (x, y) in edges}
            score = lambda x, y, a, b, w=w: w[(x, y)][a][b]
        want = brute(n, edges, score)
        for red in (True, False):   # without reductions the graph splits after branching
            stats = {"calls": 0, "reduce": red}
            got = solve(build(n, edges, score), stats)
            assert got == want, (n, edges, red, got, want)
            checks += 1
            calls += stats["calls"]
    assert calls > 0   # the split with value calls was exercised
    print("value calls in total:", calls)
    # Min Bisection with negated cut scores equals minus the smallest bisection.
    n, edges = 10, random_graph(random.Random(3), 10, 0.4)
    neg = solve(build(n, edges, lambda x, y, a, b: -int(a != b)), {"calls": 0})
    bis = min(sum(int(p[x] != p[y]) for (x, y) in edges)
              for p in itertools.product(range(2), repeat=n) if sum(p) == n // 2)
    assert -neg[n // 2] == bis
    print(checks, "random instances: count tables equal brute force; min bisection", bis)
    print("all asserts passed")
