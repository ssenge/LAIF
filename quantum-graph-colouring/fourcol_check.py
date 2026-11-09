"""Tests of the polynomial-space 4-colouring tree: the branching of [8] and the terminal algorithms of [9], at the
weights of fourcol_bound.py. An instance is (G, I, S), where I gets colour 4, S is restricted to colours 1, 2, 3, and
U = V - I - S is free, with N(I) inside S.

1. One branching step on random states of graphs of maximum degree 4: the real measure drops satisfy
   sum r^-drop <= 1, and P is colourable if and only if a child is. Asserts also check the structural claims in the
   proofs of the cases of [8].
2. Terminal instances: the three terminal algorithms, as trees with an exact leaf test, agree with brute force, and
   the smallest of their cost bounds is at most r^mu(P). Triangles use the nine local lists, a factor 2 per triangle
   above the 9/2 of Lemma 5.3 of [9], whose block construction is tested separately on blocks of size 1 and 2.
3. Whole algorithm on random graphs: the answer equals brute force and the sum of the terminal costs is at most
   r^mu(root)."""
import itertools as it
import math
import random
import sys
from collections import Counter

from fourcol_bound import ETA, LAM, M, R_CERT, WEIGHTS, g, rows

R, K3, K4, C3, W1, W2 = float(R_CERT), float(WEIGHTS["k3"]), float(WEIGHTS["k4"]), float(WEIGHTS["c"]), float(WEIGHTS["w1"]), float(WEIGHTS["w2"])
ROWS = [[float(v) for v in row] for row in rows()]
Lam = float(LAM)


def comps(adj, free):
    seen, out = set(), []
    for s in sorted(free):
        if s in seen:
            continue
        comp, st = {s}, [s]
        while st:
            for y in adj[st.pop()] & free:
                if y not in comp:
                    comp.add(y)
                    st.append(y)
        seen |= comp
        out.append(comp)
    return out


def clique(adj, c):
    return all(len(adj[v] & c) == len(c) - 1 for v in c)


def mu(adj, I, S):
    m = len(S) * C3
    for c in comps(adj, set(adj) - I - S):
        if len(c) == 3 and clique(adj, c):
            m += K3
        elif len(c) == 4 and clique(adj, c):
            m += K4
        else:
            m += sum({0: 0, 1: W1, 2: W2}.get(len(adj[v] & c), 1) for v in c)
    return m


def list_colourable(adj, dom):
    """Backtracking on lists, for the variables in dom; a vertex outside dom is ignored."""
    order = sorted(dom, key=lambda v: (len(dom[v]), v))
    col = {}

    def go(i):
        if i == len(order):
            return True
        v = order[i]
        for x in sorted(dom[v]):
            if all(col.get(u) != x for u in adj[v]):
                col[v] = x
                if go(i + 1):
                    return True
                del col[v]
        return False
    return go(0)


def brute(adj, I, S):
    return list_colourable(adj, {v: ({4} if v in I else {1, 2, 3} if v in S else {1, 2, 3, 4}) for v in adj})


def parameters(adj, I, S):
    """The two maximal star packings of Section 5.2 of [9], and the vector x = (s1, s', a0..a3, b0..b4)."""
    free = set(S)
    stars = []
    for v in sorted(S):
        nb = sorted(adj[v] & free - {v})
        if v in free and len(nb) >= 3:
            stars.append((v, nb[:3]))
            free -= {v, *nb[:3]}
    assert all(len(adj[v] & free) <= 2 for v in free), "Lemma 5.1"
    s1 = 4 * len(stars)
    U = set(adj) - I - S
    centres = {}
    for u in sorted(U):
        nb = sorted(adj[u] & free)
        if len(nb) >= 3:
            centres[u] = nb[:3]
            free -= set(nb[:3])
    assert all(len(adj[u] & free) <= 2 for u in U - set(centres)), "Lemma 5.1"
    cl = comps(adj, U)
    a, b = [0] * 4, [0] * 5
    for c in cl:
        (a if len(c) == 3 else b)[len(c & set(centres))] += 1
    x = [s1, len(free)] + a + b
    assert sum(x[j] * M[0][j] for j in range(11)) == len(S) and sum(a) + sum(b) == len(cl)
    return stars, centres, free, cl, x


def terminal_colour(adj, I, S, cl, count):
    """Lemma 5.2: choose the vertex of colour 4 in each clique, then 3-colour the rest."""
    for ch in it.product(*[sorted(c) for c in cl]):
        count[0] += 1
        chosen = set(ch)
        if list_colourable(adj, {v: {1, 2, 3} for v in set(adj) - I - chosen}):
            return True
    return False


def star_options(adj, stars):
    return [[{v: {c}} for c in (1, 2, 3)] for v, _ in stars]


def terminal_csp(adj, I, S, stars, centres, cl, count):
    """Lemma 5.4: fix star centres in [3], restrict cliques to lists, then solve the list instance."""
    opts = star_options(adj, stars)
    for c in cl:
        cs, m = sorted(c & set(centres)), len(c)
        if not cs:
            if m == 3:
                t = sorted(c)
                opts.append([{t[a]: ({1, 2, 3} - {cc} if a == xx else {cc, 4}) for a in range(3)} for cc in (1, 2, 3) for xx in range(3)])
            else:
                opts.append([{v: ({1, 2} if v in w else {3, 4}) for v in c} for w in it.combinations(sorted(c), 2)])
        else:
            o = []
            for vals in it.permutations([1, 2, 3, 4], len(cs)):
                o.append({v: {x} for v, x in zip(cs, vals)})
            opts.append(o)
    base = {v: {1, 2, 3} for v in S}
    base.update({u: {1, 2, 3} for c in cl for u in c})
    base.update({v: {4} for v in I})
    for ch in it.product(*opts):
        count[0] += 1
        dom = {k: set(v) for k, v in base.items()}
        for d in ch:
            dom.update({k: set(v) for k, v in d.items()})
        # a clique with fixed centres: the other vertices have lists without those colours; a clique without colour 4
        # among its centres may use colour 4 on another vertex
        for c in cl:
            cs = c & set(centres)
            fixed = set().union(*[dom[v] for v in cs]) if cs else set()
            if cs:
                for u in c - cs:
                    dom[u] = {1, 2, 3, 4} - fixed
        if list_colourable(adj, dom):
            return True
    return False


def terminal_tree(adj, I, S, stars, free_after, cl, count):
    """Lemma 5.5: enumerate the colours of the first stars and the cliques, then list colour paths and cycles."""
    opts = []
    for v, nb in stars:
        opts.append([dict(zip((v, *nb), (c, *rest))) for c in (1, 2, 3) for rest in it.product(*[[x for x in (1, 2, 3) if x != c]] * 3)])
    for c in cl:
        t = sorted(c)
        o = [dict(zip(t, p)) for p in it.permutations([1, 2, 3, 4], len(t)) if 4 in p]
        opts.append(o)
    rest = set(S) - {x for v, nb in stars for x in (v, *nb)}
    for ch in it.product(*opts):
        count[0] += 1
        col = {v: 4 for v in I}
        for d in ch:
            col.update(d)
        if any(col.get(u) == x for v, x in col.items() for u in adj[v]):
            continue
        dom = {v: {x for x in (1, 2, 3) if all(col.get(u) != x for u in adj[v])} for v in rest}
        if list_colourable(adj, dom):
            return True
    return False


def cost(x):
    return [sum(ROWS[a][j] * x[j] for j in range(11)) for a in range(3)]


def branch(adj, C):
    d = {v: len(adj[v] & C) for v in C}
    N = lambda v: adj[v] & C
    NN = lambda X: set().union(*[N(x) for x in X])
    take = lambda X, *Y: (set(X), NN(X) | set(Y))
    lo, hi = min(d.values()), max(d.values())
    if lo == 1:
        v = next(x for x in sorted(C) if d[x] == 1)
        return "1", [take([v]), take([next(iter(N(v)))])]
    if lo == 2 and hi == 2:
        kids, vs = [], sorted(C)
        for m in range(1, len(vs) + 1):
            for X in it.combinations(vs, m):
                Xs = set(X)
                if not any(N(a) & Xs for a in X) and Xs | NN(X) == C:
                    kids.append(take(X))
        return "2", kids
    if lo >= 2 and hi >= 5:
        v = max(sorted(C), key=lambda x: d[x])
        return "4", [take([v]), (set(), {v})]
    if lo == 2:
        for v in sorted(C):
            if d[v] == 2:
                for a, b in it.permutations(sorted(N(v))):
                    if d[a] >= 3 and (b not in N(a) or d[a] == 4 or d[b] == 4 or d[b] >= 3):
                        return "3.1", [take([v]), take([a]), take([b], a)]
        v = next(x for x in sorted(C) if d[x] == 2 and any(d[y] >= 3 for y in N(x)))
        a, b = sorted(N(v), key=lambda x: d[x])
        assert d[a] == 2 and d[b] == 3 and b in N(a)
        w = next(iter(N(b) - {a, v}))
        assert d[w] >= 3, "3.2"
        if d[w] == 4:
            return "3.2.1", [take([w]), (set(), {w})]
        if any(d[x] == 2 for x in N(w)):
            return "3.2.2", [take([b]), take([v]), take([a])]
        w1, w2 = sorted(N(w) - {b})
        return "3.2.3", [take([w]), take([b]), take([w1], b), take([w2], b, w1)]
    for v in sorted(C):
        if d[v] == 3:
            for p in it.permutations(sorted(N(v))):
                if d[p[0]] == 4 and all(d[x] == 4 or x not in N(p[0]) for x in p[1:]):
                    return "5.1", [take([v]), take([p[0]]), take([p[1]], p[0]), take([p[2]], p[0], p[1])]
    for q in it.combinations(sorted(C), 4):
        if all(b in N(a) for a, b in it.combinations(q, 2)):
            V4, out = [x for x in q if d[x] == 4], sorted(NN(q) - set(q))
            if len(V4) >= 3:
                return "5.2.1", [take([x]) for x in q]
            if len(out) == 1:
                return "5.2.2", [take(out), (set(), set(out))]
            assert len(out) == 2 and len(V4) == 2, "5.2.3"
            return "5.2.3", [take([out[0]]), take([out[1]], out[0]), (set(), set(out))]
    for v in sorted(C):
        four = [x for x in sorted(N(v)) if d[x] == 4]
        if d[v] == 3 and len(four) >= 2:
            v1, v2 = four[:2]
            v3 = next(iter(N(v) - {v1, v2}))
            assert d[v3] == 3 and v3 in N(v1) and v3 in N(v2) and v2 not in N(v1), "5.3"
            w1, w2 = sorted(N(v1) - {v, v3})
            kids = [take([v]), take([v3]), take([v1])]
            if w1 not in N(v2):
                kids.append(take([v2, w1]))
            if w2 not in N(v2):
                kids.append(take([v2, w2], w1))
            return "5.3", kids
    tri = [t for t in it.combinations(sorted(C), 3) if all(b in N(a) for a, b in it.combinations(t, 2)) and any(d[x] == 3 for x in t)]
    if tri:
        t = max(tri, key=lambda t: sum(d[x] == 3 for x in t))
        D = [x for x in t if d[x] == 3]
        T = NN(D) - set(t)
        assert len(D) >= 2 and len(T) >= 2, "Claim 7"
        kids = [take([t[0]]), take([t[1]]), take([t[2]])]
        if not any(N(a) & T for a in T):
            kids.append((set(T), NN(T) | set(t)))
        return "5.4", kids
    if lo == 3:
        assert hi == 3, "5.5"
        v = sorted(C)[0]
        a, b, c = sorted(N(v))
        return "5.5", [take([v]), take([a]), take([b], a), take([c], a, b)]
    assert lo == hi == 4
    v = min(sorted(C), key=lambda v: sum(len(N(x) & N(v)) for x in N(v)))
    nb = sorted(N(v))
    dg = {x: len(N(x) & set(nb)) for x in nb}
    assert max(dg.values()) <= 2, "5.6"
    if max(dg.values()) == 2:
        v1 = next(x for x in nb if dg[x] == 2)
        v2, v3 = sorted(N(v1) & set(nb))
        assert v3 not in N(v2)
        v4 = next(x for x in nb if x not in (v1, v2, v3))
        w = next(iter(N(v1) - {v, v2, v3}))
        kids = [take([v]), take([v1]), take([v2]), take([v3], v2)]
        if w not in N(v4):
            kids.append(take([v4, w], v2, v3))
        return "5.6.1", kids
    for p, q in [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]:
        A, B = [nb[i] for i in p], [nb[i] for i in q]
        if not any(y in N(x) for x in A for y in B):
            return "5.6.2", [take([v]), take([A[0]]), take([B[0]], A[0]), take([A[1]], A[0], B[0]), take([B[1]], A[0], A[1], B[0])]
    raise AssertionError("5.6.2")


def children(adj, I, S, kids):
    out = []
    for X, Y in kids:
        I2, S2 = I | X, S | Y
        if not (I2 & S2 or any(adj[a] & I2 for a in X)):
            out.append((I2, S2 - I2))
    return out


def degree_graph(rng, n):
    adj = {v: set() for v in range(n)}

    def add(a, b):
        if a != b and len(adj[a]) < 4 and len(adj[b]) < 4:
            adj[a].add(b)
            adj[b].add(a)
    v = 0
    while v + 4 <= n and rng.random() < 0.6:
        piece = rng.choice(["tri", "dia", "k4"])
        q = list(range(v, v + (3 if piece == "tri" else 4)))
        for a, b in it.combinations(q, 2):
            if not (piece == "dia" and (a, b) == (q[0], q[3])):
                add(a, b)
        v += len(q)
    t = rng.choice([3, 4, 4])
    for _ in range(40 * n):
        a, b = rng.sample(range(n), 2)
        if len(adj[a]) < t and len(adj[b]) < t:
            add(a, b)
    return adj


def test_steps(count, seed):
    rng, tested, worst = random.Random(seed), Counter(), {}
    for _ in range(count):
        adj = degree_graph(rng, rng.randint(7, 24))
        I, S = set(), set()
        for v in rng.sample(sorted(adj), rng.randint(0, 4)):
            if rng.random() < 0.5:
                if not adj[v] & I and v not in S:
                    I.add(v)
                    S |= adj[v]
            elif v not in I:
                S.add(v)
        free = set(adj) - I - S
        for v in sorted(free):
            if not adj[v] & free:
                I.add(v)
        free = set(adj) - I - S
        rest = [c for c in comps(adj, free) if not (len(c) in (3, 4) and clique(adj, c))]
        if not rest:
            continue
        name, kids = branch(adj, rest[0])
        out = children(adj, I, S, kids)
        m = mu(adj, I, S)
        total = sum(R ** -(m - mu(adj, a, b)) for a, b in out)
        worst[name] = max(worst.get(name, 0), total)
        assert total <= 1 + 1e-9, (name, total)
        assert brute(adj, I, S) == any(brute(adj, a, b) for a, b in out), name
        tested[name] += 1
    print(f"branching steps: {sum(tested.values())} states, largest sum {max(worst.values()):.5f}, cases {dict(sorted(tested.items()))}")


def terminal_instance(rng):
    """Random terminal instance: cliques in U, then S, I with N(I) inside S and no edge between I and U."""
    adj = {}
    v = 0
    cliques = []
    for _ in range(rng.randint(0, 3)):
        m = rng.choice([3, 3, 4])
        cliques.append(list(range(v, v + m)))
        v += m
    U = v
    nS, nI = rng.randint(0, 9), rng.randint(0, 3)
    n = U + nS + nI
    adj = {x: set() for x in range(n)}

    def add(a, b):
        adj[a].add(b)
        adj[b].add(a)
    for c in cliques:
        for a, b in it.combinations(c, 2):
            add(a, b)
    S = list(range(U, U + nS))
    I = list(range(U + nS, n))
    p, q = rng.uniform(0.1, 0.7), rng.uniform(0.1, 0.8)
    for a, b in it.combinations(S, 2):
        if rng.random() < p:
            add(a, b)
    for a in range(U):
        for b in S:
            if rng.random() < q:
                add(a, b)
    for a in I:
        for b in S:
            if rng.random() < 0.3:
                add(a, b)
    return adj, set(I), set(S)


def test_terminal(count, seed):
    rng, used, yes = random.Random(seed), Counter(), 0
    for _ in range(count):
        adj, I, S = terminal_instance(rng)
        stars, centres, free, cl, x = parameters(adj, I, S)
        truth = brute(adj, I, S)
        yes += truth
        cnt = [[0], [0], [0]]
        res = (terminal_colour(adj, I, S, cl, cnt[0]), terminal_csp(adj, I, S, stars, centres, cl, cnt[1]), terminal_tree(adj, I, S, stars, free, cl, cnt[2]))
        assert res == (truth, truth, truth), (res, truth, adj, I, S)
        c = cost(x)
        lhs = math.log(R) * mu(adj, I, S)
        assert sum(float(e) * v for e, v in zip(ETA, c)) <= lhs + 1e-6, "Lemma 5.8"
        used[min(range(3), key=lambda a: c[a])] += 1
    print(f"terminal instances: {count} ({yes} colourable), all three algorithms agree with brute force; cheapest algorithm counts {dict(sorted(used.items()))}")


def test_blocks():
    """Lemma 5.3 of [9]: greedy selection covers every colouring of a block within the stated number of candidates."""
    for j in (1, 2):
        one = [c for c in it.product([1, 2, 3, 4], repeat=3) if len(set(c)) == 3 and 4 in c]
        local = [[({1, 2, 3} - {cc} if v == xx else {cc, 4}) for v in range(3)] for cc in (1, 2, 3) for xx in range(3)]
        cols = list(it.product(one, repeat=j))
        cands = list(it.product(local, repeat=j))
        fits = lambda L, c: all(c[t][v] in L[t][v] for t in range(j) for v in range(3))
        left, chosen = set(range(len(cols))), 0
        cover = [{i for i, c in enumerate(cols) if fits(L, c)} for L in cands]
        assert all(len(s) == 4 ** j for s in cover)
        while left:
            best = max(cover, key=lambda s: len(s & left))
            left -= best
            chosen += 1
        bound = math.ceil(4.5 ** j * j * math.log(18))
        assert chosen <= bound
        print(f"block of {j} triangle(s): {len(cols)} colourings covered by {chosen} candidates, bound {bound}, 4.5^j = {4.5 ** j}")


def test_full(count, seed, nmax, limit):
    rng, done, yes, stopped, used = random.Random(seed), 0, 0, 0, Counter()
    for _ in range(count):
        n = rng.randint(4, nmax)
        adj = {v: set() for v in range(n)}
        kind = rng.choice(["gnp", "hidden", "deg"])
        if kind == "deg":
            adj = degree_graph(rng, n)
        else:
            col = [rng.randrange(4) for _ in range(n)]
            p = rng.uniform(0.2, 0.8)
            for a, b in it.combinations(range(n), 2):
                if (kind == "gnp" or col[a] != col[b]) and rng.random() < p:
                    adj[a].add(b)
                    adj[b].add(a)
        state = dict(nodes=0, total=0.0, answer=False)

        def solve(I, S):
            state["nodes"] += 1
            if state["nodes"] > limit:
                raise TimeoutError
            free = set(adj) - I - S
            for v in sorted(free):
                if not adj[v] & free:
                    return solve(I | {v}, S)
            rest = [c for c in comps(adj, free) if not (len(c) in (3, 4) and clique(adj, c))]
            if not rest:
                stars, centres, fr, cl, x = parameters(adj, I, S)
                c = cost(x)
                a = min(range(3), key=lambda i: c[i])
                state["total"] += math.exp(c[a])
                cnt = [0]
                ans = (terminal_colour(adj, I, S, cl, cnt) if a == 0 else terminal_csp(adj, I, S, stars, centres, cl, cnt) if a == 1 else terminal_tree(adj, I, S, stars, fr, cl, cnt))
                state["answer"] |= ans
                return
            case, kids = branch(adj, rest[0])
            used[case] += 1
            for a, b in children(adj, I, S, kids):                 # the full tree, no stop at an accepting leaf
                solve(a, b)
        try:
            solve(set(), set())
        except TimeoutError:
            stopped += 1
            continue
        assert state["answer"] == brute(adj, set(), set()), adj
        assert state["total"] <= (1 + 1e-6) * R ** mu(adj, set(), set()), "sum of terminal costs"
        done += 1
        yes += state["answer"]
    print(f"whole algorithm, full tree: {done} graphs with n <= {nmax} ({yes} colourable), {stopped} stopped at the node limit; answers equal brute force, terminal costs sum to at most r^mu(root); cases {dict(sorted(used.items()))}")


if __name__ == "__main__":
    test_steps(int(sys.argv[1]) if len(sys.argv) > 1 else 30000, 11)
    test_terminal(int(sys.argv[2]) if len(sys.argv) > 2 else 400, 5)
    test_blocks()
    test_full(int(sys.argv[3]) if len(sys.argv) > 3 else 300, 3, 16, 3000)
