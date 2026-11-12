"""Directed primitives on planar networks: centralized simulation of notes/DIRECTED.md.

Checks the logic of the out-forest, the order of the condensation and depth-first search on the tree of bags.
It does not simulate rounds: reachability inside a child is computed directly, where the note reads it from labels.
Every FAIL counter is a claim of the note.

python3 -I dirs.py SEED SECS [big]    main lane
python3 -I dirs.py ctl SEED SECS      negative controls
"""
import collections, json, os, random, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
import fam
import mm
import gm


def key(u, v):
    return (min(u, v), max(u, v))


def inside(arcs, Y):
    """Arcs of the digraph on edges of the bag Y."""
    out = collections.defaultdict(set)
    for u, vs in arcs.items():
        for v in vs:
            if key(u, v) in Y.eset:
                out[u].add(v)
    return out


def reach(arcs, srcs):
    seen, st = set(srcs), list(srcs)
    while st:
        x = st.pop()
        for y in arcs.get(x, ()):
            if y not in seen:
                seen.add(y)
                st.append(y)
    return seen


# ---------------------------------------------------------------- out-forest, Section 3
def forest(Y, arcs, A, st, mode='ok', rng=None):
    """Parent arcs for all vertices reached from A in `arcs`, inside the bag Y. Returns {x: parent}."""
    st['chk.forest_bags'] += 1
    A = set(A) & Y.V
    if not Y.kids:
        par, cur = {}, sorted(A)
        seen = set(A)
        while cur:
            nxt = []
            for u in cur:
                for v in sorted(arcs.get(u, ())):
                    if v not in seen:
                        seen.add(v)
                        par[v] = u
                        nxt.append(v)
            cur = nxt
        if mode == 'leafany':
            ins = collections.defaultdict(list)
            for u, vs in arcs.items():
                for v in vs:
                    if u in seen:
                        ins[v].append(u)
            for v in par:
                par[v] = rng.choice(ins[v])
        return par
    S = Y.sep
    kids = Y.kids
    D = [inside(arcs, c) for c in kids]
    # who reaches what inside each child
    R_hub = [{a: reach(D[j], [a]) for a in S if a in c.V} for j, c in enumerate(kids)]
    R_star = [reach(D[j], [a for a in A - S if a in c.V]) for j, c in enumerate(kids)]
    if mode == 'nostar':
        R_star = [set() for _ in kids]
    INF = 10 ** 9
    lab = {x: 0 for x in A}
    # breadth first on hubs: level 0 is A and the star of each child
    frontier = [('*', j) for j in range(len(kids))] + [(a, j) for a in A & S for j in range(len(kids)) if a in R_hub[j]]
    level = 0
    while frontier:
        new = set()
        for a, j in frontier:
            for b in (R_star[j] if a == '*' else R_hub[j][a]) & S:
                if b not in lab and b != a:
                    new.add(b)
        level += 1
        for b in new:
            lab[b] = level
        frontier = [(b, j) for b in new for j in range(len(kids)) if b in R_hub[j]]
    st['max.label'] = max(st['max.label'], level)
    for j, c in enumerate(kids):
        for x in c.V - S:
            if x in A:
                continue
            best = INF
            if x in R_star[j]:
                best = 0
            for a, r in R_hub[j].items():
                if x in r and a in lab and a != x:
                    best = min(best, lab[a])
            if best < INF:
                lab[x] = best + 1
    # sources of the children, and the arcs that stay
    par, reached = {}, {}
    for j, c in enumerate(kids):
        Dp = collections.defaultdict(set)
        Ap, low = set(), {}
        for u, vs in D[j].items():
            for v in vs:
                if v in A or u not in lab or v not in lab:
                    continue
                if mode == 'crosslayer' or lab[u] == lab[v]:
                    if u not in A:
                        Dp[u].add(v)
                if lab[u] == lab[v] - 1 and (u in S or u in A):
                    Ap.add(v)
                    low.setdefault(v, u)
        sub = forest(c, Dp, Ap, st, mode, rng)
        got = reach(Dp, Ap)
        for x in c.V - S:
            if x in A or x not in lab:
                continue
            if x not in got:
                st['FAIL.not_reached_in_child'] += 1
                continue
            par[x] = low[x] if x in Ap else sub[x]
        reached[j] = (got, sub, Ap, low)
    for h in S:
        if h in A or h not in lab:
            continue
        cands = [j for j in range(len(kids)) if h in reached[j][0]]
        if not cands:
            st['FAIL.hub_not_reached'] += 1
            continue
        j = rng.choice(cands) if mode == 'randchild' else cands[0]
        got, sub, Ap, low = reached[j]
        par[h] = low[h] if h in Ap else sub[h]
    return par


def check_forest(V, arcs, A, par, st):
    want = reach(arcs, A) - set(A)
    st['chk.forest'] += 1
    if set(par) != want:
        st['FAIL.forest_cover'] += 1
    for x, p in par.items():
        if x not in arcs.get(p, ()):
            st['FAIL.forest_not_arc'] += 1
    done = set(A)
    for x in par:
        seen, y = [], x
        while y not in done:
            if y in seen or y not in par:
                st['FAIL.forest_cycle'] += 1
                break
            seen.append(y)
            y = par[y]
        else:
            done.update(seen)


# ---------------------------------------------------------------- order of the condensation, Section 4
def order(Y, arcs, X, scc, st, mode='ok'):
    """A key on the active vertices X in Y: equal exactly on one strong component, increasing along arcs between two."""
    X = X & Y.V
    S, kids = (Y.sep if Y.kids else Y.V) & X, Y.kids
    D = [inside(arcs, c) for c in kids] if kids else []
    R = [{a: reach(D[j], [a]) for a in S if a in c.V} for j, c in enumerate(kids)]
    J = nx.DiGraph()
    J.add_nodes_from(S)
    if kids:
        for j in range(len(kids)):
            for a, r in R[j].items():
                J.add_edges_from((a, b) for b in r & S if b != a)
    else:
        J.add_edges_from((u, v) for u, vs in arcs.items() for v in vs if u in S and v in S)
    C = nx.condensation(J)
    lam = {}
    for c in nx.topological_sort(C):
        lam[c] = 1 + max((lam[d] for d in C.predecessors(c)), default=-1)
    st['max.layers'] = max(st['max.layers'], 1 + max(lam.values(), default=-1))
    lv = {h: lam[C.graph['mapping'][h]] for h in S}
    # hubs in one strong component of J are exactly the hubs of one strong component
    ids = {}
    for h in S:
        c = C.graph['mapping'][h]
        if ids.setdefault(scc[h], c) != c:
            st['FAIL.J_component'] += 1
    block = {scc[h]: lv[h] for h in S}
    out = {h: (2 * lv[h], scc[h]) for h in S}
    for j, c in enumerate(kids):
        W, L = set(), {}
        for x in (c.V & X) - S:
            if scc[x] in block and mode != 'noblock':
                out[x] = (2 * block[scc[x]], scc[x])
                continue
            W.add(x)
            vals = [lv[a] for a, r in R[j].items() if x in r]
            L[x] = min(vals, default=-1) if mode == 'minlabel' else max(vals, default=-1)
        if not W:
            continue
        Dp = collections.defaultdict(set)
        for u, vs in D[j].items():
            if u in W:
                for v in vs:
                    if v in W and L[u] == L[v]:
                        Dp[u].add(v)
        sub = order(c, Dp, W, scc, st, mode)
        for x in W:
            out[x] = (2 * L[x] + (0 if mode == 'hublayer' else 1), j) + sub[x]
    return out


def check_order(arcs, phi, scc, st):
    st['chk.order'] += 1
    first = {}
    for x, k in phi.items():
        if first.setdefault(scc[x], k) != k:
            st['FAIL.order_split_component'] += 1
    if len(set(phi.values())) != len(first):
        st['FAIL.order_merged_components'] += 1
    for u, vs in arcs.items():
        for v in vs:
            if scc[u] != scc[v] and not phi[u] < phi[v]:
                st['FAIL.order_arc'] += 1


# ---------------------------------------------------------------- depth first search, Section 5
class Tree:
    def __init__(self, roots):
        self.roots = list(roots)
        self.kids = collections.defaultdict(list)
        self.par = {r: None for r in roots}

    def numbers(self):
        pre, post, a, b = {}, {}, 0, 0
        for r in self.roots:
            st = [(r, 0)]
            pre[r] = a
            a += 1
            while st:
                x, i = st.pop()
                if i < len(self.kids[x]):
                    st.append((x, i + 1))
                    c = self.kids[x][i]
                    pre[c] = a
                    a += 1
                    st.append((c, 0))
                else:
                    post[x] = b
                    b += 1
        return pre, post


def owners(T, arcs, pre, post, mode='ok'):
    """owner(x): the tree vertex earliest in post-order that reaches x through non-tree vertices."""
    own = {}
    order = sorted(post, key=lambda v: post[v], reverse=mode == 'latest')
    for u in order:
        st = [u]
        while st:
            x = st.pop()
            for y in arcs.get(x, ()):
                if y not in post and y not in own:
                    own[y] = u
                    st.append(y)
    return own


def check_C(T, arcs, pre, post, st):
    """(C): no path through non-tree vertices from a tree vertex to one to its right."""
    st['chk.C'] += 1
    for u in post:
        seen, stk = {u}, [u]
        while stk:
            x = stk.pop()
            for y in arcs.get(x, ()):
                if y in seen:
                    continue
                seen.add(y)
                if y in post:
                    if pre[y] > pre[u] and post[y] > post[u]:
                        st['FAIL.C'] += 1
                else:
                    stk.append(y)


def dfs(h_root, bags, roots, arcs, st, mode='ok', rng=None):
    T = Tree(roots)
    height = max(b.depth for b in bags)
    by_level = collections.defaultdict(list)
    for b in bags:
        by_level[b.depth].append(b)
    rounds = 0
    for L in range(height + 1):
        lev = 0
        while True:
            pre, post = T.numbers()
            own = owners(T, arcs, pre, post, 'latest' if mode == 'latest' else 'ok')
            reqs = []
            for Y in by_level[L]:
                hubs = sorted(x for x in Y.sep if x in own)
                if hubs:
                    reqs.append((Y, hubs[0]))
            if not reqs:
                break
            lev += 1
            rounds += 1
            used = set()
            for Y, h_ in reqs:
                o = own[h_]
                # a path from o to h_ among vertices owned by o
                prev, q = {}, [o]
                while q and h_ not in prev:
                    nq = []
                    for x in q:
                        for y in sorted(arcs.get(x, ())):
                            if y not in post and y not in prev and (mode == 'anypath' or own.get(y) == o):
                                prev[y] = x
                                nq.append(y)
                    q = nq
                if h_ not in prev:
                    st['FAIL.no_path_in_part'] += 1
                    continue
                path, x = [], h_
                while x != o:
                    path.append(x)
                    x = prev[x]
                path.reverse()
                if o not in Y.V:
                    st['FAIL.owner_not_in_bag'] += 1
                a = o
                for v in path:
                    if v not in Y.V or key(a, v) not in Y.eset:
                        st['FAIL.path_leaves_bag'] += 1
                    a = v
                if used & set(path):
                    st['FAIL.requests_share_a_vertex'] += 1
                    continue
                used |= set(path)
                if mode == 'firstchild':
                    T.kids[o].insert(0, path[0])
                else:
                    T.kids[o].append(path[0])
                T.par[path[0]] = o
                for u, v in zip(path, path[1:]):
                    T.kids[u].append(v)
                    T.par[v] = u
                T.par.setdefault(path[-1], path[-2] if len(path) > 1 else o)
            if st['chk.C'] < st['limit.C'] and len(arcs) <= 400:
                p2, q2 = T.numbers()
                check_C(T, arcs, p2, q2, st)
        st['max.rounds_level'] = max(st['max.rounds_level'], lev)
        if lev > max((len(Y.sep) for Y in by_level[L]), default=0):
            st['FAIL.rounds_above_hubs'] += 1
    st['max.rounds'] = max(st['max.rounds'], rounds)
    return T


def check_dfs(T, arcs, roots, st):
    """A replay of a real depth-first search: at a vertex visit its tree children in order, then see no new vertex."""
    st['chk.dfs'] += 1
    want = reach(arcs, roots)
    if set(T.par) != want:
        st['FAIL.dfs_cover'] += 1
        return
    seen = set()
    for r in T.roots:
        if r in seen:
            st['FAIL.dfs_replay'] += 1
            continue
        seen.add(r)
        stk = [(r, 0)]
        while stk:
            x, i = stk.pop()
            if i < len(T.kids[x]):
                stk.append((x, i + 1))
                c = T.kids[x][i]
                if c in seen or c not in arcs.get(x, ()):
                    st['FAIL.dfs_replay'] += 1
                    continue
                seen.add(c)
                stk.append((c, 0))
            else:
                if any(v not in seen for v in arcs.get(x, ())):
                    st['FAIL.dfs_replay'] += 1


# ---------------------------------------------------------------- instances
def to_sets(arcs):
    out = collections.defaultdict(set)
    for u, vs in arcs.items():
        out[u] |= set(vs)
    return out


def digraph(rng, big):
    k = rng.randrange(8)
    m = 14 if big else 8
    if k == 0:
        V, E, arcs, _, _ = fam.snake(rng.randrange(2, m + 2), rng.randrange(2, m + 2), rng)
        return 'snake', V, E, to_sets(arcs)
    if k == 1:
        V, E, arcs, _, _ = fam.spiral(rng.randrange(2, m + 2), rng)
        return 'spiral', V, E, to_sets(arcs)
    if k == 2:
        V, E, arcs, _, _ = fam.griddag(rng.randrange(2, m + 2), rng.randrange(2, m + 2), rng)
        return 'griddag', V, E, to_sets(arcs)
    if k == 3:
        V, E, arcs = fam.manhattan(rng.randrange(2, m + 2), rng.randrange(2, m + 2), rng)
        return 'manhattan', V, E, to_sets(arcs)
    name, (V, E) = gm.sample(rng, big)
    E = [key(*e) for e in E]
    if k == 4:
        return name + '.dag', V, E, to_sets(fam.orient(V, E, rng, 'dag'))
    if k == 5:
        return name + '.rand', V, E, to_sets(fam.orient(V, E, rng, 'rand'))
    # both directions on most edges: strongly connected regions with planted one-way arcs
    p = rng.choice([0.5, 0.8, 1.0])
    out = collections.defaultdict(set)
    for u, v in E:
        if rng.random() < p:
            out[u].add(v)
            out[v].add(u)
        elif rng.random() < 0.5:
            out[u].add(v)
        else:
            out[v].add(u)
    return name + '.bi', V, E, out


def acyclic(arcs, V):
    G = nx.DiGraph()
    G.add_nodes_from(V)
    G.add_edges_from((u, v) for u, vs in arcs.items() for v in vs)
    return nx.is_directed_acyclic_graph(G), G


def build(V, E, rng):
    return mm.build(V, E, rng, leaf=rng.choice([1, 2, 4, 6]), closure=rng.choice([False, False, True, 'two']))


def run_one(rng, st, big=False, mode='ok', only=None):
    name, V, E, arcs = digraph(rng, big)
    if not V:
        return
    ok, _ = nx.check_planarity(nx.Graph(E))
    st['chk.planar'] += 1
    if not ok:
        st['FAIL.not_planar'] += 1
    root, bags = build(V, E, rng)
    st['max.n'] = max(st['max.n'], len(V))
    st['max.depth'] = max(st['max.depth'], max(b.depth for b in bags))
    st['max.sep'] = max(st['max.sep'], max(len(b.sep) for b in bags))
    st['runs'] += 1
    if only in (None, 'forest'):
        k = rng.choice([1, 1, 2, 3, max(1, len(V) // 5)])
        A = set(rng.sample(sorted(V), min(k, len(V))))
        par = forest(root, arcs, A, st, mode if only else 'ok', rng)
        check_forest(V, arcs, A, par, st)
    dag, G = acyclic(arcs, V)
    if only in (None, 'order'):
        C = nx.condensation(G)
        scc = C.graph['mapping']
        phi = order(root, arcs, set(V), scc, st, mode if only else 'ok')
        check_order(arcs, phi, scc, st)
        st['chk.dag'] += int(dag)
    if only in (None, 'dfs'):
        if rng.random() < 0.7:
            roots = [rng.choice(sorted(V))]
        else:
            C = nx.condensation(G)
            roots = [min(C.nodes[c]['members']) for c in C.nodes if C.in_degree(c) == 0]
            rng.shuffle(roots)
        T = dfs(root, bags, roots, arcs, st, mode if only else 'ok', rng)
        check_dfs(T, arcs, roots, st)


def lane(seed, secs, big=False):
    rng = random.Random(seed)
    st = collections.Counter()
    st['limit.C'] = 10 ** 9
    t0 = time.time()
    while time.time() - t0 < secs:
        run_one(rng, st, big)
    return dict(sorted((k, int(v)) for k, v in st.items()))


CTL = {'nostar': 'forest', 'randchild': 'forest', 'crosslayer': 'forest', 'leafany': 'forest',
       'minlabel': 'order', 'hublayer': 'order', 'noblock': 'order',
       'latest': 'dfs', 'firstchild': 'dfs'}


def controls(seed, secs):
    out = {}
    for mode, only in CTL.items():
        rng = random.Random(seed)
        st = collections.Counter()
        st['limit.C'] = 10 ** 9
        t0 = time.time()
        while time.time() - t0 < secs:
            try:
                run_one(rng, st, False, mode, only)
            except (KeyError, nx.NetworkXUnfeasible, nx.NetworkXError):
                st['FAIL.crash'] += 1
                st['runs'] += 1
        out[mode] = {k: int(v) for k, v in st.items() if k.startswith('FAIL') or k == 'runs'}
    return out


if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == 'ctl':
        print(json.dumps(controls(int(a[1]), float(a[2])), indent=0))
    else:
        print(json.dumps(lane(int(a[0]), float(a[1]), len(a) > 2), indent=0))
