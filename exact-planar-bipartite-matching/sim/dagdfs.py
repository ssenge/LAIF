"""Depth-first search of a planar DAG: centralized simulation of notes/DAG_DFS.md.

Checks the logic of the Split Lemma and of the algorithm. It does not simulate rounds: reachability is computed
directly where the note uses labels, and the separator is a fundamental cycle of a triangulation, not the protocol of [5].
Every FAIL counter is a claim of the note. Instances are DAGs and, to test the Split Lemma and the bound in s, digraphs with cycles.

python3 -I dagdfs.py SEED SECS [big]    main lane
python3 -I dagdfs.py ctl SEED SECS      negative controls
python3 -I dagdfs.py scale              levels against n on large instances
"""
import collections, json, math, os, random, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
import dirs
import fam
import gm

SMALL = 12


def reach(arcs, sources, allowed):
    seen = {s for s in sources if s in allowed}
    stack = list(seen)
    while stack:
        u = stack.pop()
        for v in arcs.get(u, ()):
            if v in allowed and v not in seen:
                seen.add(v)
                stack.append(v)
    return seen


def order_keys(path, arcs, rest, mode='ok'):
    """Least key of each head: deepest vertex of the path first, then the identifier of the head."""
    keyz, via = {}, {}
    k = len(path) - 1
    for i, v in enumerate(path):
        depth = i if mode == 'shallow' else k - i
        for z in arcs.get(v, ()):
            if z in rest and (depth, z) < keyz.get(z, (10 ** 9, 0)):
                keyz[z], via[z] = (depth, z), v
    return keyz, via


def classes_direct(keyz, arcs, rest):
    """Class of each vertex: the least head that reaches it outside the path."""
    cls, left = {}, set(rest)
    for z in sorted(keyz, key=keyz.get):
        if z in left:
            got = reach(arcs, [z], left)
            for y in got:
                cls[y] = z
            left -= got
    return cls


def classes_bits(keyz, arcs, rest, n):
    """The same by binary search with multi-source reachability, as in the note. Returns the least key of each vertex."""
    code = {z: k[0] * (n + 1) + k[1] for z, k in keyz.items()}
    b = max(1, max(code.values(), default=1).bit_length())
    pre = {y: 0 for y in reach(arcs, list(keyz), rest)}
    for i in range(b, 0, -1):
        kept = {u: [v for v in arcs.get(u, ()) if v in pre and pre[v] == pre[u]] for u in pre}
        src = [z for z, c in code.items() if z in pre and c >> i == pre[z] and not (c >> (i - 1)) & 1]
        got = reach(kept, src, set(pre))
        for y in pre:
            pre[y] = 2 * pre[y] + (0 if y in got else 1)
    return pre, code


def out_tree(x, K, arcs, rng):
    """Any spanning out-tree of K from x. The algorithm must work for each of them, so the shape varies.
    The shape 'any' can give every spanning out-tree. The others give first-visit trees only."""
    how = rng.choice(['queue', 'stack', 'random', 'any'])
    if how == 'any':
        par, seen, front = {}, {x}, [(x, v) for v in arcs.get(x, ()) if v in K]
        while front:
            u, v = front.pop(rng.randrange(len(front)))
            if v not in seen:
                seen.add(v)
                par[v] = u
                front += [(v, w) for w in arcs.get(v, ()) if w in K and w not in seen]
        return par
    par, front = {}, [x]
    seen = {x}
    while front:
        i = 0 if how == 'queue' else -1 if how == 'stack' else rng.randrange(len(front))
        u = front.pop(i)
        vs = [v for v in arcs.get(u, ()) if v in K and v not in seen]
        rng.shuffle(vs)
        for v in vs:
            seen.add(v)
            par[v] = u
            front.append(v)
    return par


def root_path(par, w):
    p = [w]
    while p[-1] in par:
        p.append(par[p[-1]])
    return p[::-1]


def separator(x, K, arcs, par, st):
    """A pair u, v whose tree path is a balanced separator: the dual edge of a triangulation that splits the face weight best."""
    U = nx.Graph()
    U.add_nodes_from(K)
    U.add_edges_from((u, v) for u in K for v in arcs.get(u, ()) if v in K)
    ok, emb = nx.check_planarity(U)
    if not ok:
        st['FAIL.not_planar'] += 1
    tri, _ = nx.algorithms.planar_drawing.triangulate_embedding(emb, True)
    face, faces = {}, []
    for a, b in list(tri.edges()):
        if (a, b) not in face:
            f = len(faces)
            walk = tri.traverse_face(a, b, set())
            faces.append(walk)
            for i, p in enumerate(walk):
                face[(p, walk[(i + 1) % len(walk)])] = f
    w = [0] * len(faces)
    done = set()
    for (a, _b), f in face.items():
        if a not in done:
            done.add(a)
            w[f] += 1
    tree = {frozenset((v, p)) for v, p in par.items()}
    adj = collections.defaultdict(list)
    for (a, b), f in face.items():
        if frozenset((a, b)) not in tree:
            g = face[(b, a)]
            adj[f].append((g, a, b))
    # subtree weights on the dual tree
    root, seen, order, up = 0, {0}, [0], {}
    for f in order:
        for g, a, b in adj[f]:
            if g not in seen:
                seen.add(g)
                up[g] = (f, a, b)
                order.append(g)
    if len(seen) != len(faces):
        st['FAIL.dual_not_tree'] += 1
    tot = list(w)
    best, pick = 10 ** 9, None
    for g in reversed(order[1:]):
        f, a, b = up[g]
        side = max(tot[g], sum(w) - tot[g])
        if side < best:
            best, pick = side, (a, b)
        tot[f] += tot[g]
    u, v = pick
    pu, pv = root_path(par, u), root_path(par, v)
    P = set(pu) ^ set(pv)
    common = [a for a, b in zip(pu, pv) if a == b]
    P.add(common[-1])
    H = U.subgraph(K - P)
    big = max((len(c) for c in nx.connected_components(H)), default=0)
    st['chk.balance'] += 1
    if big * 4 > 3 * len(K):
        st['FAIL.unbalanced'] += 1
    st['max.side_x100'] = max(st['max.side_x100'], 100 * big // len(K))
    return pu, pv


def split(K, path, arcs, kids, st, mode, rng, n, bits):
    """Split Lemma: returns the new problems, and fixes the children of the vertices of the path."""
    rest = K - set(path)
    keyz, via = order_keys(path, arcs, rest, mode)
    cls = classes_direct(keyz, arcs, rest)
    if set(cls) != rest:
        st['FAIL.split_not_cover'] += 1
    if bits:
        pre, code = classes_bits(keyz, arcs, rest, n)
        st['chk.bits'] += 1
        if any(code[cls[y]] != pre[y] for y in rest):
            st['FAIL.bits'] += 1
    groups = collections.defaultdict(set)
    for y, z in cls.items():
        groups[z].add(y)
    for z, g in groups.items():
        if reach(arcs, [z], g) != g:
            st['FAIL.class_not_reached'] += 1
    heads = collections.defaultdict(list)
    for z in sorted(groups, key=lambda z: keyz[z]):
        heads[via[z]].append(z)
    for i, v in enumerate(path):
        next_ = [path[i + 1]] if i + 1 < len(path) else []
        if mode == 'headfirst':
            kids[v] = heads[v] + next_
        elif mode == 'revhead':
            kids[v] = next_ + heads[v][::-1]
        else:
            kids[v] = next_ + heads[v]
    return [(z, groups[z]) for z in groups]


def small(x, K, arcs, kids):
    """A problem with few vertices is solved directly."""
    seen = {x}

    def go(u):
        kids[u] = []
        for v in sorted(arcs.get(u, ())):
            if v in K and v not in seen:
                seen.add(v)
                kids[u].append(v)
                go(v)
    go(x)


def absorb(z, Kz, tau, arcs, kids, st, mode, rng, n):
    """One pass on a block: a path from z that ends with a suffix of the block, entered at the least index it can be."""
    if z in tau:
        k = tau.index(z)
        path = tau[k:]
    else:
        ts = set(tau)
        par = out_tree(z, Kz - ts, arcs, rng)
        R = set(par) | {z}
        best = {}
        for u in R:
            for v in arcs.get(u, ()):
                if v in ts and tau.index(v) not in best:
                    best[tau.index(v)] = u
        if not best:
            st['FAIL.block_not_reached'] += 1
            return [(z, Kz)], []
        k = max(best) if mode == 'firsthit' else min(best)
        path = root_path(par, best[k]) + tau[k:]
    return split(Kz, path, arcs, kids, st, mode, rng, n, False), tau[:k]


def dag_dfs(arcs, roots, n, rng, st, mode='ok', scc_size=1):
    kids = {}
    all_ = reach(arcs, roots, set(arcs) | {v for vs in arcs.values() for v in vs} | set(roots))
    keyz = {r: (i, r) for i, r in enumerate(roots)}
    cls = classes_direct(keyz, arcs, all_)
    groups = collections.defaultdict(set)
    for y, z in cls.items():
        groups[z].add(y)
    probs = [(z, groups[z]) for z in groups]
    tops = [r for r in roots if r in groups]
    level, passes = 0, 0
    while probs:
        new = []
        worst = 1
        for x, K in probs:
            if len(K) < SMALL:
                small(x, K, arcs, kids)
                continue
            par = out_tree(x, K, arcs, rng)
            pu, pv = separator(x, K, arcs, par, st)
            sig = [v for v in pv if v not in set(pu)]
            bits = mode == 'ok' and rng.random() < 0.2
            queue = split(K, pu, arcs, kids, st, mode, rng, n, bits)
            left = list(sig)
            iters = 1
            while left and mode != 'onepath':
                iters += 1
                now, nleft = [], []
                for z, Kz in queue:
                    tau = [w for w in left if w in Kz]
                    if not tau:
                        now.append((z, Kz))
                        continue
                    st['chk.block'] += 1
                    i = left.index(tau[0])
                    if left[i:i + len(tau)] != tau:
                        st['FAIL.block_not_contiguous'] += 1
                    got, rest = absorb(z, Kz, tau, arcs, kids, st, mode, rng, n)
                    now += got
                    nleft += rest
                if len(nleft) >= len(left):
                    st['FAIL.block_no_progress'] += 1
                    break
                queue, left = now, sorted(nleft, key=sig.index)
            worst = max(worst, iters)
            for z, Kz in queue:
                st['chk.class_size'] += 1
                if len(Kz) * 4 > 3 * len(K):
                    st['FAIL.class_big'] += 1
            new += queue
        st['max.passes_per_level'] = max(st['max.passes_per_level'], worst)
        if scc_size == 1 and worst > 2:
            st['FAIL.dag_more_than_two_passes'] += 1
        if worst > scc_size + 1:
            st['FAIL.passes_above_scc'] += 1
        passes += worst
        probs = new
        level += 1
        if level > math.log(max(n, 2) / SMALL, 4 / 3) + 3 if n > SMALL else level > 2:
            st['FAIL.levels'] += 1
            break
    st['max.levels'] = max(st['max.levels'], level)
    st['max.passes'] = max(st['max.passes'], passes)
    st['max.levels_over_log_x100'] = max(st['max.levels_over_log_x100'], int(100 * level / max(1, math.log2(max(n, 2)))))
    return tops, kids, all_


def check(tops, kids, all_, arcs, roots, st, topo):
    """A replay of a real search: visit the tree children in order, then find nothing new among the other arcs."""
    st['chk.dfs'] += 1
    seen, post = set(), []
    bad = 0
    for r in tops:
        if r in seen:
            bad += 1
            continue
        seen.add(r)
        stack = [(r, iter(kids.get(r, ())))]
        while stack:
            x, it = stack[-1]
            c = next(it, None)
            if c is None:
                stack.pop()
                post.append(x)
                bad += sum(1 for v in arcs.get(x, ()) if v not in seen)
            elif c in seen or c not in arcs.get(x, ()):
                bad += 1
            else:
                seen.add(c)
                stack.append((c, iter(kids.get(c, ()))))
    if seen != all_:
        bad += 1
    # roots out of order: an earlier root must not leave anything for a later one to steal
    if bad:
        st['FAIL.replay'] += 1
    if topo and not bad:
        st['chk.topo'] += 1
        rank = {v: i for i, v in enumerate(reversed(post))}
        if any(rank[u] >= rank[v] for u in arcs for v in arcs[u]):
            st['FAIL.topological'] += 1


# ---------------------------------------------------------------- instances
def orient_order(V, E, rng):
    """A DAG from a vertex order: random, breadth first or depth first, the last two with one source if connected."""
    G = nx.Graph(E)
    G.add_nodes_from(V)
    how = rng.choice(['random', 'bfs', 'dfs', 'rbfs', 'rdfs'])
    if how == 'random':
        o = list(V)
        rng.shuffle(o)
    else:
        o = []
        seen = set()
        for r in rng.sample(sorted(V), len(V)):
            if r not in seen:
                it = nx.bfs_tree(G, r) if 'bfs' in how else nx.dfs_tree(G, r)
                o += list(it)
                seen |= set(it)
        if how[0] == 'r':
            o.reverse()
    pos = {v: i for i, v in enumerate(o)}
    out = collections.defaultdict(set)
    for u, v in E:
        if pos[u] < pos[v]:
            out[u].add(v)
        else:
            out[v].add(u)
    return out


def digraph(rng, big, how=None):
    how = how or rng.choice(['order', 'order', 'griddag', 'general'])
    if how == 'griddag':
        m = 14 if big else 8
        V, E, arcs, _, _ = fam.griddag(rng.randrange(2, m + 2), rng.randrange(2, m + 2), rng)
        return 'griddag', V, E, dirs.to_sets(arcs)
    if how == 'general':
        return dirs.digraph(rng, big)
    name, (V, E) = gm.sample(rng, big)
    E = sorted({(min(e), max(e)) for e in E if e[0] != e[1]})
    return name + '.dag', V, E, orient_order(V, E, rng)


def run_one(rng, st, big=False, mode='ok', how=None):
    name, V, E, arcs = digraph(rng, big, how)
    if len(V) < 2:
        return
    st['chk.planar'] += 1
    if not nx.check_planarity(nx.Graph(E))[0]:
        st['FAIL.not_planar'] += 1
    D = nx.DiGraph()
    D.add_nodes_from(V)
    D.add_edges_from((u, v) for u, vs in arcs.items() for v in vs)
    C = nx.condensation(D)
    s_ = max(len(C.nodes[c]['members']) for c in C.nodes)
    dag = s_ == 1
    st['chk.dag'] += int(dag)
    if rng.random() < 0.5:
        roots = [min(C.nodes[c]['members']) for c in C.nodes if C.in_degree(c) == 0]
        rng.shuffle(roots)
        forest = True
    else:
        roots = [rng.choice(sorted(V))]
        forest = False
    tops, kids, all_ = dag_dfs(arcs, roots, len(V), rng, st, mode, s_)
    check(tops, kids, all_, arcs, roots, st, forest and dag)
    if not dag and mode == 'ok' and rng.random() < 0.5:
        condensed(C, rng, st)
    st['runs'] += 1
    st['max.n'] = max(st['max.n'], len(V))
    st['fam.' + name] += 1


def condensed(C, rng, st):
    """Integer ranks of the strong components: the same search on the condensation, which is a planar DAG."""
    arcs = {u: set(C[u]) for u in C.nodes}
    U = nx.Graph()
    U.add_nodes_from(C.nodes)
    U.add_edges_from(C.edges)
    st['chk.cond_planar'] += 1
    if not nx.check_planarity(U)[0]:
        st['FAIL.not_planar'] += 1
    roots = [c for c in C.nodes if C.in_degree(c) == 0]
    rng.shuffle(roots)
    tops, kids, all_ = dag_dfs(arcs, roots, C.number_of_nodes(), rng, st)
    check(tops, kids, all_, arcs, roots, st, True)
    st['chk.cond'] += 1


def lane(seed, secs, big=False):
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    while time.time() - t0 < secs:
        run_one(rng, st, big)
    return dict(sorted((k, int(v)) for k, v in st.items()))


CTL = ['shallow', 'headfirst', 'revhead', 'onepath', 'firsthit']


def controls(seed, secs):
    out = {}
    for mode in CTL:
        rng = random.Random(seed)
        st = collections.Counter()
        t0 = time.time()
        while time.time() - t0 < secs:
            run_one(rng, st, True, mode, 'order' if mode == 'firsthit' else None)
        out[mode] = {k: int(v) for k, v in st.items() if k.startswith('FAIL') or k == 'runs'}
    return out


def scale():
    rng = random.Random(1)
    for name, make in (('griddag', lambda m: fam.griddag(m, m, rng)[:3]), ('stacked', lambda m: None)):
        for m in (10, 20, 40, 80):
            st = collections.Counter()
            if name == 'griddag':
                V, E, arcs = make(m)
                arcs = dirs.to_sets(arcs)
            else:
                V, E = gm.stacked_drop(m * m, rng, 0.2)
                E = sorted({(min(e), max(e)) for e in E if e[0] != e[1]})
                arcs = orient_order(V, E, rng)
            D = nx.DiGraph()
            D.add_nodes_from(V)
            D.add_edges_from((u, v) for u, vs in arcs.items() for v in vs)
            roots = [v for v in V if D.in_degree(v) == 0]
            tops, kids, all_ = dag_dfs(arcs, roots, len(V), rng, st)
            check(tops, kids, all_, arcs, roots, st, True)
            print(json.dumps({'fam': name, 'n': len(V), 'levels': st['max.levels'], 'passes': st['max.passes'], 'log2n': round(math.log2(len(V)), 1),
                              'fails': sum(v for k, v in st.items() if k.startswith('FAIL'))}), flush=True)


if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == 'ctl':
        print(json.dumps(controls(int(a[1]), float(a[2])), indent=0))
    elif a[0] == 'scale':
        scale()
    else:
        print(json.dumps(lane(int(a[0]), float(a[1]), len(a) > 2), indent=0))
