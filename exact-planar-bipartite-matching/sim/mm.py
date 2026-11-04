"""Exact bipartite matching on planar graphs: centralized simulation of notes/MATCHING.md.

Checks the logic of the Path Lemma and of the two insertion algorithms, not round counts.
Python: python3 -I run.py ...; every assert is a claim of the note.
"""
import collections, heapq, random


# ---------------------------------------------------------------- decomposition
class Bag:
    __slots__ = ('id', 'V', 'E', 'eset', 'adj', 'parent', 'sep', 'kids', 'depth', 'splus', 'leaf')


def adj_of(V, E):
    a = {v: [] for v in V}
    for u, v in E:
        a[u].append(v)
        a[v].append(u)
    for v in a:
        a[v].sort()
    return a


def comps(V, adj, removed):
    seen, out = set(removed), []
    for s in sorted(V):
        if s in seen:
            continue
        seen.add(s)
        c, st = [s], [s]
        while st:
            x = st.pop()
            for y in adj[x]:
                if y in V and y not in seen:
                    seen.add(y)
                    c.append(y)
                    st.append(y)
        out.append(set(c))
    return out


def pick_sep(V, adj, rng, tries=40):
    """Two paths of a BFS tree, as a fundamental cycle separator. Balance is best effort."""
    r = rng.choice(sorted(V))
    par, order = {r: None}, [r]
    for x in order:
        for y in adj[x]:
            if y in V and y not in par:
                par[y] = x
                order.append(y)

    def up(v):
        p = []
        while v is not None:
            p.append(v)
            v = par[v]
        return p

    cands = [(v, v) for v in order]
    rng.shuffle(cands)
    cands = cands[:tries]
    nt = [(u, v) for u in order for v in adj[u] if v in V and u < v and par.get(u) != v and par.get(v) != u]
    rng.shuffle(nt)
    cands += nt[:tries]
    best, bs = None, None
    for u, v in cands:
        S = set(up(u)) | set(up(v))
        m = max((len(c) for c in comps(V, adj, S)), default=0)
        key = (m, len(S))
        if bs is None or key < bs:
            best, bs = S, key
    return best


def build(V, E, rng, leaf=6, closure=False):
    """Decomposition with the properties the note uses: every edge of a bag lies in a child, and
    a vertex off sep(Y) lies in exactly one child. closure=True puts all of sep(Y) into every
    child; closure=False only the adjacent part; closure='two' makes two children, as the cycle
    separator does, each holding the whole separator and one group of components."""
    bags, nid = [], [0]

    def rec(V, E, parent, depth):
        b = Bag()
        b.id = nid[0]
        nid[0] += 1
        b.V, b.E, b.parent, b.depth = set(V), list(E), parent, depth
        b.eset = {(min(u, v), max(u, v)) for u, v in E}
        b.adj = adj_of(V, E)
        b.kids, b.sep, b.leaf = [], set(), False
        b.splus = set(parent.splus) if parent else set()
        bags.append(b)
        if len(V) <= leaf:
            b.leaf = True
            b.sep = set(V)
            b.splus |= b.sep
            return b
        S = pick_sep(b.V, b.adj, rng)
        Cs = comps(b.V, b.adj, S)
        specs = []
        if closure == 'two':
            groups = [set(), set()]
            for c in Cs:
                groups[rng.randrange(2)] |= c
            for i, c in enumerate(groups):
                W = c | S
                specs.append((W, [e for e in E if e[0] in W and e[1] in W and (e[0] in c or e[1] in c or i == 0 or rng.random() < 0.5)]))
            Cs = []
        for c in Cs:
            hubs = set(S) if closure else {s for s in S if any(y in c for y in b.adj[s])}
            W = c | hubs
            specs.append((W, [e for e in E if e[0] in W and e[1] in W and (e[0] in c or e[1] in c or closure)]))
        covered = {e for _, es in specs for e in es}
        for e in E:
            if e not in covered:
                specs.append(({e[0], e[1]}, [e]))
        if any(len(W) >= len(V) for W, _ in specs):
            b.leaf = True
            b.sep = set(V)
            b.splus |= b.sep
            return b
        b.sep = S
        b.splus |= S
        for W, es in specs:
            b.kids.append(rec(W, es, b, depth + 1))
        return b

    root = rec(V, E, None, 0)
    return root, bags


# ---------------------------------------------------------------- reachability in a bag
def reach_from(Y, arcs, s):
    seen, st = {s}, [s]
    while st:
        x = st.pop()
        for y in arcs.get(x, ()):
            if y in Y.V and y not in seen and (min(x, y), max(x, y)) in Y_edges(Y):
                seen.add(y)
                st.append(y)
    return seen


def Y_edges(Y):
    return Y.eset


def int_set(Y, arcs, u, v, rev):
    """Vertices x with u ~> x ~> v inside Y."""
    a = reach_from(Y, arcs, u)
    b = reach_from(Y, rev, v)
    return a & b


def path_lemma(root, arcs, s, t, st, minhop=True, erase=True, check_disjoint=True, ties=None, budget=None):
    """The Path Lemma: a simple directed s-t path of `arcs` inside the bag `root`. minhop and
    erase switch off the two rules of the note, for the negative controls."""
    rev = collections.defaultdict(list)
    for x, ys in arcs.items():
        for y in ys:
            rev[y].append(x)
    spent = [0]

    def refine(Y, reqs):
        """Requests of Y are pairwise disjoint; returns the realized path of each."""
        st['requests'] += len(reqs)
        spent[0] += len(reqs)
        assert budget is None or spent[0] <= budget, 'budget'
        st['chk.request_bound'] += 1
        if len(reqs) > len((Y.parent.splus if Y.parent else set()) & Y.V) + 2:
            st['FAIL.request_bound'] += 1
        st['max_requests_in_bag'] = max(st['max_requests_in_bag'], len(reqs))
        if check_disjoint and len(reqs) > 1:
            ints = [int_set(Y, arcs, u, v, rev) for u, v in reqs]
            seen = set()
            for I in ints:
                st['chk.requests_disjoint'] += 1
                if seen & I:
                    st['FAIL.requests_disjoint'] += 1
                seen |= I
        if Y.leaf:
            out = []
            for u, v in reqs:
                par = {u: None}
                q = collections.deque([u])
                while q and v not in par:
                    x = q.popleft()
                    out_ = sorted(arcs.get(x, ()))
                    if ties:
                        ties.shuffle(out_)
                    for y in out_:
                        if y in Y.V and y not in par and (min(x, y), max(x, y)) in Y_edges(Y):
                            par[y] = x
                            q.append(y)
                assert v in par, 'leaf request not realizable'
                p = [v]
                while par[p[-1]] is not None:
                    p.append(par[p[-1]])
                out.append(p[::-1])
            return out
        S = Y.splus & Y.V
        kid_of = {}
        for k in Y.kids:
            for x in k.V:
                if x not in Y.sep:
                    assert x not in kid_of, 'vertex off the separator in two children'
                    kid_of[x] = k
        reachk = {}

        def rk(k, x):
            if (k.id, x) not in reachk:
                reachk[k.id, x] = reach_from(k, arcs, x)
            return reachk[k.id, x]

        out, per_kid, plans, visits = [], collections.defaultdict(list), [], collections.Counter()
        for ri, (u, v) in enumerate(reqs):
            nodes = S | {u, v}
            # J: arcs labelled by a child that holds both ends and connects them
            def succs(x):
                got = []
                for k in (Y.kids if x in Y.sep else [kid_of[x]]):
                    if x in k.V:
                        r = rk(k, x)
                        got += [(y, k) for y in sorted(nodes) if y != x and y in k.V and y in r]
                if ties or not minhop:
                    (ties or random.Random(x * 7919 + u)).shuffle(got)
                return got

            par = {u: None}
            if minhop:
                q = collections.deque([u])
                while q and v not in par:
                    x = q.popleft()
                    for y, k in succs(x):
                        if y not in par:
                            par[y] = (x, k)
                            q.append(y)
            else:
                # control: a J path that may have shortcuts; a vertex is taken when first entered
                stack = [(u, iter(succs(u)))]
                while stack and v not in par:
                    x, it = stack[-1]
                    for y, k in it:
                        if y not in par:
                            par[y] = (x, k)
                            stack.append((y, iter(succs(y))))
                            break
                    else:
                        stack.pop()
            assert v in par, 'request not realizable in J'
            seq, x = [], v
            while par[x] is not None:
                seq.append((par[x][0], x, par[x][1]))
                x = par[x][0]
            seq.reverse()
            plans.append(seq)
            for ai in range(len(seq)):
                for bi in range(ai + 1, len(seq)):
                    if seq[bi][2] is seq[ai][2]:
                        st['same_child_pairs'] += 1
            for ai, (a, b, k) in enumerate(seq):
                per_kid[k.id].append((ri, ai, a, b))
        kid_by_id = {k.id: k for k in Y.kids}
        real = {}
        for kid, lst in per_kid.items():
            got = refine(kid_by_id[kid], [(a, b) for _, _, a, b in lst])
            for (ri, ai, _, _), p in zip(lst, got):
                real[ri, ai] = p
        for ri, seq in enumerate(plans):
            walk = []
            for ai in range(len(seq)):
                p = real[ri, ai]
                walk += p if not walk else p[1:]
            cnt = collections.Counter(walk)
            rep = {x for x, c in cnt.items() if c > 1}
            st['chk.repeats_in_sep'] += 1
            if rep - Y.sep:
                st['FAIL.repeats_in_sep'] += 1
            st['walk_repeats'] += len(rep)
            st['max_segments'] = max(st['max_segments'], len(seq))
            for x in Y.sep:
                visits[x] += cnt[x]
            out.append(loop_erase(walk, Y.sep) if erase else walk)
        for x, c in visits.items():
            st['chk.hub_visits'] += 1
            if c > 2:
                st['FAIL.hub_visits'] += 1
        return out

    return refine(root, [(s, t)])[0]


def loop_erase(walk, hubs):
    """Chronological loop erasure that looks only at the visits of hubs."""
    last = {}
    for i, x in enumerate(walk):
        if x in hubs:
            last[x] = i
    out, i = [], 0
    while i < len(walk):
        x = walk[i]
        if x in hubs:
            i = last[x]
        out.append(x)
        i += 1
    return out


# ---------------------------------------------------------------- matching
def residual(C, E, side, match, h):
    """Arcs of the residual digraph on the vertex set C, read from a source h on either side:
    from the side of h along unmatched edges, back along matched edges."""
    arcs = collections.defaultdict(list)
    sh = side[h]
    for u, v in E:
        if u in C and v in C:
            a, b = (u, v) if side[u] == sh else (v, u)
            if match.get(a) == b:
                arcs[b].append(a)
            else:
                arcs[a].append(b)
    for x in arcs:
        arcs[x].sort()
    return arcs


def flip(match, path):
    """path alternates, starting with an unmatched edge from a free vertex and ending at a free one."""
    for i in range(0, len(path) - 1, 2):
        match[path[i]] = path[i + 1]
        match[path[i + 1]] = path[i]


def outer_order(root):
    """Bags by depth, deepest first, with X° = V(X) minus the separators of proper ancestors."""
    levels = collections.defaultdict(list)
    st = [root]
    while st:
        b = st.pop()
        levels[b.depth].append(b)
        st += b.kids
    return [levels[d] for d in sorted(levels, reverse=True)]


def own_set(b):
    return b.V - b.parent.splus if b.parent else set(b.V)


def max_matching(n, V, E, side, rng, st, leaf=6, closure=False, inner_closure=False, minhop=True,
                 erase=True, use_path_lemma=True, skip_hub=None):
    root, _ = build(V, E, rng, leaf=leaf, closure=closure)
    match = {}
    steps = 0
    for level in outer_order(root):
        lvl_max = 0
        for X in level:
            C = own_set(X)
            hubs = sorted(C & X.sep)
            cur = C - set(hubs)
            for ix, h in enumerate(hubs):
                cur.add(h)
                if skip_hub and skip_hub(h):
                    continue
                st['insertions'] += 1
                arcs = residual(cur, E, side, match, h)
                seen, par, stk = {h}, {h: None}, [h]
                while stk:
                    x = stk.pop()
                    for y in arcs.get(x, ()):
                        if y not in seen:
                            seen.add(y)
                            par[y] = x
                            stk.append(y)
                targets = sorted(x for x in seen if x != h and side[x] != side[h] and x not in match)
                if not targets:
                    continue
                t = targets[0]
                st['augmentations'] += 1
                if use_path_lemma:
                    iroot, _ = build(X.V, X.E, rng, leaf=leaf, closure=inner_closure)
                    p = path_lemma(iroot, arcs, h, t, st, minhop=minhop, erase=erase, budget=None if minhop else 4000)
                else:
                    p = [t]
                    while par[p[-1]] is not None:
                        p.append(par[p[-1]])
                    p.reverse()
                st['chk.simple'] += 1
                if len(set(p)) != len(p):
                    st['FAIL.simple'] += 1
                    if not (minhop and erase):
                        continue
                st['chk.arcs'] += 1
                if any(p[i + 1] not in arcs.get(p[i], ()) for i in range(len(p) - 1)):
                    st['FAIL.arcs'] += 1
                    continue
                flip(match, p)
            lvl_max = max(lvl_max, len(hubs))
        steps += lvl_max
    st['max_steps'] = max(st['max_steps'], steps)
    return match


def hopcroft_karp(V, E, side):
    A = [v for v in V if side[v] == 0]
    adj = {v: [] for v in V}
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    ma, INF = {}, 10 ** 9
    while True:
        dist, q = {}, collections.deque()
        for a in A:
            if a not in ma:
                dist[a] = 0
                q.append(a)
            else:
                dist[a] = INF
        found = INF
        while q:
            a = q.popleft()
            if dist[a] >= found:
                continue
            for b in adj[a]:
                c = ma.get(b)
                if c is None:
                    found = min(found, dist[a] + 1)
                elif dist.get(c, INF) == INF:
                    dist[c] = dist[a] + 1
                    q.append(c)
        if found == INF:
            break

        def dfs(a):
            for b in adj[a]:
                c = ma.get(b)
                if c is None or (dist.get(c, INF) == dist[a] + 1 and dfs(c)):
                    ma[a], ma[b] = b, a
                    return True
            dist[a] = INF
            return False

        for a in A:
            if a not in ma:
                dfs(a)
    return sum(1 for a in A if a in ma)


# ---------------------------------------------------------------- weighted
def hungarian_insert(h, cur, E, side, wt, match, y, st, wrong=None, iroot=None):
    """One step of the weighted insertion, with exact distances in reduced lengths."""
    sh = side[h]
    best = 0
    nb = collections.defaultdict(list)
    for u, v in E:
        if u in cur and v in cur:
            nb[u].append(v)
            nb[v].append(u)
    for b in nb[h]:
        best = max(best, wt[min(h, b), max(h, b)] - y[b])
    y[h] = best
    dist, par, pq = {h: 0}, {h: None}, [(0, h)]
    while pq:
        d, x = heapq.heappop(pq)
        if d > dist[x]:
            continue
        if side[x] == sh:
            for b in nb[x]:
                if match.get(x) == b:
                    continue
                l = y[x] + y[b] - wt[min(x, b), max(x, b)]
                st['chk.reduced_nonneg'] += 1
                if l < 0:
                    st['FAIL.reduced_nonneg'] += 1
                if d + l < dist.get(b, 10 ** 18):
                    dist[b], par[b] = d + l, x
                    heapq.heappush(pq, (d + l, b))
        elif x in match:
            a = match[x]
            if d < dist.get(a, 10 ** 18):
                dist[a], par[a] = d, x
                heapq.heappush(pq, (d, a))
    delta, z = None, None
    for x in sorted(dist):
        if side[x] == sh:
            val = dist[x] + y[x]
        elif x not in match:
            val = dist[x]
        else:
            continue
        if delta is None or val < delta:
            delta, z = val, x
    if wrong == 'nomin':
        delta = max(dist[x] for x in dist)
    y0 = dict(y)
    for x, d in dist.items():
        if d < delta:
            y[x] += (d - delta) if side[x] == sh else (delta - d)
    if wrong == 'stop_at_free':
        z = next((x for x in sorted(dist) if side[x] != sh and x not in match), z)
    if z == h:
        return
    if iroot is None:
        p = [z]
        while par[p[-1]] is not None:
            p.append(par[p[-1]])
        p.reverse()
    else:
        # as in the note: the Path Lemma on the tight arcs, no parent pointers
        tight = collections.defaultdict(list)
        for x, dx in dist.items():
            if side[x] == sh:
                for b in nb[x]:
                    if match.get(x) != b and b in dist and dist[b] == dx + y0[x] + y0[b] - wt[min(x, b), max(x, b)]:
                        tight[x].append(b)
            elif x in match and match[x] in dist and dist[match[x]] == dx:
                tight[x].append(match[x])
        p = path_lemma(iroot, tight, h, z, st, ties=st_rng(st))
        st['chk.weighted_simple'] += 1
        if len(set(p)) != len(p):
            st['FAIL.weighted_simple'] += 1
    # flip: every second edge starting at h becomes matched
    for i in range(0, len(p) - 1, 2):
        match[p[i]] = p[i + 1]
        match[p[i + 1]] = p[i]
    if len(p) % 2 == 1:
        match.pop(p[-1], None)
    st['weighted_flips'] += 1


def st_rng(st):
    return random.Random(st['requests'])


def check_duals(cur, E, side, wt, match, y, st):
    for u, v in E:
        if u in cur and v in cur:
            st['chk.dual_feasible'] += 1
            s = y[u] + y[v] - wt[min(u, v), max(u, v)]
            if s < 0:
                st['FAIL.dual_feasible'] += 1
            if match.get(u) == v:
                st['chk.tight'] += 1
                if s != 0:
                    st['FAIL.tight'] += 1
    for v in cur:
        st['chk.dual_nonneg'] += 1
        if y[v] < 0:
            st['FAIL.dual_nonneg'] += 1
        if v not in match and y[v] != 0:
            st['chk_free_zero_bad'] += 1
            st['FAIL.free_zero'] += 1


def max_weight(V, E, side, wt, rng, st, leaf=6, closure=False, wrong=None, inner_closure=False, via_lemma=True):
    root, _ = build(V, E, rng, leaf=leaf, closure=closure)
    match, y = {}, {v: 0 for v in V}
    for level in outer_order(root):
        for X in level:
            C = own_set(X)
            hubs = sorted(C & X.sep)
            cur = C - set(hubs)
            for h in hubs:
                cur.add(h)
                iroot = build(X.V, X.E, rng, leaf=leaf, closure=inner_closure)[0] if via_lemma and wrong is None else None
                hungarian_insert(h, cur, E, side, wt, match, y, st, wrong, iroot)
                check_duals(cur, E, side, wt, match, y, st)
    return match, y


def weight_of(match, wt):
    return sum(wt[min(a, b), max(a, b)] for a, b in match.items() if a < b)


def is_matching(match, E):
    es = {(min(u, v), max(u, v)) for u, v in E}
    for a, b in match.items():
        if match.get(b) != a or (min(a, b), max(a, b)) not in es:
            return False
    return True


def opt_weight_exact(V, E, side, wt):
    """Independent optimum: successive longest augmenting paths by Bellman-Ford on the full graph."""
    A = [v for v in V if side[v] == 0]
    adj = {v: [] for v in V}
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    match, total = {}, 0
    while True:
        INF = -10 ** 18
        dist = {a: 0 for a in A if a not in match}
        par = {a: None for a in dist}
        for _ in range(2 * len(V) + 2):
            ch = False
            for a in A:
                if a not in dist:
                    continue
                for b in adj[a]:
                    if match.get(a) == b:
                        continue
                    g = dist[a] + wt[min(a, b), max(a, b)]
                    if g > dist.get(b, INF):
                        dist[b], par[b] = g, a
                        ch = True
                        c = match.get(b)
                        if c is not None:
                            g2 = g - wt[min(b, c), max(b, c)]
                            if g2 > dist.get(c, INF):
                                dist[c], par[c] = g2, b
            if not ch:
                break
        best, bv = 0, None
        for b in V:
            if side[b] == 1 and b not in match and b in dist and dist[b] > best:
                best, bv = dist[b], b
        if bv is None:
            return total
        p = [bv]
        while par[p[-1]] is not None:
            p.append(par[p[-1]])
        p.reverse()
        for i in range(0, len(p) - 1, 2):
            match[p[i]] = p[i + 1]
            match[p[i + 1]] = p[i]
        total += best


def brute_weight(V, E, wt):
    es = sorted((min(u, v), max(u, v)) for u, v in E)
    best = [0]

    def rec(i, used, w):
        if w > best[0]:
            best[0] = w
        for j in range(i, len(es)):
            u, v = es[j]
            if u not in used and v not in used:
                rec(j + 1, used | {u, v}, w + wt[es[j]])

    rec(0, frozenset(), 0)
    return best[0]


def konig_check(V, E, side, match, st):
    """Vertex cover from the residual reach set of the free vertices of side 0."""
    arcs = collections.defaultdict(list)
    for u, v in E:
        a, b = (u, v) if side[u] == 0 else (v, u)
        if match.get(a) == b:
            arcs[b].append(a)
        else:
            arcs[a].append(b)
    Z = {v for v in V if side[v] == 0 and v not in match}
    st_ = list(Z)
    while st_:
        x = st_.pop()
        for y in arcs.get(x, ()):
            if y not in Z:
                Z.add(y)
                st_.append(y)
    cover = {v for v in V if (side[v] == 0) != (v in Z)}
    st['chk.konig_size'] += 1
    if len(cover) != len(match) // 2:
        st['FAIL.konig_size'] += 1
    st['chk.konig_cover'] += 1
    if any(u not in cover and v not in cover for u, v in E):
        st['FAIL.konig_cover'] += 1
    return arcs, Z


def multi_source_labels(root, V, arcs, sources, st):
    """Reach set of `sources` by the labels: a bag aggregates Out of the sources on it, and v reads
    In(v) against the aggregate along its chain. A source that is a hub of the bag counts itself."""
    def reach(Y, x, ad):
        seen, stk = {x}, [x]
        while stk:
            w = stk.pop()
            for z in ad.get(w, ()):
                if z in Y.V and z not in seen and (min(w, z), max(w, z)) in Y.eset:
                    seen.add(z)
                    stk.append(z)
        return seen

    rev = collections.defaultdict(list)
    for x, ys in arcs.items():
        for y in ys:
            rev[y].append(x)
    got = set(sources)
    stack = [root]
    while stack:
        Y = stack.pop()
        stack += Y.kids
        anc = Y.parent.splus if Y.parent else set()
        R = set()
        for a in sources:
            if a in Y.V and a not in anc:
                R |= reach(Y, a, arcs) & Y.sep
        st['max_aggregate_excess'] = max(st['max_aggregate_excess'], len(R) - len(Y.sep))
        for h in R:
            got |= {v for v in reach(Y, h, arcs) if v not in anc}
    return got
