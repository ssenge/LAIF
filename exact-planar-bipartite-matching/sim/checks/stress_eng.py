"""Independent engine for notes/GENERAL_DFS.md, written from the note, not from sim/gdfs.py.
All choices the note leaves open (F, separators, roots of Corollary 4, DFS of the small case, w in the link)
are made by an chooser with lookahead. Every lemma is checked in exact integer arithmetic."""
import collections, math, random, sys
import networkx as nx


def reach(out, srcs, allowed):
    seen = {s for s in srcs if s in allowed}
    st = list(seen)
    while st:
        u = st.pop()
        for v in out.get(u, ()):
            if v in allowed and v not in seen:
                seen.add(v)
                st.append(v)
    return seen


def sccs(out, allowed):
    index, low, on, stack, res = {}, {}, set(), [], []
    n = 0
    for r in allowed:
        if r in index:
            continue
        index[r] = low[r] = n
        n += 1
        stack.append(r)
        on.add(r)
        work = [(r, iter(out.get(r, ())))]
        while work:
            u, it = work[-1]
            adv = False
            for v in it:
                if v not in allowed:
                    continue
                if v not in index:
                    index[v] = low[v] = n
                    n += 1
                    stack.append(v)
                    on.add(v)
                    work.append((v, iter(out.get(v, ()))))
                    adv = True
                    break
                if v in on:
                    low[u] = min(low[u], index[v])
            if adv:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[u])
            if low[u] == index[u]:
                c = set()
                while True:
                    w = stack.pop()
                    on.discard(w)
                    c.add(w)
                    if w == u:
                        break
                res.append(c)
    return res


def conn_max(und, allowed):
    seen, best = set(), 0
    for s in allowed:
        if s in seen:
            continue
        seen.add(s)
        st, c = [s], 0
        while st:
            u = st.pop()
            c += 1
            for v in und.get(u, ()):
                if v in allowed and v not in seen:
                    seen.add(v)
                    st.append(v)
        best = max(best, c)
    return best


def rev_of(out):
    r = collections.defaultdict(set)
    for u, vs in out.items():
        for v in vs:
            r[v].add(u)
    return r


def und_of(out):
    r = collections.defaultdict(set)
    for u, vs in out.items():
        for v in vs:
            r[v].add(u)
            r[u].add(v)
    return r


def out_tree(x, K, out, rng, how=None):
    """A spanning out-tree of D[K] from x. Every spanning out-tree has positive probability under 'any'."""
    how = how or rng.choice(['bfs', 'dfs', 'any', 'any'])
    par, seen = {}, {x}
    if how == 'any':
        front = [(x, v) for v in out.get(x, ()) if v in K]
        while front:
            i = rng.randrange(len(front))
            front[i], front[-1] = front[-1], front[i]
            u, v = front.pop()
            if v not in seen:
                seen.add(v)
                par[v] = u
                front += [(v, w) for w in out.get(v, ()) if w in K and w not in seen]
    elif how == 'bfs':
        q = collections.deque([x])
        while q:
            u = q.popleft()
            vs = [v for v in out.get(u, ()) if v in K and v not in seen]
            rng.shuffle(vs)
            for v in vs:
                seen.add(v)
                par[v] = u
                q.append(v)
    else:
        st = [(x, None)]
        seen = set()
        while st:
            u, p = st.pop()
            if u in seen:
                continue
            seen.add(u)
            if p is not None:
                par[u] = p
            vs = [v for v in out.get(u, ()) if v in K and v not in seen]
            rng.shuffle(vs)
            st += [(v, u) for v in vs]
    return par


def root_path(par, w):
    p = [w]
    while p[-1] in par:
        p.append(par[p[-1]])
    return p[::-1]


def heavy(L, S, out, st):
    st['tests'] += 1
    for c in sccs(out, L - S):
        if 4 * len(c) > 3 * len(L):
            return c
    return None


def blink(lo, hi, bad):
    """least i in lo..hi with bad(i) False, bad monotone, bad(hi) False"""
    while lo < hi:
        m = (lo + hi) // 2
        if bad(m):
            lo = m + 1
        else:
            hi = m
    return lo


def trim(P, O, L, out, st):
    """note, Lemma 3, Trim. Returns segment, X at its last vertex, Y at its first vertex."""
    if not P or heavy(L, O, out, st) is None:
        return [], None, None
    s = len(P)
    i = blink(1, s, lambda i: heavy(L, O | set(P[:i]), out, st) is not None)
    X = heavy(L, O | set(P[:i - 1]), out, st)
    # greatest h in 1..i with no heavy after removing p_h..p_i
    h = i - blink(0, i - 1, lambda d: heavy(L, O | set(P[i - 1 - d:i]), out, st) is not None)
    Y = heavy(L, O | set(P[h:i]), out, st)
    if P[i - 1] not in X:
        st['FAIL.trim_X'] += 1
    if P[h - 1] not in Y:
        st['FAIL.trim_Y'] += 1
    return P[h - 1:i], X, Y


def linkpath(a, X, b, Y, out, rev, rng, st):
    both = X & Y
    if not both:
        st['FAIL.heavy_no_meet'] += 1
        return None
    w = rng.choice(sorted(both))
    first = root_path(out_tree(a, X, out, rng), w)
    second = root_path(out_tree(b, Y, rev, rng), w)[::-1]
    pos = {v: i for i, v in enumerate(second)}
    k = next(i for i, v in enumerate(first) if v in pos)
    q = first[:k] + second[pos[first[k]]:]
    if len(set(q)) != len(q) or q[0] != a or q[-1] != b or any(y not in out.get(x, ()) for x, y in zip(q, q[1:])):
        st['FAIL.link_not_path'] += 1
    return q


def lemma3(L, A, B, out, rev, rng, st):
    """Trim, Join, Close, from paths A and B with no heavy left. Returns a cycle as a list."""
    if heavy(L, set(A) | set(B), out, st) is not None:
        st['FAIL.lemma3_hyp'] += 1
        return None
    A1, X1, _ = trim(A, set(B), L, out, st)
    B1, _, Y2 = trim(B, set(A1), L, out, st)
    if not A1 and not B1:
        st['FAIL.both_dropped'] += 1
        return None
    if not A1:
        U = B1
    elif not B1:
        U = A1
    else:
        q = linkpath(A1[-1], X1, B1[0], Y2, out, rev, rng, st)
        if set(q[1:-1]) & (set(A1) | set(B1)):
            st['FAIL.join_inner_on_segments'] += 1
        U = A1 + q[1:-1] + B1
    if len(set(U)) != len(U) or any(y not in out.get(x, ()) for x, y in zip(U, U[1:])):
        st['FAIL.U_not_path'] += 1
    if heavy(L, set(U), out, st) is not None:
        st['FAIL.U_heavy_left'] += 1
    t = blink(1, len(U), lambda i: heavy(L, set(U[:i]), out, st) is not None)
    X = heavy(L, set(U[:t - 1]), out, st)
    d = blink(0, t - 1, lambda d: heavy(L, set(U[t - 1 - d:t]), out, st) is not None)
    s = t - d  # 1-based, u_s .. u_t
    if s == t:
        C = [U[t - 1]]
    else:
        Y = heavy(L, set(U[s:t]), out, st)
        if U[t - 1] not in X or U[s - 1] not in Y:
            st['FAIL.close_ends'] += 1
        q = linkpath(U[t - 1], X, U[s - 1], Y, out, rev, rng, st)
        if set(q[1:-1]) & set(U[s - 1:t]):
            st['FAIL.close_inner'] += 1
        C = U[s - 1:t] + q[1:-1]
    st['chk.cycle'] += 1
    if len(set(C)) != len(C) or not set(C) <= L:
        st['FAIL.C_not_simple'] += 1
    if len(C) > 1 and any(y not in out.get(x, ()) for x, y in zip(C, C[1:] + C[:1])):
        st['FAIL.C_not_cycle'] += 1
    if heavy(L, set(C), out, st) is not None:
        st['FAIL.C_heavy_left'] += 1
    return C


def dfs_post(r, L, out, rng):
    """A real search of D[L] from r with a random order at each vertex. Returns par, last-visit order."""
    par, post, seen = {}, [], {r}
    st = [(r, None)]
    order = {}

    def nbrs(u):
        vs = [v for v in out.get(u, ()) if v in L]
        rng.shuffle(vs)
        return iter(vs)
    st = [(r, nbrs(r))]
    while st:
        u, it = st[-1]
        for v in it:
            if v not in seen:
                seen.add(v)
                par[v] = u
                st.append((v, nbrs(v)))
                break
        else:
            st.pop()
            post.append(u)
    return par, post


def cor4_options(L, out, rev, und, rng, st, tries, script=None):
    """Yields candidate cycles of Corollary 4 under different chooser choices."""
    Ls = sorted(L)
    if len(L) == 1:
        yield [Ls[0]]
        return
    n_ok = 0
    if script:
        for r, par, u, v in script(L):
            pu, pv = root_path(par, u), root_path(par, v)
            common = [a for a, b in zip(pu, pv) if a == b]
            P = (set(pu) ^ set(pv)) | {common[-1]}
            if len(L) >= 12 and 4 * conn_max(und, L - P) > 3 * len(L):
                st['script_l_invalid'] += 1
                continue
            yield lemma3(L, pu, [w for w in pv if w not in set(pu)], out, rev, rng, st)
    for _ in range(tries):
        r = rng.choice(Ls)
        if len(L) < 12:
            par, post = dfs_post(r, L, out, rng)
            m = post[(len(post) - 1) // 2]
            U = root_path(par, m)
            # note: leaves no strong component of more than half
            for c in sccs(out, L - set(U)):
                if 2 * len(c) > len(L):
                    st['FAIL.kao_median'] += 1
            yield lemma3(L, U, [], out, rev, rng, st)
            continue
        par = out_tree(r, L, out, rng)
        verts = Ls
        for _2 in range(40):
            u, v = rng.choice(verts), rng.choice(verts)
            pu, pv = root_path(par, u), root_path(par, v)
            su = set(pu)
            common = [a for a, b in zip(pu, pv) if a == b]
            P = (su ^ set(pv)) | {common[-1]}
            if 4 * conn_max(und, L - P) <= 3 * len(L):
                n_ok += 1
                k = len(common)
                A = pu[k - 1:]          # with the ancestor
                B = pv[k:]              # without it
                yield lemma3(L, A, B, out, rev, rng, st)
                break


def classes(Q, R, out):
    """Split Lemma from its definition."""
    rest = Q - set(R)
    k = len(R) - 1
    key, tail = {}, {}
    for i, v in enumerate(R):
        for z in out.get(v, ()):
            if z in rest:
                kz = (k - i, z)
                if z not in key or kz < key[z]:
                    key[z], tail[z] = kz, v
    e, left = {}, set(rest)
    groups = {}
    for z in sorted(key, key=key.get):
        if z in left:
            g = reach(out, [z], left)
            left -= g
            groups[z] = g
    return groups, key, tail, left


def small_solve(x, K, out, kids, rng):
    seen = {x}
    st = [x]

    def nbrs(u):
        vs = [v for v in out.get(u, ()) if v in K]
        rng.shuffle(vs)
        return iter(vs)
    stack = [(x, nbrs(x))]
    kids[x] = []
    while stack:
        u, it = stack[-1]
        for v in it:
            if v not in seen:
                seen.add(v)
                kids[u].append(v)
                kids[v] = []
                stack.append((v, nbrs(v)))
                break
        else:
            stack.pop()


class Adv:
    """k1 trees and separators per pass, k2 cycles per component. Lookahead: largest top component of the next bad class."""

    def __init__(self, k1=4, k2=3, prefer_step4=True, script_q=None, script_l=None, check_every=1.0):
        self.k1, self.k2, self.prefer_step4 = k1, k2, prefer_step4
        self.script_q, self.script_l = script_q, script_l
        self.check_every = check_every


def q_options(z, Q, W, out, und, rng, st, adv, f):
    """spanning out-trees and pairs with the note's separator condition, with the ends and mids computed"""
    res = []
    if adv.script_q:
        for par, u, v in adv.script_q(z, Q):
            pu, pv = root_path(par, u), root_path(par, v)
            if 4 * conn_max(und, Q - set(pu) - set(pv)) <= 3 * len(Q):
                res.append((par, pu, pv))
            else:
                st['script_q_invalid'] += 1
        if res:
            return res
    verts = sorted(Q)
    for _ in range(adv.k1):
        par = out_tree(z, Q, out, rng)
        leaves = sorted(set(verts) - set(par.values()))
        got = 0
        for _2 in range(200):
            pool = leaves if rng.random() < .5 else verts
            u, v = rng.choice(pool), rng.choice(pool)
            pu, pv = root_path(par, u), root_path(par, v)
            if 4 * conn_max(und, Q - set(pu) - set(pv)) <= 3 * len(Q):
                res.append((par, pu, pv))
                got += 1
                if got >= 3:
                    break
    return res


def analyze(pu, pv, W, f):
    ends = []
    mids = []
    for p in (pu, pv):
        if 8 * f(p[0]) <= 7 * W:
            return None
        i = 0
        while i + 1 < len(p) and 8 * f(p[i + 1]) > 7 * W:
            i += 1
        ends.append(p[i])
        if i + 1 < len(p) and 16 * f(p[i + 1]) >= W:
            mids.append(p[:i + 2])
    return ends, mids


def check_l1(R, Q, groups, tail, out, st):
    m = R[-1]
    M = next(c for c in sccs(out, Q) if m in c)
    rm = reach(out, [m], Q)
    for y, Ky in groups.items():
        st['chk.l1'] += 1
        if tail[y] in M:
            if not Ky <= rm:
                st['FAIL.l1a'] += 1
        elif Ky & rm:
            st['FAIL.l1b'] += 1


def one_pass(z, Q, W, out, rev, und, kids, rng, st, adv, prevL, log):
    fc = {}

    def f(v):
        if v not in fc:
            st['reach'] += 1
            fc[v] = len(reach(out, [v], Q))
        return fc[v]
    opts = q_options(z, Q, W, out, und, rng, st, adv, f)
    if not opts:
        st['no_separator_found'] += 1
        return None
    best = None
    scc_q = sccs(out, Q)
    comp = {}
    for c in scc_q:
        for v in c:
            comp[v] = c
    stepped3 = []
    for par, pu, pv in opts:
        an = analyze(pu, pv, W, f)
        if an is None:
            st['FAIL.root_not_high'] += 1
            continue
        ends, mids = an
        if mids:
            stepped3.append((par, mids[0]))
            continue
        a, b = ends
        ra = reach(out, [a], Q)
        rb = reach(out, [b], Q)
        pick = b if (b in ra and a not in rb) else a
        L = comp[pick]
        # Lemma 2, full check
        st['chk.l2'] += 1
        if 8 * f(pick) <= 7 * W:
            st['FAIL.l2_no_high'] += 1
        below = reach(out, list(L), Q) - L
        items = sorted(below)
        if rng.random() > adv.check_every:
            items = rng.sample(items, min(40, len(items)))
        for y in items:
            st['max.l2_below_f_x1000'] = max(st['max.l2_below_f_x1000'], 1000 * f(y) // W)
            if 8 * f(y) > 7 * W:
                st['FAIL.l2_high_below'] += 1
                log.append(('l2', z, sorted(Q), W, pu, pv, sorted(L), y))
        for C in cor4_options(L, out, rev, und, rng, st, adv.k2, adv.script_l):
            if C is None:
                continue
            depth = lambda v: len(root_path(par, v))
            c = min(C, key=depth)
            k = C.index(c)
            R = root_path(par, c) + C[k + 1:] + C[:k]
            groups, key, tail, left = classes(Q, R, out)
            bad = [y for y, g in groups.items() if 16 * len(g) > 15 * W]
            score = (0, 0)
            if bad:
                g = groups[bad[0]]
                hi = 0
                for s in sccs(out, g):
                    v = next(iter(s))
                    if 8 * len(reach(out, [v], g)) > 7 * W:
                        hi = max(hi, len(s))
                score = (1, hi)
            if best is None or score > best[0]:
                best = (score, par, pu, pv, L, C, R, groups, key, tail, left)
    if best is None and not stepped3:
        st['no_option'] += 1
        return None
    if best is None or (not adv.prefer_step4 and stepped3 and rng.random() < .5):
        par, pth = rng.choice(stepped3)
        R = pth
        groups, key, tail, left = classes(Q, R, out)
        kind, L, C = 3, None, None
        st['n.step3'] += 1
        m = R[-1]
        if not (16 * f(m) >= W and 8 * f(m) <= 7 * W):
            st['FAIL.step3_not_mid'] += 1
    else:
        _, par, pu, pv, L, C, R, groups, key, tail, left = best
        kind = 4
        st['n.step4'] += 1
    # common checks
    if left:
        st['FAIL.split_cover'] += 1
    if len(set(R)) != len(R) or R[0] != z or any(y not in out.get(x, ()) for x, y in zip(R, R[1:])):
        st['FAIL.R_not_path'] += 1
    check_l1(R, Q, groups, tail, out, st)
    for y, g in groups.items():
        if reach(out, [y], g) != g:
            st['FAIL.class_not_reached'] += 1
    bad = [y for y, g in groups.items() if 16 * len(g) > 15 * W]
    if len(bad) > 1:
        st['FAIL.two_bad'] += 1
    if kind == 3 and bad:
        st['FAIL.l5a'] += 1
    if kind == 4 and bad:
        g = groups[bad[0]]
        st['chk.l5b'] += 1
        if tail[bad[0]] not in L:
            st['FAIL.l5b_tail'] += 1
        rest = L - set(C)
        for s in sccs(out, g):
            v = next(iter(s))
            if 8 * len(reach(out, [v], g)) > 7 * W:
                st['chk.l5b_comp'] += 1
                if not s <= rest:
                    st['FAIL.l5b_not_in_L_minus_C'] += 1
                if 4 * len(s) > 3 * len(L):
                    st['FAIL.l5b_too_big'] += 1
    if kind == 4 and prevL is not None:
        st['chk.l6_shrink'] += 1
        st['max.L_ratio_x1000'] = max(st['max.L_ratio_x1000'], 1000 * len(L) // prevL)
        if 4 * len(L) > 3 * prevL:
            st['FAIL.l6_shrink'] += 1
    # the tree
    heads = collections.defaultdict(list)
    for y in sorted(groups, key=key.get):
        heads[tail[y]].append(y)
    for i, v in enumerate(R):
        kids[v] = ([R[i + 1]] if i + 1 < len(R) else []) + heads[v]
    if log is not None:
        log.append(('pass', kind, len(Q), W, len(L) if L else None, len(C) if C else None, len(R), max(len(g) for g in groups.values()) if groups else 0))
    return groups, (len(L) if L else None)


def solve(out, roots, rng, st, adv, SMALL=12, log=None, maxlevels=10 ** 9):
    rev = rev_of(out)
    und = und_of(out)
    V = set(out) | set(rev) | set(roots)
    kids = {}
    # forest: virtual vertex, keys by root order
    left, probs, tops = set(V), [], []
    for r in roots:
        if r in left:
            g = reach(out, [r], left)
            left -= g
            probs.append((r, g))
            tops.append(r)
    allv = V - left
    n = len(V)
    bound = math.log(max(n, 2), 4 / 3) + 2
    level = 0
    while probs and level < maxlevels:
        new, worst = [], 0
        for x, K in probs:
            if len(K) < SMALL:
                small_solve(x, K, out, kids, rng)
                continue
            W = len(K)
            cur = {x: K}
            passes, prevL = 0, None
            chain = 0
            while True:
                bad = [y for y, g in cur.items() if 16 * len(g) > 15 * W]
                if not bad:
                    break
                y = bad[0]
                Q = cur.pop(y)
                res = one_pass(y, Q, W, out, rev, und, kids, rng, st, adv, prevL, log if log is not None else [])
                if res is None:
                    return None
                groups, prevL = res
                cur.update(groups)
                passes += 1
                if prevL is not None:
                    chain += 1
                if passes > bound:
                    st['FAIL.l6_passes'] += 1
                if passes > 4 * n:
                    st['FAIL.no_termination'] += 1
                    return None
            worst = max(worst, passes)
            st['max.step4_chain'] = max(st['max.step4_chain'], chain)
            st['hist.passes.%02d' % passes] += 1
            for y, g in cur.items():
                if 16 * len(g) > 15 * len(K):
                    st['FAIL.l6_size'] += 1
                new.append((y, g))
        st['max.passes_per_level'] = max(st['max.passes_per_level'], worst)
        st['n.global_passes'] += worst
        probs = new
        level += 1
    st['max.levels'] = max(st['max.levels'], level)
    return tops, kids, allv


def replay(tops, kids, allv, out, st):
    """A real depth-first search with the children of the tree, and the right-of test from the numbers."""
    st['chk.replay'] += 1
    seen, pre, post = set(), {}, {}
    a, b = 0, 0
    bad = 0
    for r in tops:
        if r in seen:
            bad += 1
            continue
        seen.add(r)
        pre[r] = a
        a += 1
        st_ = [(r, iter(kids.get(r, ())))]
        while st_:
            x, it = st_[-1]
            c = next(it, None)
            if c is None:
                st_.pop()
                post[x] = b
                b += 1
                for v in out.get(x, ()):
                    if v not in seen:
                        bad += 1
            elif c in seen or c not in out.get(x, ()):
                bad += 1
            else:
                seen.add(c)
                pre[c] = a
                a += 1
                st_.append((c, iter(kids.get(c, ()))))
    if seen != allv:
        bad += 1
    if not bad:
        for u in allv:
            for v in out.get(u, ()):
                if pre[v] > pre[u] and post[v] > post[u]:
                    bad += 1
    if bad:
        st['FAIL.replay'] += 1
    return bad == 0


def planar_ok(out):
    U = nx.Graph()
    U.add_nodes_from(out)
    for u, vs in out.items():
        for v in vs:
            U.add_edge(u, v)
    return nx.check_planarity(U)[0]


# ---------------------------------------------------------------- the ear book
def ears(n):
    """Chain c_0 -> ... -> c_{T-1} -> h. Ear E_{j+1} from h back to c_j with about a quarter of the current component."""
    out = collections.defaultdict(set)
    L = n
    sizes = []
    while L > 1:
        e = max(0, math.ceil(L / 4) - 1)
        sizes.append(e)
        L = L - 1 - e
    T = len(sizes)
    chain = list(range(T))
    h = T
    nxt = T + 1
    for a, b in zip(chain + [], chain[1:] + [h]):
        out[a].add(b)
    for j, e in enumerate(sizes):
        ear = list(range(nxt, nxt + e))
        nxt += e
        path = [h] + ear + [chain[j]]
        for a, b in zip(path, path[1:]):
            out[a].add(b)
    out[h]
    return {u: set(vs) for u, vs in out.items()}, chain, h, sizes


def ears_scripts(chain, h, out):
    cs = set(chain)

    def script_q(z, Q):
        # the unique out-tree from the first live chain vertex, with the separator chain + h
        par = out_tree(z, Q, out, random.Random(1), 'bfs')
        yield par, z, h

    def script_l(L):
        r = min(v for v in L if v in cs) if any(v in cs for v in L) else h
        par = out_tree(r, L, out, random.Random(2), 'bfs')
        yield r, par, h, r
    return script_q, script_l
