"""Who knows what, Section 5 of notes/DOMINATORS.md: an engine where vertices hold local memory and the only ways to
communicate are (P) on checked connected vertex-disjoint parts, one-round exchanges along arcs, and a Multi-Source black box.
Shares no code with sim/. Paths are chosen by the test (General Search is a black box); positions are given (T2 black box).
Several problems run in one global sequence of operations. Values carry at most WORDS integers.
python who.py SEED SECS [big]   |  python who.py scale  |  python who.py ctl SEED SECS
"""
import collections, json, math, random, sys, time

WORDS = 6
CTL = None
STAT = collections.Counter()


class RouteClash(Exception):
    pass


class Net:
    def __init__(self, arcs, V):
        self.V = set(V)
        self.out = {v: set(arcs.get(v, ())) & self.V for v in self.V}
        self.inn = {v: set() for v in self.V}
        self.und = {v: set() for v in self.V}
        for u in self.V:
            for v in self.out[u]:
                self.inn[v].add(u)
                self.und[u].add(v)
                self.und[v].add(u)
        self.cP = self.cX = self.cMS = 0
        self.mem = {v: {} for v in self.V}

    def P(self, part, inp, op):
        """(P). part: vertex -> part id. inp: vertex -> value. Everyone in a part gets the aggregate of its part."""
        self.cP += 1
        groups = collections.defaultdict(list)
        for v, pid in part.items():
            groups[pid].append(v)
        for pid, vs in groups.items():
            vset, seen, st = set(vs), {vs[0]}, [vs[0]]
            while st:
                u = st.pop()
                for w in self.und[u]:
                    if w in vset and w not in seen:
                        seen.add(w)
                        st.append(w)
            if seen != vset:
                raise AssertionError('part not connected %r' % (pid,))
        agg = {}
        for v, val in inp.items():
            if v not in part:
                raise AssertionError('input outside the parts')
            w = len(val) if isinstance(val, tuple) else 1
            if w > WORDS:
                raise AssertionError('value too long')
            pid = part[v]
            agg[pid] = val if pid not in agg else op(agg[pid], val)
        return {v: agg[pid] for v, pid in part.items() if pid in agg}

    def ms(self, sources, keep):
        """Multi-Source black box: reachable from sources along arcs (u,v) with keep(u,v), decided locally at u and v."""
        self.cMS += 1
        seen, st = set(sources), list(sources)
        while st:
            u = st.pop()
            for v in self.out[u]:
                if v not in seen and keep(u, v):
                    seen.add(v)
                    st.append(v)
        return seen


def one(a, b):
    raise RouteClash('two values in one piece')


def mkpart(pairs):
    part = {}
    for v, pid in pairs:
        if v in part:
            raise AssertionError('parts not vertex-disjoint')
        part[v] = pid
    return part


def bit_search(net, O, headkey, B):
    pre = {y: 0 for y in O}
    mem = net.mem
    for i in range(B - 1, -1, -1):
        src = [z for z, c in headkey.items() if c >> (i + 1) == pre[z] and not (c >> i) & 1]
        got = net.ms(src, lambda u, v: u in pre and v in pre and pre[u] == pre[v] and mem[u]['prob'] == mem[v]['prob'])
        for y in O:
            pre[y] = 2 * pre[y] + (0 if y in got else 1)
    return pre


def geom(mem_v, lev):
    """Segment data a vertex of R computes from its position and k."""
    t, k = mem_v['pos'], mem_v['k']
    code = t - 1
    seg = code >> (lev + 1)
    side = (code >> lev) & 1
    l = (seg << (lev + 1)) + 1
    c = l + (1 << lev) - 1
    r = min(k, l + (1 << (lev + 1)) - 1)
    return seg, side, l, c, r, c + 1 <= k


def sweep(net, members, tagf, lev, values, op, direction):
    """members: vertices of R in Z or Y of their segments at this level. tagf(v) names the subpath. Values strictly before
    or after each vertex in its subpath, by dyadic pieces, one (P) per sublevel."""
    mem = net.mem
    res = {}
    for s in range(lev):
        part, inp = {}, {}
        for v in members:
            code = mem[v]['pos'] - 1
            part[v] = (tagf(v), code >> (s + 1))
            child = (code >> s) & 1
            if v in values and ((direction == 'before' and child == 0) or (direction == 'after' and child == 1)):
                inp[v] = values[v]
        got = net.P(part, inp, op)
        for v, val in got.items():
            code = mem[v]['pos'] - 1
            child = (code >> s) & 1
            if (direction == 'before' and child == 1) or (direction == 'after' and child == 0):
                res[v] = val if v not in res else op(res[v], val)
    return res


def tmin(a, b):
    return a if a[0] <= b[0] else b


def tmax(a, b):
    return a if a[0] >= b[0] else b


def one_pass(net, probs, n):
    """probs: list of dict(id, Q, E, R). All at once. Writes rec into mem and returns the new classes."""
    mem = net.mem
    Oall = []
    for P in probs:
        k = len(P['R'])
        for v in P['Q']:
            mem[v].update(prob=P['id'], pos=0, k=k, ent=v in P['E'])
        for i, v in enumerate(P['R'], 1):
            mem[v]['pos'] = i
        Oall += [v for v in P['Q'] if mem[v]['pos'] == 0]
    # one exchange: neighbours learn prob and pos
    net.cX += 1
    same = lambda u, v: mem[u].get('prob') == mem[v].get('prob') and 'prob' in mem[u] and 'prob' in mem[v]
    # ---- Step 1
    base = n + 2
    keyb, keya = {}, {}
    for y in Oall:
        inR = [mem[u]['pos'] for u in net.inn[y] if same(u, y) and mem[u]['pos']]
        if inR:
            keyb[y] = (mem[y]['k'] - max(inR)) * base + y
        least = 0 if mem[y]['ent'] else (min(inR) if inR else None)
        if least is not None:
            keya[y] = least * base + y
    B = math.ceil(math.log2((n + 2) * base + 1)) + 1
    eb = bit_search(net, Oall, keyb, B)
    ea = bit_search(net, Oall, keya, B)
    for y in Oall:
        mem[y]['b'] = mem[y]['k'] - eb[y] // base
        mem[y]['a'] = ea[y] // base
        mem[y]['e'] = eb[y]
        if CTL == 'bflip':
            mem[y]['b'] = mem[y]['a']
    # parts A_a and B_b
    Rall = [v for P in probs for v in P['R']]
    A_part = mkpart([(v, (mem[v]['prob'], 'A', mem[v]['pos'])) for v in Rall] + [(y, (mem[y]['prob'], 'A', mem[y]['a'])) for y in Oall if mem[y]['a'] >= 1])
    B_part = mkpart([(v, (mem[v]['prob'], 'B', mem[v]['pos'])) for v in Rall] + [(y, (mem[y]['prob'], 'B', mem[y]['b'])) for y in Oall])
    # ---- exchange: p_t computes A(t), B(t) from a(u), b(u) and positions of in-neighbours, all unfiltered off R
    net.cX += 1
    INF = 10 ** 9
    for v in Rall:
        t = mem[v]['pos']
        A, B2 = INF, -INF
        if t >= 2:
            if mem[v]['ent']:
                A, B2 = 0, 0
            for u in net.inn[v]:
                if not same(u, v):
                    continue
                if mem[u]['pos']:
                    i = mem[u]['pos']
                    if i != t and i != t - 1:
                        A, B2 = min(A, i), max(B2, i)
                else:
                    A, B2 = min(A, mem[u]['a']), max(B2, mem[u]['b'])
        mem[v]['A'], mem[v]['B'] = A, B2
        mem[v]['m'] = t + 1
    Lmax = 0
    while (1 << Lmax) < max((mem[v]['k'] for v in Rall), default=1):
        Lmax += 1
    # ---- Step 2
    for lev in range(Lmax):
        Z, Y, S_part = [], [], {}
        for v in Rall:
            seg, side, l, c, r, ok = geom(mem[v], lev)
            if not ok:
                continue
            S_part[v] = (mem[v]['prob'], lev, seg)
            (Y if side else Z).append(v)
        tagY = lambda v: (mem[v]['prob'], geom(mem[v], lev)[0], 'Y')
        tagZ = lambda v: (mem[v]['prob'], geom(mem[v], lev)[0], 'Z')
        pb = sweep(net, Y, tagY, lev, {v: mem[v]['B'] for v in Y}, max, 'before')
        good = {}
        for v in Y:
            seg, side, l, c, r, ok = geom(mem[v], lev)
            t = mem[v]['pos']
            good[v] = t >= c + 2 and pb.get(v, -INF) < t
            if CTL == 'nogood':
                good[v] = t >= c + 2
        lg = sweep(net, Y, tagY, lev, {v: mem[v]['pos'] for v in Y if good[v]}, max, 'before')
        g = {}
        for v in Y:
            g[v] = mem[v]['pos'] if good[v] else lg.get(v)
        # over S: max B, last good, first with A < l
        allB = net.P(S_part, {v: mem[v]['B'] for v in Y}, max)
        lastg = net.P(S_part, {v: mem[v]['pos'] for v in Y if good[v]}, max)
        tci = net.P(S_part, {v: (mem[v]['pos'], g[v] if g[v] is not None else -1) for v in Y if mem[v]['A'] < geom(mem[v], lev)[2]}, tmin)
        # leaves send to A_a, one exchange then one (P)
        net.cX += 1
        inp = {}
        for v in Y:
            seg, side, l, c, r, ok = geom(mem[v], lev)
            a = mem[v]['A']
            if l <= a <= c:
                nb = [u for u in net.inn[v] if same(u, v) and A_part.get(u) == (mem[v]['prob'], 'A', a)]
                if not nb:
                    raise AssertionError('leaf with no neighbour in A_a')
                u = nb[0]
                val = (mem[v]['pos'], g[v] if g[v] is not None else -1)
                inp[u] = val if u not in inp else tmin(inp[u], val)
        got = net.P(A_part, inp, tmin)
        first = {}
        for v in Z:
            if v in got:
                first[v] = got[v]
        # X(j)
        before = sweep(net, Z, tagZ, lev, first, tmin, 'before')
        sa = sweep(net, Z, tagZ, lev, {v: mem[v]['A'] for v in Z}, min, 'after')
        sb = sweep(net, Z, tagZ, lev, {v: mem[v]['B'] for v in Z}, max, 'after')
        for v in Z:
            seg, side, l, c, r, ok = geom(mem[v], lev)
            gr1 = (r + 1) if allB.get(v, -INF) < r + 1 else lastg.get(v)
            if CTL == 'nogood':
                gr1 = r + 1
            cand = [(r + 1, gr1 if gr1 is not None else -1)]
            if v in tci:
                cand.append(tci[v])
            if v in before:
                cand.append(before[v])
            X, gX = min(cand, key=lambda q: q[0])
            mem[v].setdefault('X', {})[lev] = X
            j = mem[v]['pos']
            if gX != -1 and sa.get(v, INF) >= j and sb.get(v, -INF) < gX:
                if CTL != 'firstcand' or mem[v]['m'] == j + 1:
                    mem[v]['m'] = max(mem[v]['m'], gX)
            mem[v].setdefault('first', {})[lev] = first.get(v)
        for v in Y:
            mem[v].setdefault('g', {})[lev] = g[v]
    # ---- Step 3
    for lev in range(Lmax):
        Z, Y, S_part = [], [], {}
        for v in Rall:
            seg, side, l, c, r, ok = geom(mem[v], lev)
            if not ok:
                continue
            S_part[v] = (mem[v]['prob'], lev, seg)
            (Y if side else Z).append(v)
        tagY = lambda v: (mem[v]['prob'], geom(mem[v], lev)[0], 'Y')
        tagZ = lambda v: (mem[v]['prob'], geom(mem[v], lev)[0], 'Z')
        ismem = {v: mem[v]['m'] > geom(mem[v], lev)[3] + 1 for v in Z}
        token = {v: (mem[v]['pos'], v) for v in Z if ismem[v]}   # position and identifier
        lb = sweep(net, Z, tagZ, lev, token, tmax, 'before')
        la = sweep(net, Z, tagZ, lev, token, tmin, 'after')
        for v in Z:
            mem[v].setdefault('lam', {})[lev] = token.get(v) or lb.get(v)
        # parts between consecutive members
        part1 = {v: (mem[v]['prob'], lev, geom(mem[v], lev)[0], la[v][0] if v in la else -1) for v in Z}
        # the member after tells its predecessor on R in one exchange, which injects
        net.cX += 1
        succ_inp = {}
        by_pos = {(mem[v]['prob'], mem[v]['pos']): v for v in Z}
        for v in Z:
            if ismem[v]:
                pred = by_pos.get((mem[v]['prob'], mem[v]['pos'] - 1))
                if pred is not None and pred in part1 and part1[pred][2] == part1[v][2]:
                    if pred not in net.inn[v]:
                        raise AssertionError('R is not a path')
                    succ_inp[pred] = (mem[v]['m'], mem[v]['X'][lev])
        nx = net.P(part1, succ_inp, one)
        # member's own m for the vertices after it, up to the next member
        cur_inp = {v: (mem[v]['m'], mem[v]['pos'], v) for v in Z if ismem[v]}
        here = net.P({v: part1[v] for v in Z if mem[v]['lam'][lev] is not None}, {v: val for v, val in cur_inp.items()}, one)
        # rings
        inp = {}
        sent = 0
        for v in Z:
            seg, side, l, c, r, ok = geom(mem[v], lev)
            if v in here and v in nx and mem[v]['first'][lev] is not None:
                mi, ji, idi = here[v]
                mn, Xn = nx[v]
                ta = mem[v]['first'][lev][0]
                if mn < mi <= r and ta == Xn:
                    inp[v] = (ta, ji, idi)
                    sent += 1
        got = net.P(A_part, inp, one)
        net.cX += 1
        marks = {}   # leaf -> (position, j, id)
        for v in Y:
            seg, side, l, c, r, ok = geom(mem[v], lev)
            a = mem[v]['A']
            if l <= a <= c:
                nb = [u for u in net.inn[v] if same(u, v) and A_part.get(u) == (mem[v]['prob'], 'A', a) and u in got]
                if nb and got[nb[0]][0] == mem[v]['pos']:
                    ta, ji, idi = got[nb[0]]
                    pos = mem[v]['g'][lev]
                    if CTL == 'nog_mark':
                        pos = mem[v]['pos']
                    marks[v] = (pos, ji, idi)
                    STAT['ring_marks'] += 1
                    if pos != mem[v]['pos']:
                        STAT['ring_routes_nonzero'] += 1
        placed = {}
        for v, (pos, ji, idi) in marks.items():
            if pos == mem[v]['pos']:
                placed[v] = (pos, ji, idi)
        # routes by dyadic pieces of Y, at most one per piece by the disjointness claim
        for s in range(lev):
            part, inp2 = {}, {}
            for v in Y:
                code = mem[v]['pos'] - 1
                part[v] = (tagY(v), code >> (s + 1))
            for v, (pos, ji, idi) in marks.items():
                code, pc = mem[v]['pos'] - 1, pos - 1
                if pc < code and (code >> (s + 1)) == (pc >> (s + 1)) and (code >> s) & 1 and not (pc >> s) & 1:
                    inp2[v] = (pos, ji, idi)
            got2 = net.P(part, inp2, one)
            for v, (pos, ji, idi) in got2.items():
                if mem[v]['pos'] == pos:
                    if v in placed:
                        raise AssertionError('two marks')
                    placed[v] = (pos, ji, idi)
        # the rest: J, then j+, by aggregates over S
        Jv = net.P(S_part, {v: (mem[v]['pos'], v) for v in Z if ismem[v] and mem[v]['m'] > geom(mem[v], lev)[4]}, tmax)
        plus = net.P(S_part, {v: (mem[v]['pos'], mem[v]['m']) for v in Z if ismem[v] and (v not in Jv or mem[v]['pos'] > Jv[v][0])}, tmin)
        lastm = net.P(S_part, {v: (mem[v]['pos'], v) for v in Z if ismem[v]}, tmax)
        for v in Y:
            seg, side, l, c, r, ok = geom(mem[v], lev)
            if v in plus and CTL != 'norest':
                jp, mp = plus[v]
                if mp <= r and mem[v]['pos'] == mp:
                    if v in placed:
                        raise AssertionError('two marks, rest')
                    placed[v] = (mp, Jv[v][0], Jv[v][1]) if v in Jv else (mp, -1, -1)
                    STAT['rest_marks'] += 1
        # delta
        bm = sweep(net, Y, tagY, lev, placed, tmax, 'before')
        for v in Y:
            m_ = placed.get(v) or bm.get(v)
            if m_ is not None:
                d = None if m_[1] == -1 else (m_[1], m_[2])
            else:
                d = lastm.get(v)
                if d is not None:
                    d = (d[0], d[1])
            mem[v].setdefault('dlt', {})[lev] = d
    # ---- Step 4
    for v in Rall:
        ds = mem[v].get('dlt', {})
        d = None
        for lev in range(Lmax):
            if ds.get(lev) is not None:
                d = ds[lev]
                break
        mem[v]['last'] = d[1] if d else None
    # O(log n) broadcasts over A_a and B_b, one per entry of a label
    for lev in range(Lmax):
        ga = net.P(A_part, {v: mem[v]['lam'][lev] for v in Rall if mem[v].get('lam', {}).get(lev) is not None}, one)
        gb = net.P(B_part, {v: mem[v]['dlt'][lev] for v in Rall if mem[v].get('dlt', {}).get(lev) is not None}, one)
        for y in Oall:
            if y in ga:
                mem[y].setdefault('lamy', {})[lev] = ga[y]
            if y in gb:
                mem[y].setdefault('dlty', {})[lev] = gb[y]
    ida = net.P(A_part, {v: v for v in Rall}, one)   # identifier of p_a
    for y in Oall:
        a, b = mem[y]['a'], mem[y]['b']
        d = None
        if a == 0:
            d = None
        elif a == b:
            d = ida[y]
        else:
            lev = ((a - 1) ^ (b - 1)).bit_length() - 1
            x, z = mem[y].get('lamy', {}).get(lev), mem[y].get('dlty', {}).get(lev)
            if x is not None and z is not None:
                d = tmin(x, z)[1]
            else:
                for l2 in range(lev + 1, Lmax):
                    z2 = mem[y].get('dlty', {}).get(l2)
                    if z2 is not None:
                        d = z2[1]
                        break
        mem[y]['last'] = d
    for v in Rall + Oall:
        if mem[v].get('last') is not None:
            mem[v]['rec'] = mem[v]['last']
    # new classes and entries: one exchange
    net.cX += 1
    out = []
    groups = collections.defaultdict(set)
    for y in Oall:
        groups[(mem[y]['prob'], mem[y]['e'])].add(y)
    for key, K in groups.items():
        head = [y for y in K if keyb.get(y) == key[1]]
        assert len(head) == 1
        E = {y for y in K if mem[y]['ent'] or any(same(u, y) and (u not in K) for u in net.inn[y])}
        out.append(dict(Q=K, E=E, root=head[0], parent=key))
    for v in Rall + Oall:
        for f in ('X', 'first', 'g', 'lam', 'dlt', 'lamy', 'dlty', 'm', 'A', 'B', 'a', 'b', 'e', 'last'):
            mem[v].pop(f, None)
        # R is done
    for v in Rall:
        mem[v].pop('prob', None)
    for y in Oall:
        mem[y].pop('prob', None)
    return out


def brute_last(arcs, E, Q):
    """Last dominator in the flow graph, by removal."""
    def reach(ban):
        seen = {e for e in E if e != ban and e in Q}
        st = list(seen)
        while st:
            u = st.pop()
            for v in arcs.get(u, ()):
                if v in Q and v != ban and v not in seen:
                    seen.add(v)
                    st.append(v)
        return seen
    dom = {y: set() for y in Q}
    for w in Q:
        got = reach(w)
        for y in Q - got - {w}:
            dom[y].add(w)
    return {y: (max(dom[y], key=lambda p: len(dom[p])) if dom[y] else None) for y in Q}


def rand_path(arcs, Q, z, rng, stop):
    R, seen, cur = [z], {z}, z
    while rng.random() >= stop:
        opts = [v for v in arcs.get(cur, ()) if v in Q and v not in seen]
        if not opts:
            break
        cur = rng.choice(opts)
        R.append(cur)
        seen.add(cur)
    return R


def spine_path(arcs, Q, z, rng):
    R, seen, cur = [z], {z}, z
    while True:
        nxt = cur + 1
        if nxt in arcs.get(cur, ()) and nxt in Q and nxt not in seen:
            cur = nxt
            R.append(cur)
            seen.add(cur)
        else:
            opts = [v for v in arcs.get(cur, ()) if v in Q and v not in seen]
            if not opts or rng.random() < 0.2:
                return R
            cur = rng.choice(opts)
            R.append(cur)
            seen.add(cur)


def full_run(arcs, r, rng, small=12, spine=False):
    V = set(arcs) | {v for vs in arcs.values() for v in vs} | {r}
    net = Net(arcs, V)
    n = max(V) + 1
    seen, st = {r}, [r]
    while st:
        u = st.pop()
        for v in arcs.get(u, ()):
            if v not in seen:
                seen.add(v)
                st.append(v)
    live = [dict(Q=seen, E={r}, root=r)]
    passes, maxP, maxk = 0, 0, 1
    pid = 0
    while live:
        big = []
        for P in live:
            if len(P['Q']) < small:
                net_arcs = {u: net.out[u] & P['Q'] for u in P['Q']}
                bl = brute_last(net_arcs, P['E'], P['Q'])
                for y, d in bl.items():
                    if d is not None:
                        net.mem[y]['rec'] = d
            else:
                big.append(P)
        if not big:
            break
        for P in big:
            pid += 1
            P['id'] = pid
            P['R'] = spine_path(net.out, P['Q'], P['root'], rng) if spine else rand_path(net.out, P['Q'], P['root'], rng, rng.choice([0.0, 0.02, 0.1]))
            maxk = max(maxk, len(P['R']))
        c0 = net.cP
        STAT['max_problems_at_once'] = max(STAT['max_problems_at_once'], len(big))
        STAT['passes_with_many_problems'] += len(big) > 1
        live = one_pass(net, big, n)
        passes += 1
        maxP = max(maxP, net.cP - c0)
    # truth
    truth = brute_last({u: net.out[u] for u in seen}, {r}, seen)
    bad = [y for y in seen if truth[y] != net.mem[y].get('rec')]
    return bad, passes, maxP, maxk, net, len(seen)


# generators, own
def g_sparse(rng, n, dens):
    return {u: {v for v in range(n) if v != u and rng.random() < dens / n} for u in range(n)}


def g_nested(rng, k, extra):
    arcs = collections.defaultdict(set)
    for i in range(k - 1):
        arcs[i].add(i + 1)
    nxt = k
    st = [(0, k - 1)]
    while st:
        lo, hi = st.pop()
        if hi - lo < 2 or rng.random() < .2:
            continue
        a = rng.randrange(lo, hi - 1)
        b = rng.randrange(a + 2, hi + 1)
        u, v = (a, b) if rng.random() < .67 else (b, a)
        if nxt < k + extra and rng.random() < .5:
            arcs[u].add(nxt)
            arcs[nxt].add(v)
            nxt += 1
        else:
            arcs[u].add(v)
        st += [(lo, a), (a, b), (b, hi)]
    return {u: set(vs) for u, vs in arcs.items()}


def g_mixed(rng, k, extra):
    """A path with off-path vertices that have several in-arcs from the path and arcs back, so a < b occurs, plus chords."""
    arcs = collections.defaultdict(set)
    for i in range(k - 1):
        arcs[i].add(i + 1)
    for x in range(k, k + extra):
        for _ in range(rng.randrange(1, 4)):
            arcs[rng.randrange(k)].add(x)
        if rng.random() < .6:
            arcs[x].add(rng.randrange(k))
        if rng.random() < .3 and x > k:
            arcs[x].add(rng.randrange(k, x))
    for _ in range(rng.randrange(0, k // 3 + 1)):
        arcs[rng.randrange(k)].add(rng.randrange(k))
    return {u: {v for v in vs if v != u} for u, vs in arcs.items()}


def g_rings(rng, k):
    arcs = collections.defaultdict(set)
    for i in range(k - 1):
        arcs[i].add(i + 1)
    lo, hi = rng.randrange(1, 3), k - 1 - rng.randrange(0, 2)
    while hi - lo > 2:
        arcs[lo].add(hi)
        if rng.random() < .33 and hi - 2 > lo + 1:
            arcs[hi].add(hi - 2)
            hi -= 2
        lo += rng.randrange(1, 4)
        hi -= rng.randrange(1, 4)
    return {u: set(vs) for u, vs in arcs.items()}


def lane(seed, secs, bigk=False):
    rng = random.Random(seed)
    t0 = time.time()
    st = collections.Counter()
    while time.time() - t0 < secs:
        c = rng.randrange(4)
        kmax = 400 if bigk else 90
        if c == 0:
            nn = rng.randrange(4, kmax // 2)
            arcs, r = g_sparse(rng, nn, rng.choice([1.2, 1.6, 2.2, 3.0])), rng.randrange(nn)
        elif c == 1:
            k = rng.randrange(4, kmax)
            arcs, r = g_nested(rng, k, rng.randrange(0, 30)), 0
        elif c == 2:
            arcs, r = g_rings(rng, rng.randrange(8, kmax)), 0
        else:
            k = rng.randrange(4, kmax // 2)
            arcs, r = g_mixed(rng, k, rng.randrange(1, k + 3)), 0
        bad, passes, maxP, maxk, net, sz = full_run(arcs, r, rng, rng.choice([1, 2, 4, 12]), spine=c > 0)
        st['runs'] += 1
        st['n.vertices'] += sz
        st['n.passes'] += passes
        st['max.P_per_pass'] = max(st['max.P_per_pass'], maxP)
        st['max.k'] = max(st['max.k'], maxk)
        st['FAIL.tree'] += 1 if bad else 0
    st.update({'stat.' + k: v for k, v in STAT.items()})
    return dict(st)


def scale():
    rng = random.Random(5)
    for name, mk in (('rings', lambda s: g_rings(rng, s)), ('nested', lambda s: g_nested(rng, s, s // 3)), ('sparse', lambda s: g_sparse(rng, s, 2.0))):
        for s in (64, 256, 1024, 4096):
            if name == 'sparse' and s > 1024:
                continue
            arcs = mk(s)
            t0 = time.time()
            bad, passes, maxP, maxk, net, sz = full_run(arcs, 0, rng, 12, spine=name != 'sparse') if s <= 1024 else (None,) * 6
            if bad is None:
                # no brute force at this size: run one pass and check m only by the sizes of operations
                V = set(arcs) | {v for vs in arcs.values() for v in vs}
                net = Net(arcs, V)
                seen, st = {0}, [0]
                while st:
                    u = st.pop()
                    for v in net.out[u]:
                        if v not in seen:
                            seen.add(v)
                            st.append(v)
                R = spine_path(net.out, seen, 0, rng)
                one_pass(net, [dict(id=1, Q=seen, E={0}, R=R)], max(V) + 1)
                maxk, maxP, passes = len(R), net.cP, 1
                print(json.dumps(dict(fam=name, n=len(V), k=maxk, P_one_pass=maxP, P_over_log2k_sq=round(maxP / math.log2(maxk) ** 2, 2), MS=net.cMS, secs=round(time.time() - t0, 1))), flush=True)
                continue
            print(json.dumps(dict(fam=name, n=sz, passes=passes, max_k=maxk, max_P_per_pass=maxP, P_over_log2k_sq=round(maxP / max(1, math.log2(max(2, maxk))) ** 2, 2), bad=len(bad), secs=round(time.time() - t0, 1))), flush=True)


def controls(seed, secs):
    global CTL
    out = {}
    for c in ['nogood', 'firstcand', 'norest', 'bflip', 'nog_mark']:
        CTL = c
        rng = random.Random(seed)
        t0, runs, fails, raised = time.time(), 0, 0, collections.Counter()
        while time.time() - t0 < secs:
            k = rng.randrange(8, 60)
            w = rng.randrange(3)
            arcs = g_rings(rng, k) if w == 0 else g_nested(rng, k, 10) if w == 1 else g_mixed(rng, k, 12)
            try:
                bad, *_ = full_run(arcs, 0, rng, 1, spine=True)
                fails += 1 if bad else 0
            except (RouteClash, AssertionError, KeyError, TypeError) as e:
                raised[type(e).__name__] += 1
            runs += 1
        out[c] = dict(runs=runs, wrong_tree=fails, raised=dict(raised))
    CTL = None
    return out


if __name__ == '__main__':
    if sys.argv[1] == 'scale':
        scale()
    elif sys.argv[1] == 'ctl':
        print(json.dumps(controls(int(sys.argv[2]), float(sys.argv[3])), indent=0))
    else:
        print(json.dumps(lane(int(sys.argv[1]), float(sys.argv[2]), len(sys.argv) > 3)))
