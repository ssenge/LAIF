"""Who knows what: Section 5 and the entry marks of notes/DOMINATORS.md with local states and explicit parts.

Every value is held by one vertex in S[v]. It moves only by
  ex(...)   one round on the edges of G, O(1) words per edge,
  P(...)    one application of (P): each vertex names its part from its own state, parts are checked connected in G,
            one part per vertex, values at most WMAX words,
  ms(...)   the Multi-Source Lemma as a black box on arcs whose two ends agree on a group id (after one exchange).
Part ids, values and stores are functions of S[v] and of v's own arcs only. No repo code except instance generators.

python3 -I -B who.py SEED SECS [big]
"""
import collections, json, math, os, random, sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
import networkx as nx

WMAX = 4
INF = 10 ** 9
MUT = os.environ.get('WHO_MUT', '') if False else ''


class Sim:
    def __init__(self, G, arcs, st, literal_marks=False):
        self.G, self.arcs, self.st = G, arcs, st
        self.inn = collections.defaultdict(set)
        for u, vs in arcs.items():
            for v in vs:
                self.inn[v].add(u)
        self.S = {v: {} for v in G}
        self.rec = {}
        self.ent = {}
        self.literal_marks = literal_marks

    def P(self, name, part_of, value_of, combine, store):
        st = self.st
        st['P'] += 1
        self.passP += 1
        parts = collections.defaultdict(list)
        for v in self.G:
            pid = part_of(v)
            if pid is not None:
                parts[pid].append(v)
        res = {}
        for pid, vs in parts.items():
            if len(vs) > 1 and not nx.is_connected(self.G.subgraph(vs)):
                st['FAIL.part_not_connected.' + name] += 1
            cur = None
            for v in vs:
                x = value_of(v)
                if x is not None:
                    if isinstance(x, tuple) and len(x) > WMAX:
                        st['FAIL.words.' + name] += 1
                    cur = x if cur is None else combine(cur, x)
            res[pid] = cur
        for pid, vs in parts.items():
            for v in vs:
                store(v, res[pid])

    def ex(self, name, send, recv):
        """One round. send(v) gives (message to all neighbours) or None. recv(v, {u: msg})."""
        self.st['rounds_ex'] += 1
        out = {v: send(v) for v in self.G}
        for v in self.G:
            got = {u: out[u] for u in self.G[v] if out[u] is not None}
            recv(v, got)

    def ms(self, group_of, source_of, store):
        self.st['MS'] += 1
        grp = {v: group_of(v) for v in self.G}
        seen = {v for v in self.G if grp[v] is not None and source_of(v)}
        stack = list(seen)
        while stack:
            u = stack.pop()
            for v in self.arcs.get(u, ()):
                if grp[v] is not None and grp[v] == grp[u] and v not in seen:
                    seen.add(v)
                    stack.append(v)
        for v in self.G:
            if grp[v] is not None:
                store(v, v in seen)


def roles(t, k, lev):
    size = 1 << lev
    block = (t - 1) >> (lev + 1)
    l = block * 2 * size + 1
    c = l + size - 1
    r = min(k, l + 2 * size - 1)
    return block, l, c, r


def sweep(sim, group_of, val_of, op, before, store, B):
    """Value of op over strictly earlier (before) or strictly later positions in the same group. O(log) applications of (P)."""
    S = sim.S
    res = {}
    for b in range(B):
        def part(v):
            g = group_of(v)
            return None if g is None else (g, (S[v]['pos'] - 1) >> (b + 1))

        def value(v):
            bit = ((S[v]['pos'] - 1) >> b) & 1
            return val_of(v) if (bit == 0) == before else None

        def put(v, x, b=b):
            bit = ((S[v]['pos'] - 1) >> b) & 1
            if (bit == 1) == before and x is not None:
                res[v] = x if v not in res else op(res[v], x)
        sim.P('sweep', part, value, op, put)
    for v in sim.G:
        g = group_of(v)
        if g is not None:
            store(v, res.get(v))


def path_step_all(sim, probs, keep_b=True):
    """probs: {pid: (Q, R)}. Entries are the bits S[v]['E'], set before."""
    S, st = sim.S, sim.st
    for v in sim.G:
        S[v] = {'E': sim.ent.get(v, False), 'p': None, 'pos': 0, 'level': {}}
    for pid, (Q, R) in probs.items():
        for v in Q:
            S[v]['p'] = pid
        for i, v in enumerate(R, 1):
            S[v]['pos'] = i      # by (T2)
    # k by (P) over Q
    sim.P('Q', lambda v: S[v]['p'], lambda v: S[v]['pos'] or None, max, lambda v, x: S[v].__setitem__('k', x))
    Kmax = max(len(R) for _, R in probs.values())
    B = max(1, math.ceil(math.log2(Kmax + 1)))
    N = len(sim.G) + 1
    idx = {v: i for i, v in enumerate(sorted(sim.G))}

    # step 1: heads and keys in one exchange
    def send1(v):
        return (S[v]['p'], S[v]['pos']) if S[v]['p'] is not None else None

    def recv1(v, got):
        if S[v]['p'] is None or S[v]['pos']:
            return
        tails = [m[1] for u, m in got.items() if u in sim.inn[v] and m[0] == S[v]['p'] and m[1] > 0]
        ia = 0 if S[v]['E'] else (min(tails) if tails else None)
        S[v]['ka'] = None if ia is None else ia * N + idx[v]
        S[v]['kb'] = None if not tails else (S[v]['k'] - max(tails)) * N + idx[v]
    sim.ex('keys', send1, recv1)
    bits = math.ceil(math.log2((Kmax + 2) * N))

    def search(tag):
        pre = {v: 0 for v in sim.G if S[v]['p'] is not None and not S[v]['pos']}
        for bit in range(bits - 1, -1, -1):
            def grp(v):
                return (S[v]['p'], pre[v]) if v in pre else None

            def src(v):
                k = S[v].get(tag)
                return k is not None and (k >> (bit + 1)) == pre[v] and ((k >> bit) & 1) == 0

            def store(v, reached):
                pre[v] = (pre[v] << 1) | (0 if reached else 1)
            sim.ms(grp, src, store)
        return pre
    ea, eb = search('ka'), search('kb')
    for v in ea:
        S[v]['a'] = ea[v] // N
        S[v]['ea'] = ea[v]
        S[v]['b'] = S[v]['k'] - eb[v] // N
        S[v]['eb'] = eb[v]

    # A, B and the neighbour towards A_a
    def send2(v):
        s = S[v]
        if s['p'] is None:
            return None
        return (s['p'], s['pos'], s.get('a'), s.get('b'))

    def recv2(v, got):
        s = S[v]
        if not s['pos'] or s['pos'] < 2:
            return
        t = s['pos']
        A, Bb, nb = INF, -INF, {}
        if s['E']:
            A, Bb = 0, 0
        for u, m in got.items():
            if u in sim.inn[v] and m[0] == s['p']:
                if m[1]:
                    i = m[1]
                    if i != t and i != t - 1:
                        A, Bb = min(A, i), max(Bb, i)
                        nb[i] = u
                else:
                    A, Bb = min(A, m[2]), max(Bb, m[3])
                    nb[m[2]] = u
        s['A'], s['B'], s['nb'] = A, Bb, nb
    sim.ex('AB', send2, recv2)
    for v in sim.G:
        if S[v]['pos'] == 1:
            S[v]['A'], S[v]['B'], S[v]['nb'] = INF, -INF, {}

    def active(v, lev):
        """segment of v at this level, or None if Y is empty"""
        s = S[v]
        if not s['pos']:
            return None
        block, l, c, r = roles(s['pos'], s['k'], lev)
        return None if c + 1 > s['k'] else (s['p'], lev, block)

    def inY(v, lev):
        return S[v]['pos'] > roles(S[v]['pos'], S[v]['k'], lev)[2]

    def Agroup(v):
        s = S[v]
        return s['pos'] if s['pos'] else s.get('a', 0)

    def Bgroup(v):
        s = S[v]
        return s['pos'] if s['pos'] else s.get('b', 0)
    LEV = max(1, math.ceil(math.log2(Kmax))) if Kmax > 1 else 0

    # step 2
    for lev in range(LEV):
        def seg(v):
            return active(v, lev)

        def gZ(v):
            return (seg(v), 'Z') if seg(v) is not None and not inY(v, lev) else None

        def gY(v):
            return (seg(v), 'Y') if seg(v) is not None and inY(v, lev) else None
        for v in sim.G:
            if S[v]['pos']:
                S[v]['level'][lev] = {}
        L = lambda v: S[v]['level'][lev]
        sweep(sim, gY, lambda v: S[v]['B'], max, True, lambda v, x: L(v).__setitem__('M', x), B)

        def good(v):
            s = S[v]
            t = s['pos']
            c = roles(t, s['k'], lev)[2]
            m = L(v).get('M')
            return t >= c + 2 and (m is None or m < t)
        sweep(sim, gY, lambda v: S[v]['pos'] if good(v) else None, max, True, lambda v, x: L(v).__setitem__('gb', x), B)
        for v in sim.G:
            if gY(v) is not None:
                L(v)['g'] = S[v]['pos'] if good(v) else L(v).get('gb')
        # over S: max B on Y, max good on Y, t0
        sim.P('S1', seg, lambda v: S[v]['B'] if inY(v, lev) else None, max, lambda v, x: L(v).__setitem__('maxB', x))
        sim.P('S2', seg, lambda v: S[v]['pos'] if inY(v, lev) and good(v) else None, max, lambda v, x: L(v).__setitem__('maxgood', x))

        def v0(v):
            s = S[v]
            return s['pos'] if inY(v, lev) and s['A'] < roles(s['pos'], s['k'], lev)[1] else None
        sim.P('S3', seg, v0, min, lambda v, x: L(v).__setitem__('t0', x))
        sim.P('S4', seg, lambda v: (L(v).get('g') or 0) if L(v).get('t0') == S[v]['pos'] else None, max, lambda v, x: L(v).__setitem__('gt0', x))
        for v in sim.G:
            if seg(v) is None:
                continue
            s = S[v]
            r = roles(s['pos'], s['k'], lev)[3]
            mb = L(v).get('maxB')
            L(v)['gr1'] = r + 1 if (mb is None or mb < r + 1) else (L(v).get('maxgood') or 0)
            L(v)['r'] = r
        # leaves send (t, g(t)) over one edge to A_a, then one aggregate over A_a
        inbox = collections.defaultdict(list)
        for v in sim.G:
            if gY(v) is None:
                continue
            s = S[v]
            a = s['A']
            block, l, c, r = roles(s['pos'], s['k'], lev)
            if l <= a <= c:
                u = s['nb'].get(a)
                if u is None:
                    st['FAIL.leaf_no_neighbour'] += 1
                    continue
                if u not in sim.G[v]:
                    st['FAIL.leaf_not_adjacent'] += 1
                inbox[u].append((s['pos'], L(v).get('g') or 0))
                st['leaf_msgs'] += 1

        def partA(v):
            s = S[v]
            if s['p'] is None:
                return None
            a = Agroup(v)
            if a < 1:
                return None
            k = s['k']
            block, l, c, r = roles(a, k, lev)
            return (s['p'], a) if a <= c and c + 1 <= k else None
        sim.P('A_leaf', partA, lambda v: min(inbox[v]) if v in inbox else None, min, lambda v, x: S[v].__setitem__(('ta', lev), x))

        # X(j)
        def tval(v):
            x = S[v].get(('ta', lev))
            return x
        sweep(sim, gZ, tval, min, True, lambda v, x: L(v).__setitem__('Xs', x), B)
        for v in sim.G:
            if gZ(v) is None:
                continue
            s = S[v]
            r = L(v)['r']
            opts = [(r + 1, L(v)['gr1'])]
            if L(v).get('t0') is not None:
                opts.append((L(v)['t0'], L(v).get('gt0') or 0))
            if L(v).get('Xs') is not None:
                opts.append(L(v)['Xs'])
            L(v)['X'] = min(opts)
        sweep(sim, gZ, lambda v: S[v]['A'], min, False, lambda v, x: L(v).__setitem__('sa', x), B)
        sweep(sim, gZ, lambda v: S[v]['B'], max, False, lambda v, x: L(v).__setitem__('sb', x), B)
        for v in sim.G:
            if gZ(v) is None:
                continue
            s = S[v]
            j = s['pos']
            x = L(v)['X'][1]
            sa, sb = L(v).get('sa'), L(v).get('sb')
            if x and (sa is None or sa >= j) and (sb is None or sb < x):
                s['cand'] = max(s.get('cand', 0), x)
    for v in sim.G:
        if S[v]['pos']:
            S[v]['m'] = max(S[v]['pos'] + 1, S[v].get('cand', 0))

    # step 3
    for lev in range(LEV):
        def seg(v):
            return active(v, lev)

        def gZ(v):
            return (seg(v), 'Z') if seg(v) is not None and not inY(v, lev) else None

        def gY(v):
            return (seg(v), 'Y') if seg(v) is not None and inY(v, lev) else None
        L = lambda v: S[v]['level'][lev]

        def member(v):
            s = S[v]
            return gZ(v) is not None and s['m'] > roles(s['pos'], s['k'], lev)[2] + 1
        sweep(sim, gZ, lambda v: S[v]['pos'] if member(v) else None, max, True, lambda v, x: L(v).__setitem__('lb', x), B)
        for v in sim.G:
            if gZ(v) is not None:
                L(v)['lam'] = S[v]['pos'] if member(v) else L(v).get('lb')

        def send(v):
            return (S[v]['p'], S[v]['pos'], S[v]['m'], L(v)['X'][0], True) if gZ(v) is not None and member(v) else None
        succ = {}

        def recv(v, got):
            if gZ(v) is None:
                return
            for u, m in got.items():
                # the successor on R, known from positions, in the same Z
                if u in sim.arcs.get(v, ()) and m[0] == S[v]['p'] and m[1] == S[v]['pos'] + 1 and gZ(u) == gZ(v):
                    succ[v] = m
        sim.ex('member', send, recv)

        def part_ring(v):
            return (gZ(v), L(v)['lam']) if gZ(v) is not None and L(v)['lam'] is not None else None
        sim.P('ring_m', part_ring, lambda v: S[v]['m'] if member(v) else None, max, lambda v, x: L(v).__setitem__('mi', x))
        sim.P('ring_next', part_ring, lambda v: (succ[v][2], succ[v][3], succ[v][1]) if v in succ else None, max, lambda v, x: L(v).__setitem__('nxt', x))
        # a decides, and sends over A_a
        def sendval(v):
            s = S[v]
            if not s['pos'] or gZ(v) is None or L(v).get('nxt') is None or L(v).get('lam') is None:
                return None
            ta = s.get(('ta', lev))
            if ta is None:
                return None
            mi = L(v)['mi']
            mn, xn, jn = L(v)['nxt']
            r = L(v)['r']
            if mn < mi <= r and ta[0] == xn:
                st['ring_sends'] += 1
                return (ta[0], L(v)['lam'])
            return None

        def partA(v):
            s = S[v]
            if s['p'] is None:
                return None
            a = Agroup(v)
            if a < 1:
                return None
            k = s['k']
            block, l, c, r = roles(a, k, lev)
            return (s['p'], a) if a <= c and c + 1 <= k else None
        sim.P('A_mark', partA, sendval, max, lambda v, x: S[v].__setitem__(('msg', lev), x))

        def send3(v):
            return ('m', partA(v), S[v].get(('msg', lev))) if S[v].get(('msg', lev)) is not None else None
        marks = {}

        def recv3(v, got):
            s = S[v]
            if gY(v) is None:
                return
            a = s['A']
            u = s['nb'].get(a) if a < INF else None
            if u is not None and u in got and got[u][1] == (s['p'], a) and got[u][2][0] == s['pos']:
                marks[v] = (L(v).get('g'), got[u][2][1])
        sim.ex('mark', send3, recv3)
        # p_a itself may be the neighbour: covered since p_a is in the part and has the message
        # routes: for each dyadic piece of Y, at most one mark crosses the middle
        at = {}
        for v, (pos, val) in marks.items():
            if pos is None:
                st['FAIL.mark_no_g'] += 1
                continue
            if pos == S[v]['pos']:
                at[v] = (pos, val)
        for b in range(B):
            def part(v):
                g = gY(v)
                return None if g is None else (g, (S[v]['pos'] - 1) >> (b + 1))

            def value(v):
                if v not in marks or marks[v][0] is None:
                    return None
                pos, val = marks[v]
                t = S[v]['pos']
                if pos != t and (pos - 1) >> (b + 1) == (t - 1) >> (b + 1) and (((t - 1) >> b) & 1) == 1 and (((pos - 1) >> b) & 1) == 0:
                    st['route_cross'] += 1
                    return (1, pos, val)
                return None

            def comb(x, y):
                st['FAIL.routes_meet'] += 1
                return (x[0] + y[0], x[1], x[2])

            def put(v, x):
                if x is not None and x[1] == S[v]['pos']:
                    at[v] = (x[1], x[2])
            sim.P('route', part, value, comb, put)
        # rest, over S
        def jv(v):
            return S[v]['pos'] if member(v) and S[v]['m'] > L(v)['r'] else None
        sim.P('J', seg, jv, max, lambda v, x: L(v).__setitem__('J', x))

        def jpv(v):
            if not member(v):
                return None
            J = L(v).get('J')
            return (S[v]['pos'], S[v]['m']) if J is None or S[v]['pos'] > J else None
        sim.P('jplus', seg, jpv, min, lambda v, x: L(v).__setitem__('jp', x))
        sim.P('last', seg, lambda v: S[v]['pos'] if member(v) else None, max, lambda v, x: L(v).__setitem__('js', x))
        for v in sim.G:
            if seg(v) is None:
                continue
            jp = L(v).get('jp')
            if jp is not None and jp[1] <= L(v)['r'] and jp[1] == S[v]['pos']:
                if v in at:
                    st['FAIL.mark_twice'] += 1
                at[v] = (jp[1], L(v).get('J') or 0)
        sweep(sim, gY, lambda v: at.get(v), max, True, lambda v, x: L(v).__setitem__('db', x), B)
        for v in sim.G:
            if gY(v) is not None:
                x = at.get(v) or L(v).get('db')
                L(v)['delta'] = x[1] if x is not None else (L(v).get('js') or 0)
    # step 4: labels by broadcasts over A_a and B_b, level by level
    for lev in range(LEV):
        L = lambda v: S[v]['level'][lev]

        def pa(v):
            s = S[v]
            if s['p'] is None:
                return None
            a = Agroup(v)
            return (s['p'], a) if a >= 1 else None

        def pb(v):
            s = S[v]
            if s['p'] is None:
                return None
            b = Bgroup(v)
            return (s['p'], b) if b >= 1 else None

        def lab(v):
            if not S[v]['pos'] or lev not in S[v]['level'] or active(v, lev) is None or inY(v, lev):
                return None
            return (L(v).get('lam') or 0,)

        def dab(v):
            if not S[v]['pos'] or lev not in S[v]['level'] or active(v, lev) is None or not inY(v, lev):
                return None
            return (L(v).get('delta') or 0,)
        sim.P('labA', pa, lab, max, lambda v, x: S[v].__setitem__(('la', lev), None if x is None else x[0]))
        sim.P('labB', pb, dab, max, lambda v, x: S[v].__setitem__(('db', lev), None if x is None else x[0]))
    # the position of the dominator is turned into an identifier by one more broadcast in the real thing: labels hold (pos, id)
    out = {}
    for v in sim.G:
        s = S[v]
        if s['p'] is None:
            continue
        if s['pos']:
            d = 0
            for lev in range(LEV):
                if lev in s['level'] and active(v, lev) is not None and inY(v, lev):
                    d = s['level'][lev].get('delta') or 0
                    if d:
                        break
            out[v] = d
        else:
            a, b = s['a'], s['b']
            if a == 0:
                out[v] = 0
            elif a == b:
                out[v] = a
            else:
                lev = ((a - 1) ^ (b - 1)).bit_length() - 1
                x, y = s.get(('la', lev)) or 0, s.get(('db', lev)) or 0
                if x and y:
                    out[v] = min(x, y)
                else:
                    d = 0
                    for l2 in range(lev + 1, LEV):
                        d = s.get(('db', l2)) or 0
                        if d:
                            break
                    out[v] = d
    return out


def direct(arcs, sources, allowed):
    seen = set(s for s in sources if s in allowed)
    stack = list(seen)
    while stack:
        u = stack.pop()
        for v in arcs.get(u, ()):
            if v in allowed and v not in seen:
                seen.add(v)
                stack.append(v)
    return seen


def pick_path(z, Q, arcs, rng, style):
    R, seen = [z], {z}
    cur = z
    while True:
        opts = [v for v in arcs.get(cur, ()) if v in Q and v not in seen]
        if not opts:
            break
        if style == 0 and rng.random() < .05:
            break
        if style == 1:   # greedy: toward large remaining reach
            cur = max(opts, key=lambda v: (len(direct(arcs, [v], Q - seen)), rng.random()))
        elif style == 2 and rng.random() < .2:
            break
        else:
            cur = rng.choice(sorted(opts, key=str))
        R.append(cur)
        seen.add(cur)
    return R


def truth_small(Q, E, arcs, y):
    """Immediate dominator in (Q, E) of y by removal. Returns vertex or None for rho."""
    base = direct(arcs, E, Q)
    if y not in base:
        return None
    doms = [w for w in Q if w != y and y not in direct(arcs, E - {w}, Q - {w})]
    if not doms:
        return None
    return max(doms, key=lambda d: sum(1 for w in Q if w != d and d not in direct(arcs, E - {w}, Q - {w})))


def run(G, arcs, r, st, rng, small=1, literal=False):
    """Whole chain: at each pass all problems of at least `small` vertices take a path at once."""
    Q0 = direct(arcs, [r], set(G))
    sim = Sim(G, arcs, st)
    sim.ent = {r: True}
    probs = {0: (Q0, r)}
    nextid = 1
    passes = 0
    while probs:
        active = {}
        for pid, (Q, z) in probs.items():
            if len(Q) < small:
                E = {v for v in Q if sim.ent.get(v)}
                for y in Q:
                    d = truth_small(Q, E, arcs, y)
                    if d is not None:
                        sim.rec[y] = d
                continue
            R = pick_path(z, Q, arcs, rng, rng.randrange(4))
            if R[0] != z:
                st['FAIL.root'] += 1
            active[pid] = (Q, R)
        if not active:
            break
        passes += 1
        sim.passP = 0
        out = path_step_all(sim, active)
        st['max.P_per_pass'] = max(st['max.P_per_pass'], sim.passP)
        st['max.problems_at_once'] = max(st['max.problems_at_once'], len(active))
        S = sim.S
        new = {}
        # check against definition, on all problems
        for pid, (Q, R) in active.items():
            E = {v for v in Q if sim.ent.get(v)}
            pos = {v: i + 1 for i, v in enumerate(R)}
            O = Q - set(R)
            if len(Q) <= 60 or rng.random() < .05:
                reach_wo = {j: direct(arcs, E - {R[j - 1]}, Q - {R[j - 1]}) for j in pos.values()}
                for y in Q:
                    tr = 0
                    for j in range(1, len(R) + 1):
                        if R[j - 1] != y and y not in reach_wo[j]:
                            tr = j
                    st['chk.y'] += 1
                    if out[y] != tr:
                        st['FAIL.deepest'] += 1
            # a, b by definition
            if len(Q) <= 60 or rng.random() < .05:
                ta, tb = {}, {}
                for i in range(len(R) + 1):
                    src = (E if i == 0 else arcs.get(R[i - 1], ()))
                    f = direct(arcs, [v for v in src if v in O], O)
                    for y in f:
                        ta.setdefault(y, i)
                        tb[y] = i
                for y in O:
                    st['chk.ab'] += 1
                    if S[y]['a'] != ta[y] or S[y]['b'] != tb[y]:
                        st['FAIL.ab'] += 1
            for y in Q:
                if out[y]:
                    sim.rec[y] = R[out[y] - 1]
            # classes from local e(y), by b-key: head has key==e
            cls = collections.defaultdict(set)
            for y in O:
                cls[S[y]['eb']].add(y)
            for e, K in cls.items():
                heads = [h for h in K if S[h].get('kb') == e]
                if len(heads) != 1:
                    st['FAIL.head'] += 1
                new[nextid] = (K, heads[0])
                nextid += 1
        # entries: one exchange
        classof = {}
        for pid, (K, h) in new.items():
            for v in K:
                classof[v] = pid
        allowed_from = Q0 if not literal else set(G)
        for v in classof:
            for u in sim.inn[v]:
                if classof.get(u) != classof[v] and u in allowed_from:
                    sim.ent[v] = True
        # idle problems? none here: every problem takes a path or is small
        for pid, (K, h) in new.items():
            pass
        probs = new
    st['max.passes'] = max(st['max.passes'], passes)
    return sim.rec


def truth(arcs, r, V):
    Gd = nx.DiGraph()
    Gd.add_nodes_from(V)
    Gd.add_edges_from((u, v) for u in arcs for v in arcs[u])
    return {y: d for y, d in nx.immediate_dominators(Gd, r).items() if y != r}


# ------------------------------------------------- instances, all checked planar unless flagged
def wheel_hub(rim, rng):
    """Rim path 1..rim, hub 0. Hub off or on the path, arcs in both directions at random. Root is 1 or the hub."""
    arcs = collections.defaultdict(set)
    for i in range(1, rim):
        arcs[i].add(i + 1)
    if rng.random() < .3:
        arcs[rim].add(1)
    pin, pout = rng.choice([(.1, .1), (.5, .5), (.02, .6), (.6, .02), (.3, .05)])
    for i in range(1, rim + 1):
        if rng.random() < pin:
            arcs[i].add(0)
        if rng.random() < pout:
            arcs[0].add(i)
    return arcs


def rings(m, rng):
    """Planar chain of rings: nested non-crossing chords a -> t, a up and t down, on one side, some through vertices off the path,
    and short back arcs on the other side. Path 0..2m."""
    k = 2 * m + rng.randrange(0, 4)
    arcs = collections.defaultdict(set)
    for i in range(k - 1):
        arcs[i].add(i + 1)
    nxt = k
    a, t = rng.randrange(0, 2), k - 1 - rng.randrange(0, 2)
    mid = k // 2 if rng.random() < .5 else (1 << (k.bit_length() - 1))
    while a < mid - 1 and t > mid + 1:
        if rng.random() < .7:
            if rng.random() < .35:
                arcs[a].add(nxt)
                arcs[nxt].add(t)
                if rng.random() < .3:
                    arcs[nxt].add(nxt + 1)
                    nxt += 1
                nxt += 1
            else:
                arcs[a].add(t)
        a += rng.randrange(1, 3)
        t -= rng.randrange(0, 3)
        if t <= a:
            break
    i = 0
    while i + 2 < k:
        if rng.random() < .15:
            arcs[i + 2].add(i)
            i += 2
        i += 1
    return arcs


def rings2(m, rng):
    """Planar. Nested chords a_i -> T_i, a up, T down, with a back arc t'_i -> t_i on the other side, t_i < T_i <= t'_i, so that the
    mark must travel from T_i back to t_i. Non-crossing on each side."""
    arcs = collections.defaultdict(set)
    k = 2 ** (1 + max(2, int(math.log2(max(m, 2))) + 2))
    for i in range(k - 1):
        arcs[i].add(i + 1)
    nxt = k
    a, top = rng.randrange(0, 2), k - 1 - rng.randrange(0, 3)
    mid = k // 2
    while a < mid - 1:
        d, e = rng.randrange(0, 4), rng.randrange(0, 3)
        tp = top - rng.randrange(0, 2)
        T = tp - e
        t = T - d
        if t <= mid + 1:
            break
        if rng.random() < .3:
            arcs[a].add(nxt)
            arcs[nxt].add(T)
            nxt += 1
        else:
            arcs[a].add(T)
        if tp > t + 1 or d + e >= 1:
            if tp >= t + 2:
                if rng.random() < .3:
                    arcs[tp].add(nxt)
                    arcs[nxt].add(t)
                    nxt += 1
                else:
                    arcs[tp].add(t)
        top = t - 1 if rng.random() < .8 else t
        a += rng.randrange(1, 3)
    return arcs


def pendants(k, rng):
    """Path with many small classes hanging off, each a small DAG or cycle, fed from several indices (planar by construction)."""
    arcs = collections.defaultdict(set)
    for i in range(k - 1):
        arcs[i].add(i + 1)
    nxt = k
    i = 0
    while i + 1 < k:
        s = rng.randrange(1, 4)
        vs = list(range(nxt, nxt + s))
        nxt += s
        arcs[i].add(vs[0])
        for u, v in zip(vs, vs[1:]):
            arcs[u].add(v)
        if rng.random() < .5:
            arcs[vs[-1]].add(i + 1)
        if rng.random() < .3:
            arcs[i + 1].add(vs[-1])
        i += rng.randrange(1, 3)
    return arcs


def nonplanar(n, rng):
    p = rng.choice([1.2, 1.6, 2.2, 3.0]) / n
    return {u: {v for v in range(n) if v != u and rng.random() < p} for u in range(n)}


def instance(rng, big):
    import gdfs
    q = rng.random()
    if q < .2:
        return 'wheel', wheel_hub(rng.randrange(5, 200 if big else 50), rng), True
    if q < .3:
        return 'rings', rings(rng.randrange(3, 120 if big else 24), rng), True
    if q < .4:
        return 'rings2', rings2(rng.randrange(3, 40 if big else 10), rng), True
    if q < .55:
        return 'pendants', pendants(rng.randrange(4, 80 if big else 24), rng), True
    if q < .7:
        return 'nonplanar', nonplanar(rng.randrange(3, 60 if big else 25), rng), False
    name, arcs = gdfs.instance(rng, False)
    return name, {u: set(vs) for u, vs in arcs.items()}, True


def main(seed, secs, big=False):
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    fails = []
    while time.time() - t0 < secs:
        name, arcs, planar = instance(rng, big)
        V = set(arcs) | {v for vs in arcs.values() for v in vs}
        if len(V) < 2:
            continue
        U = nx.Graph()
        U.add_nodes_from(V)
        U.add_edges_from((u, v) for u in arcs for v in arcs[u])
        if planar:
            st['chk.planar'] += 1
            if not nx.check_planarity(U)[0]:
                st['FAIL.not_planar'] += 1
                continue
        else:
            st['nonplanar_runs'] += 1
        # network: arc-less extra edges would be fine; G here is the underlying graph, made connected by a star of arc-less edges only if it is not connected and non-planar is allowed
        if not nx.is_connected(U):
            comps = [sorted(c, key=str)[0] for c in nx.connected_components(U)]
            for x, y in zip(comps, comps[1:]):
                U.add_edge(x, y)
        r = rng.choice(sorted(V, key=str))
        small = rng.choice([1, 1, 2, 3, 12])
        rec = run(U, arcs, r, st, rng, small)
        true = truth(arcs, r, V)
        st['runs'] += 1
        st['fam.' + name.split('.')[0]] += 1
        st['n.vertices'] += len(true)
        st['max.n'] = max(st['max.n'], len(V))
        if rec != true:
            st['FAIL.tree'] += 1
            if len(fails) < 3:
                fails.append((name, r, sorted((u, sorted(vs)) for u, vs in arcs.items()), small))
    return dict(sorted((k, int(v)) for k, v in st.items())), fails


if __name__ == '__main__':
    out, fails = main(int(sys.argv[1]), float(sys.argv[2]), len(sys.argv) > 3)
    print(json.dumps(out))
    for f in fails:
        print(f)
