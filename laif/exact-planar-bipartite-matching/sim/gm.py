"""Exact matching in general planar networks: centralized simulation of notes/GENERAL.md.

Checks the logic of elimination in the tree of bags, the search for mates and the certificate, and counts
words per bag. It does not simulate rounds. Every assert and every FAIL counter is a claim of the note.

python3 -I gm.py SEED SECS [big]    main lane
python3 -I gm.py ctl SEED SECS      negative controls
python3 -I gm.py region SEED SECS   region bags of the sibling repository, with hierarchy checks
python3 -I gm.py scale              words on grids with diagonals, on region bags
python3 -I gm.py tw SEED SECS       Section 6: low treewidth, many children per bag, with the filter
python3 -I gm.py twctl SEED SECS    controls of the filter
python3 -I gm.py paths SEED SECS    vertex-disjoint s-t paths in digraphs, with a control
"""
import collections, json, os, random, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
import numpy as np
import fam
import mm

P = 2147483647


# ---------------------------------------------------------------- hierarchy
class H:
    """A tree of bags: V[b], S[b], kids[b], parent[b], depth[b]. A leaf has kids[b] == []."""

    def __init__(self, V, S, kids, parent, depth, root):
        self.V, self.S, self.kids, self.parent, self.depth, self.root = V, S, kids, parent, depth, root
        self.Qp = {}          # union of S over strict ancestors
        for b in sorted(V, key=lambda x: depth[x]):
            a = parent[b]
            self.Qp[b] = set() if a is None else self.Qp[a] | S[a]
        self.home = {}
        for b in sorted(V, key=lambda x: depth[x]):
            for v in V[b]:
                if v in self.Qp[b]:
                    continue
                if not kids[b] or v in S[b]:
                    assert v not in self.home, 'two homes'
                    self.home[v] = b
        self.members = collections.defaultdict(list)
        for v, b in self.home.items():
            self.members[b].append(v)

    def post(self, r):
        out, st = [], [r]
        while st:
            b = st.pop()
            out.append(b)
            st.extend(self.kids[b])
        return out[::-1]

    def below(self, b, a):
        while b is not None:
            if b == a:
                return True
            b = self.parent[b]
        return False


def from_mm(root, bags):
    V = {b.id: set(b.V) for b in bags}
    S = {b.id: set(b.sep) for b in bags}
    kids = {b.id: [k.id for k in b.kids] for b in bags}
    parent = {b.id: (b.parent.id if b.parent else None) for b in bags}
    depth = {b.id: b.depth for b in bags}
    return H(V, S, kids, parent, depth, root.id)


def assign_edges(h, E, st):
    """Each edge goes to the deeper home of its ends; both ends are then in V(bag) and no edge is lost."""
    own = collections.defaultdict(list)
    for u, v in E:
        a, b = h.home[u], h.home[v]
        if h.depth[a] > h.depth[b]:
            a, b = b, a
        if not h.below(b, a):
            st['FAIL.homes_incomparable'] += 1
        if u not in h.V[b] or v not in h.V[b]:
            st['FAIL.edge_not_in_home_bag'] += 1
        own[b].append((u, v))
    return own


# ---------------------------------------------------------------- arithmetic
def inv(a, p):
    return pow(int(a) % p, p - 2, p)


def rank_mod(M, p):
    M = M.copy() % p
    r = 0
    rows, cols = M.shape
    for c in range(cols):
        nz = np.nonzero(M[r:, c])[0] if r < rows else []
        if len(nz) == 0:
            continue
        k = r + int(nz[0])
        if k != r:
            M[[r, k]] = M[[k, r]]
        M[r] = M[r] * inv(M[r, c], p) % p
        for i in np.nonzero(M[:, c])[0]:
            if i != r:
                M[i] = (M[i] - M[i, c] * M[r]) % p
        r += 1
    return r


def indep_rows(M, p):
    """The rows taken greedily, as a list of positions."""
    M = M.copy() % p
    keep, basis = [], []            # basis: (pivot column, reduced row)
    for i in range(M.shape[0]):
        row = M[i].copy()
        for c, br in basis:
            if row[c]:
                row = (row - row[c] * br) % p
        nz = np.nonzero(row)[0]
        if len(nz):
            c = int(nz[0])
            row = row * inv(row[c], p) % p
            basis.append((c, row))
            keep.append(i)
    return keep


class Fact:
    __slots__ = ('J', 'piv', 'out')


def eliminate(h, own, a, root, active, st, p=P, mode='ok', flt=False, rng=None):
    """Bottom-up over the subtree of root, on the active vertices. Returns the facts per bag, pivots and dropped."""
    facts, pivots, dropped = {}, [], []
    out = {}
    for b in h.post(root):
        idx = set(v for v in h.members[b] if v in active)
        edges = [(u, v) for u, v in own[b] if u in active and v in active]
        for u, v in edges:
            idx.add(u)
            idx.add(v)
        for k in h.kids[b]:
            idx |= set(out[k][0])
        J = sorted(idx)
        pos = {v: i for i, v in enumerate(J)}
        M = np.zeros((len(J), len(J)), dtype=np.int64)
        for u, v in edges:
            M[pos[u], pos[v]] = (M[pos[u], pos[v]] + a[(u, v)]) % p
            M[pos[v], pos[u]] = (M[pos[v], pos[u]] - a[(u, v)]) % p
        words = len(edges)
        for k in h.kids[b]:
            Jk, Mk = out[k]
            words += len(Jk) ** 2
            if Jk:
                ix = [pos[v] for v in Jk]
                M[np.ix_(ix, ix)] = (M[np.ix_(ix, ix)] + Mk) % p
        st['max.words_in_bag'] = max(st['max.words_in_bag'], words)
        interior = [i for i, v in enumerate(J) if v not in h.Qp[b]]
        bnd = [i for i, v in enumerate(J) if v in h.Qp[b]]
        if flt and h.kids[b]:
            # Section 6: rows retained by children are zero on each other, so a basis on the rest suffices
            Rr = [i for i in interior if J[i] not in h.S[b]]
            others = [i for i in range(len(J)) if i not in set(Rr)]
            if Rr:
                if M[np.ix_(Rr, Rr)].any():
                    st['FAIL.retained_block_not_zero'] += 1
                st['max.R_before_filter'] = max(st['max.R_before_filter'], len(Rr))
                k0 = indep_rows(M[np.ix_(Rr, others)], p) if others else []
                st['max.R_after_filter'] = max(st['max.R_after_filter'], len(k0))
                if len(k0) > len(others):
                    st['FAIL.filter_above_bag'] += 1
                if mode == 'fltbad' and k0:
                    k0 = k0[:-1]
                gone = [Rr[i] for i in range(len(Rr)) if i not in set(k0)]
                dropped += [J[i] for i in gone]
                M[gone, :] = 0
                M[:, gone] = 0
                goneset = set(gone)
                interior = [i for i in interior if i not in goneset]
                st['chk.filter'] += 1
        rem, zero, piv = list(interior), [], []
        while rem:
            i = rem.pop(0)
            j = next((x for x in rem if M[i, x] % p), None)
            if j is None:
                zero.append(i)
                continue
            rem.remove(j)
            d = int(M[i, j])
            di = inv(d, p)
            ri, rj = M[i].copy(), M[j].copy()
            piv.append((i, j, d, ri, rj))
            if mode != 'noschur':
                # with block [[0,d],[-d,0]], row q loses M[q,i]*(-1/d)*M[j,.] + M[q,j]*(1/d)*M[i,.]
                ci, cj = M[:, i].copy(), M[:, j].copy()
                M = (M + (np.outer(ci, rj) % p) * di % p - (np.outer(cj, ri) % p) * di % p) % p
            M[i], M[j], M[:, i], M[:, j] = 0, 0, 0, 0
            pivots += [J[i], J[j]]
        if zero and M[np.ix_(zero, zero)].any():
            st['FAIL.interior_not_zero'] += 1
        keep = [] if mode == 'noretain' else indep_rows(M[np.ix_(zero, bnd)], p) if bnd else []
        if len(keep) > len(bnd):
            st['FAIL.retained_above_boundary'] += 1
        kept = [zero[i] for i in keep]
        dropped += [J[i] for i in zero if i not in kept]
        rest = sorted(kept + bnd)
        st['max.retained'] = max(st['max.retained'], len(kept))
        st['chk.retained'] += 1
        if kept:
            st['bags.with_retained'] += 1
        if b == root and rest:
            st['FAIL.root_has_rest'] += 1
        Jo = [J[i] for i in rest]
        out[b] = (Jo, M[np.ix_(rest, rest)].copy() if rest else np.zeros((0, 0), dtype=np.int64))
        f = Fact()
        f.J, f.piv, f.out = J, piv, Jo
        facts[b] = f
    return facts, pivots, dropped


def solve(h, facts, root, active, rhs, st, p=P):
    """A x = rhs on active, by message passing over the bags of the subtree: rhs[v] enters at the home of v."""
    up, saved, order = {}, {}, h.post(root)
    for b in order:
        f = facts[b]
        pos = {v: i for i, v in enumerate(f.J)}
        y = np.zeros(len(f.J), dtype=np.int64)
        for v in h.members[b]:
            if v in active:
                y[pos[v]] = rhs.get(v, 0) % p
        for k in h.kids[b]:
            for v, val in zip(facts[k].out, up[k]):
                y[pos[v]] = (y[pos[v]] + val) % p
        st['max.solve_words'] = max(st['max.solve_words'], len(f.J))
        sv = []
        for i, j, d, ri, rj in f.piv:
            di = inv(d, p)
            yi, yj = int(y[i]), int(y[j])
            sv.append((yi, yj))
            ci, cj = (-ri) % p, (-rj) % p
            y = (y + (ci * yj % p) * di % p - (cj * yi % p) * di % p) % p
        up[b] = [int(y[pos[v]]) for v in f.out]
        saved[b] = sv
    x = {}
    for b in reversed(order):
        f = facts[b]
        pos = {v: i for i, v in enumerate(f.J)}
        val = np.zeros(len(f.J), dtype=np.int64)
        for v in f.out:
            val[pos[v]] = x[v]
        for (i, j, d, ri, rj), (yi, yj) in zip(reversed(f.piv), reversed(saved[b])):
            di = inv(d, p)
            bi = (yi - int((ri * val % p).sum() % p)) % p
            bj = (yj - int((rj * val % p).sum() % p)) % p
            # [[0,d],[-d,0]] (xi,xj) = (bi,bj)
            val[j] = bi * di % p
            val[i] = (-bj) * di % p
            x[f.J[i]], x[f.J[j]] = int(val[i]), int(val[j])
    return x


# ---------------------------------------------------------------- mates
def find_matching(h, own, a, B, adj, st, p=P, mode='ok'):
    mate, matched = {}, set()
    for X in sorted(h.V, key=lambda b: h.depth[b]):
        act = {v for v in h.V[X] if v not in h.Qp[X] and v in B and v not in matched}
        if not act:
            continue
        for v in act:
            for w in adj[v]:
                if w in B and w not in matched and w not in act:
                    st['FAIL.edge_leaves_bag'] += 1
        facts, piv, drop = eliminate(h, own, a, X, act, st, p)
        if drop:
            st['FAIL.singular_at_bag'] += 1
            return mate
        hubs = sorted(act) if not h.kids[X] else sorted(h.S[X] & act)
        cols, R = {}, []
        st['max.hubs'] = max(st['max.hubs'], len(hubs))
        nsol = 0
        for s in hubs:
            if s in matched:
                continue
            cs = solve(h, facts, X, act, {s: 1}, st, p)
            nsol += 1
            cur = act - set(R)
            if R:
                FRR = np.array([[cols[r][q] for r in R] for q in R], dtype=np.int64) % p
                w = solve_small(FRR, [cs[q] for q in R], p)
                if w is None:
                    st['FAIL.F_on_R_singular'] += 1
                    return mate
            else:
                w = []
            val = {}
            for v in cur:
                t = cs[v]
                if mode != 'nocorr':
                    for wj, r in zip(w, R):
                        t = (t - wj * cols[r][v]) % p
                val[v] = t % p
            if mode == 'paranoid' or st['chk.residual'] < 200000:
                # independent check: A_cur val = e_s
                for x in cur:
                    tot = 0
                    for y in adj[x]:
                        if y in cur:
                            tot += (a[(x, y)] if x < y else -a[(y, x)]) * val[y]
                    if (tot - (1 if x == s else 0)) % p and mode == 'ok':
                        st['FAIL.residual'] += 1
                    st['chk.residual'] += 1
            cand = sorted(v for v in adj[s] if v in cur and v != s and (val[v] or mode == 'anyedge'))
            if not cand:
                st['FAIL.no_partner'] += 1
                return mate
            v = cand[0]
            mate[s], mate[v] = v, s
            matched |= {s, v}
            cols[s] = cs
            cols[v] = solve(h, facts, X, act, {v: 1}, st, p)
            nsol += 1
            R += [s, v]
            st['chk.partner'] += 1
        st['max.solves_over_hubs'] = max(st['max.solves_over_hubs'], nsol / max(1, len(hubs)))
        st['max.R'] = max(st['max.R'], len(R))
        st['chk.bag_search'] += 1
    return mate


def solve_small(F, b, p):
    n = len(b)
    M = np.zeros((n, n + 1), dtype=np.int64)
    M[:, :n] = F % p
    M[:, n] = np.array(b, dtype=np.int64) % p
    r = 0
    for c in range(n):
        nz = np.nonzero(M[r:, c])[0]
        if not len(nz):
            return None
        k = r + int(nz[0])
        if k != r:
            M[[r, k]] = M[[k, r]]
        M[r] = M[r] * inv(M[r, c], p) % p
        for i in np.nonzero(M[:, c])[0]:
            if i != r:
                M[i] = (M[i] - M[i, c] * M[r]) % p
        r += 1
    return [int(M[i, n]) for i in range(n)]


# ---------------------------------------------------------------- certificate
def odd_components(h, own, rem, st):
    """Odd components of G - rem by the partitions on boundaries, passed up the tree of bags."""
    out, closed = {}, 0
    for b in h.post(h.root):
        par, odd = {}, {}

        def find(x):
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x

        def add(x):
            if x not in par:
                par[x] = x
                odd[x] = 0

        def join(x, y):
            x, y = find(x), find(y)
            if x != y:
                par[x] = y
                odd[y] ^= odd[x]

        for k in h.kids[b]:
            for block, o in out[k]:
                for v in block:
                    add(v)
                r0 = find(block[0])
                odd[r0] ^= o
                for v in block[1:]:
                    join(block[0], v)
        for v in h.members[b]:
            if v not in rem:
                add(v)
                odd[find(v)] ^= 1
        for u, v in own[b]:
            if u not in rem and v not in rem:
                add(u)
                add(v)
                join(u, v)
        blocks = collections.defaultdict(list)
        for v in par:
            blocks[find(v)].append(v)
        res = []
        for r, vs in blocks.items():
            bnd = [v for v in vs if v in h.Qp[b]]
            if bnd:
                res.append((bnd, odd[r]))
            elif odd[r]:
                closed += 1
        out[b] = res
        st['max.partition_words'] = max(st['max.partition_words'], sum(len(x) for x, _ in res))
    return closed


def certificate(h, own, a, E, B, adj, n, msize, st, rng, p=P, mode='ok'):
    N = set(h.home) - set(B)
    z = {d: rng.randrange(p) for d in N}
    rhs = {}
    for v in B:
        t = 0
        for d in adj[v]:
            if d in N:
                t += (a[(v, d)] if v < d else -a[(d, v)]) * z[d]
        rhs[v] = (-t) % p
    y = dict(z)
    if B:
        facts, _, drop = eliminate(h, own, a, h.root, set(B), st, p)
        if drop:
            st['FAIL.basis_singular'] += 1
            return None
        y.update(solve(h, facts, h.root, set(B), rhs, st, p))
    bad = 0
    for x in h.home:
        tot = 0
        for w in adj[x]:
            tot += (a[(x, w)] if x < w else -a[(w, x)]) * y[w]
        bad += int(tot % p != 0)
    st['FAIL.not_null_vector'] += bad
    Dp = {v for v, t in y.items() if t % p}
    Ap = {w for v in Dp for w in adj[v]} - Dp
    if mode == 'emptyA':
        Ap = set()
    odd = odd_components(h, own, Ap, st)
    odd_c = odd_components(h, own, Ap | Dp, st)
    st['chk.certificate'] += 1
    return Dp, Ap, odd, odd_c


# ---------------------------------------------------------------- families, all general planar
def stacked_drop(n, rng, drop):
    faces = [(0, 1, 2), (0, 1, 2)]
    E = {(0, 1), (0, 2), (1, 2)}
    for v in range(3, n):
        i = rng.randrange(len(faces))
        a, b, c = faces[i]
        faces[i] = (a, b, v)
        faces += [(b, c, v), (a, c, v)]
        E |= {(a, v), (b, v), (c, v)}
    return fam.largest(set(range(n)), [e for e in sorted(E) if rng.random() >= drop])


def grid_diag(a, b, rng, drop):
    E = []
    for i in range(a):
        for j in range(b):
            v = i * b + j
            if j + 1 < b and rng.random() >= drop:
                E.append((v, v + 1))
            if i + 1 < a and rng.random() >= drop:
                E.append((v, v + b))
            if i + 1 < a and j + 1 < b and rng.random() < 0.5:
                E.append((v, v + b + 1) if rng.random() < 0.5 else (v + 1, v + b))
    return fam.largest(set(range(a * b)), E)


def wheel(k):
    return set(range(k + 1)), [(0, i) for i in range(1, k + 1)] + [(min(i, i % k + 1), max(i, i % k + 1)) for i in range(1, k + 1)]


def barrier(k, rng):
    """A path of hubs, each with odd pieces hanging: triangles, single vertices and 5-cycles."""
    E, nxt = [(i, i + 1) for i in range(k - 1)], k
    for i in range(k):
        for _ in range(rng.randrange(0, 5)):
            t = rng.randrange(3)
            if t == 0:
                E.append((i, nxt))
                nxt += 1
            elif t == 1:
                E += [(i, nxt), (i, nxt + 1), (nxt, nxt + 1)]
                nxt += 2
            else:
                E += [(i, nxt), (i, nxt + 4), (nxt, nxt + 1), (nxt + 1, nxt + 2), (nxt + 2, nxt + 3), (nxt + 3, nxt + 4)]
                nxt += 5
    return set(range(nxt)), E


def odd_rings(r, s, rng, drop):
    """Concentric odd cycles joined by spokes."""
    s = s + 1 - s % 2
    E = []
    for i in range(r):
        for j in range(s):
            v = i * s + j
            if rng.random() >= drop:
                E.append((v, i * s + (j + 1) % s))
            if i + 1 < r and rng.random() >= drop:
                E.append((v, (i + 1) * s + j))
    return fam.largest(set(range(r * s)), [(min(e), max(e)) for e in E])


def blossom_chain(k, rng):
    """Odd cycles joined by bridges, with pendants: stem and blossom structure for alternating search."""
    E, nxt, last = [], 0, None
    for _ in range(k):
        s = rng.choice([3, 5, 7])
        cyc = list(range(nxt, nxt + s))
        nxt += s
        E += [(cyc[i], cyc[(i + 1) % s]) for i in range(s)]
        if last is not None:
            E.append((last, cyc[0]))
        last = cyc[rng.randrange(s)]
        for c in cyc:
            if rng.random() < 0.2:
                E.append((c, nxt))
                nxt += 1
    return set(range(nxt)), E


def sample(rng, big=False):
    k = rng.randrange(11)
    m = 14 if big else 8
    if k == 0:
        return 'stacked', stacked_drop(rng.randrange(5, 25 * m), rng, rng.choice([0, 0.2, 0.4, 0.6]))
    if k == 1:
        return 'griddiag', grid_diag(rng.randrange(2, m + 2), rng.randrange(2, m + 2), rng, rng.choice([0, 0.15, 0.3]))
    if k == 2:
        return 'wheel', wheel(rng.randrange(3, 10 * m))
    if k == 3:
        return 'barrier', barrier(rng.randrange(1, 3 * m), rng)
    if k == 4:
        return 'rings', odd_rings(rng.randrange(1, m), rng.randrange(3, m + 4), rng, rng.choice([0, 0.1, 0.25]))
    if k == 5:
        return 'blossoms', blossom_chain(rng.randrange(1, 2 * m), rng)
    if k == 6:
        return 'tree', fam.tree(rng.randrange(2, 10 * m), rng, rng.choice([None, 1, 2, 5]))
    if k == 7:
        return 'k2m', fam.k2m(rng.randrange(1, 6 * m), rng)
    if k == 8:
        return 'grid', fam.grid(rng.randrange(2, m + 2), rng.randrange(2, m + 2), rng, rng.choice([0, 0.1, 0.25]))
    if k == 9:
        return 'comb', fam.ladder_comb(rng.randrange(3, 3 * m), rng)
    return 'small', stacked_drop(rng.randrange(3, 11), rng, rng.choice([0.2, 0.4, 0.6]))


# ---------------------------------------------------------------- one instance
def run_one(V, E, h, rng, st, p=P, mode='ok', planar=True, flt=False):
    E = sorted({(min(e), max(e)) for e in E if e[0] != e[1]})
    n = len(V)
    G = nx.Graph()
    G.add_nodes_from(V)
    G.add_edges_from(E)
    if planar and not nx.check_planarity(G)[0]:
        st['FAIL.not_planar'] += 1
    st['chk.planar'] += int(planar)
    adj = {v: sorted(G[v]) for v in V}
    own = assign_edges(h, E, st)
    if {e for es in own.values() for e in map(lambda x: (min(x), max(x)), es)} != set(E):
        st['FAIL.edges_lost'] += 1
    a = {e: (1 if mode == 'unit' else rng.randrange(1, p)) for e in E}
    facts, pivots, dropped = eliminate(h, own, a, h.root, set(V), st, p, mode if mode in ('noretain', 'noschur', 'fltbad') else 'ok', flt)
    if set(pivots) | set(dropped) != set(V) or set(pivots) & set(dropped):
        st['FAIL.not_a_partition'] += 1
    nu = len(nx.max_weight_matching(G, maxcardinality=True))
    r = len(pivots)
    st['chk.rank'] += 1
    st['runs'] += 1
    st['verts'] += n
    if n - 2 * nu:
        st['runs.deficient'] += 1
    if r != 2 * nu:
        st['FAIL.rank'] += 1
    # independent rank of the whole matrix
    if n <= 150:
        idx = {v: i for i, v in enumerate(sorted(V))}
        Mfull = np.zeros((n, n), dtype=np.int64)
        for (u, v), x in a.items():
            Mfull[idx[u], idx[v]] = x % p
            Mfull[idx[v], idx[u]] = (-x) % p
        if rank_mod(Mfull, p) != r:
            st['FAIL.rank_against_full_matrix'] += 1
        st['chk.full_rank'] += 1
    B = set(pivots)
    mate = find_matching(h, own, a, B, adj, st, p, mode if mode in ('nocorr', 'anyedge') else 'ok')
    for x, y in mate.items():
        if mate.get(y) != x or (min(x, y), max(x, y)) not in a:
            st['FAIL.not_a_matching'] += 1
    if len(mate) != r:
        st['FAIL.matching_size'] += 1
    if mode in ('nocorr', 'anyedge', 'noretain', 'noschur', 'fltbad'):
        return
    cert = certificate(h, own, a, E, B, adj, n, len(mate) // 2, st, rng, p, mode)
    if cert is None:
        return
    Dp, Ap, odd, odd_c = cert
    H_ = G.copy()
    H_.remove_nodes_from(Ap)
    odd_nx = sum(1 for c in nx.connected_components(H_) if len(c) % 2)
    if odd_nx != odd:
        st['FAIL.odd_count'] += 1
    # weak duality holds for every set, and the certificate must be tight
    if n - 2 * (len(mate) // 2) < odd_nx - len(Ap):
        st['FAIL.weak_duality'] += 1
    if n - len(mate) != odd - len(Ap) or odd_c:
        st['FAIL.certificate_not_tight'] += 1
    if nx.is_bipartite(G):
        side = nx.bipartite.color(G)
        Cc = set(V) - Dp - Ap
        cover = Ap | {v for v in Cc if side[v] == 0}
        if any(u not in cover and v not in cover for u, v in E):
            st['FAIL.konig_not_cover'] += 1
        if len(cover) != nu:
            st['FAIL.konig_size'] += 1
        st['chk.konig'] += 1
    if n <= 40:
        Dtrue = set()
        for v in V:
            K = G.copy()
            K.remove_node(v)
            if len(nx.max_weight_matching(K, maxcardinality=True)) == nu:
                Dtrue.add(v)
        if Dtrue != Dp:
            st['FAIL.gallai_edmonds_D'] += 1
        st['chk.gallai_edmonds'] += 1


def lane(seed, secs, big=False):
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    while time.time() - t0 < secs:
        name, (V, E) = sample(rng, big)
        if len(V) < 2:
            continue
        root, bags = mm.build(V, E, rng, leaf=rng.choice([2, 4, 6, 10, 16]), closure=rng.choice([False, True, 'two']))
        h = from_mm(root, bags)
        st['fam.' + name] += 1
        st['max.n'] = max(st['max.n'], len(V))
        run_one(V, E, h, rng, st)
    return dict(st)


def tiny_lane(seed, secs):
    """Section 5 at tiny p, where wrong runs are frequent. A pass of (a) and (b) must be right, against brute force."""
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    while time.time() - t0 < secs:
        name, (V, E) = sample(rng, False)
        if not 2 <= len(V) <= 40:
            continue
        root, bags = mm.build(V, E, rng, leaf=rng.choice([2, 4, 6, 10]), closure=rng.choice([False, True, 'two']))
        h = from_mm(root, bags)
        p = rng.choice([3, 5, 7, 11, 13, 31, 101, 1009])
        E = sorted({(min(e), max(e)) for e in E if e[0] != e[1]})
        G = nx.Graph()
        G.add_nodes_from(V)
        G.add_edges_from(E)
        adj = {v: sorted(G[v]) for v in V}
        own = assign_edges(h, E, st)
        a = {e: rng.randrange(1, p) for e in E}
        _, piv, _ = eliminate(h, own, a, h.root, set(V), st, p)
        mate = find_matching(h, own, a, set(piv), adj, st, p)
        for x, y in mate.items():
            if mate.get(y) != x or (min(x, y), max(x, y)) not in a:
                st['FAIL.not_a_matching'] += 1
        if len(mate) != len(piv):
            st['FAIL.matching_size'] += 1
        Dp, Ap, odd, odd_c = certificate(h, own, a, E, set(piv), adj, len(V), len(mate) // 2, st, rng, p)
        nu = len(nx.max_weight_matching(G, maxcardinality=True))
        Dt = set()
        for v in V:
            K = G.copy()
            K.remove_node(v)
            if len(nx.max_weight_matching(K, maxcardinality=True)) == nu:
                Dt.add(v)
        right = len(mate) == 2 * nu and Dp == Dt
        pa = len(V) - len(mate) == odd - len(Ap)
        st['runs'] += 1
        st['verts'] += len(V)
        st['tiny.right'] += int(right)
        st['tiny.pass_a'] += int(pa)
        st['tiny.pass'] += int(pa and not odd_c)
        st['tiny.a_only_wrong_D'] += int(pa and Dp != Dt)
        st['tiny.not_maximum'] += int(len(mate) != 2 * nu)
        if pa and len(mate) != 2 * nu:
            st['FAIL.pass_a_not_maximum'] += 1
        if pa and not odd_c and not right:
            st['FAIL.pass_wrong'] += 1
        if right and not (pa and not odd_c):
            st['FAIL.rejects_truth'] += 1
    return {k: int(v) for k, v in st.items()}


def controls(seed, secs):
    out = {}
    for mode in ('noretain', 'noschur', 'nocorr', 'anyedge', 'unit', 'emptyA', 'p3', 'p5'):
        rng = random.Random(seed)
        st = collections.Counter()
        t0 = time.time()
        p = {'p3': 3, 'p5': 5}.get(mode, P)
        m = 'ok' if mode in ('p3', 'p5') else mode
        while time.time() - t0 < secs:
            name, (V, E) = sample(rng, False)
            if len(V) < 2:
                continue
            root, bags = mm.build(V, E, rng, leaf=rng.choice([2, 4, 6, 10]), closure=rng.choice([False, True, 'two']))
            h = from_mm(root, bags)
            run_one(V, E, h, rng, st, p, m)
        out[mode] = {k: int(v) for k, v in st.items() if k.startswith('FAIL') or k == 'runs'}
    return out


# ---------------------------------------------------------------- low treewidth, Section 6
def partial_ktree(n, k, rng, drop):
    n = max(n, k + 2)
    E, cliques = set(), [tuple(range(k + 1))]
    for i in range(k + 1):
        for j in range(i):
            E.add((j, i))
    for v in range(k + 1, n):
        c = rng.choice(cliques)
        sub = rng.sample(c, k)
        for u in sub:
            E.add((min(u, v), max(u, v)))
        cliques.append(tuple(sub) + (v,))
    return fam.largest(set(range(n)), [e for e in sorted(E) if rng.random() >= drop])


def hub_pieces(k, m, rng):
    """k hubs and many small odd or even pieces, each joined to several hubs: many children of one bag."""
    E, nxt = [(i, i + 1) for i in range(k - 1)], k
    for _ in range(m):
        t = rng.randrange(1, 5)
        ps = list(range(nxt, nxt + t))
        nxt += t
        E += [(ps[i], ps[i + 1]) for i in range(t - 1)]
        for h_ in rng.sample(range(k), rng.randrange(1, k + 1)):
            E.append((h_, rng.choice(ps)))
    return fam.largest(set(range(nxt)), [(min(e), max(e)) for e in E])


def build_tw(V, E, rng, leaf, width):
    """The strategy of arXiv:2205.14897, Section 3: S from the part G', children are components of G' - S with
    their edges to the bag. A leaf holds all its vertices."""
    adj = {v: set() for v in V}
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    Vs, Ss, kids, parent, depth, cnt = {}, {}, {}, {}, {}, [0]
    stack = [(set(V), set(), None, 0)]
    while stack:
        part, bp, par, d = stack.pop()
        b = cnt[0]
        cnt[0] += 1
        Vs[b] = part | {u for u in bp if adj[u] & part}
        parent[b], depth[b], kids[b] = par, d, []
        if par is not None:
            kids[par].append(b)
        if len(part) <= leaf:
            Ss[b] = set(part)
            continue
        deg = sorted(part, key=lambda v: (-len(adj[v] & part), rng.random()))
        S = set(deg[:rng.randrange(1, width + 1)])
        Ss[b] = S
        B = (bp & Vs[b]) | S
        seen = set(S)
        for r in sorted(part - S):
            if r in seen:
                continue
            seen.add(r)
            comp, st_ = {r}, [r]
            while st_:
                x = st_.pop()
                for y in adj[x] & part:
                    if y not in seen:
                        seen.add(y)
                        comp.add(y)
                        st_.append(y)
            stack.append((comp, B, b, d + 1))
    return H(Vs, Ss, kids, parent, depth, 0)


def sample_tw(rng):
    k = rng.randrange(4)
    if k == 0:
        return 'ktree', partial_ktree(rng.randrange(6, 90), rng.randrange(1, 7), rng, rng.choice([0, 0.2, 0.5]))
    if k == 1:
        return 'hubs', hub_pieces(rng.randrange(1, 9), rng.randrange(1, 40), rng)
    if k == 2:
        return 'k2m', fam.k2m(rng.randrange(1, 60), rng)
    return 'stacked', stacked_drop(rng.randrange(5, 80), rng, rng.choice([0, 0.3, 0.6]))


def tw_lane(seed, secs, mode='ok'):
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    while time.time() - t0 < secs:
        name, (V, E) = sample_tw(rng)
        if len(V) < 2:
            continue
        h = build_tw(V, E, rng, rng.choice([1, 2, 4, 8]), rng.choice([1, 2, 3, 6]))
        st['fam.' + name] += 1
        st['max.n'] = max(st['max.n'], len(V))
        st['max.bag_B'] = max(st['max.bag_B'], max(len(h.V[b] & (h.Qp[b] | h.S[b])) for b in h.V))
        st['max.children'] = max(st['max.children'], max(len(x) for x in h.kids.values()))
        run_one(V, E, h, rng, st, P, mode, planar=False, flt=True)
    return {k: int(v) for k, v in st.items()}


# ---------------------------------------------------------------- disjoint paths, Section 6
def quad(h):
    """Each vertex hosts four: out 4v, in 4v+1, a 4v+2, z 4v+3. Bags, separators and the tree stay."""
    f = lambda vs: {4 * v + i for v in vs for i in range(4)}
    return H({b: f(x) for b, x in h.V.items()}, {b: f(x) for b, x in h.S.items()}, h.kids, h.parent, h.depth, h.root)


def paths_one(V, arcs, s_, t_, h, rng, st, wrong=False):
    Vp = set(V) - {s_, t_}
    E = {(4 * v, 4 * v + 1) for v in Vp}
    for u, v in arcs:
        if u in Vp and v in Vp:
            E.add((4 * u, 4 * v + 1))
        elif u == s_ and v in Vp:
            E.add((4 * v + 1, 4 * v + 2))
        elif v == t_ and u in Vp:
            E.add((4 * u, 4 * u + 3))
    Es = sorted({(min(e), max(e)) for e in E})
    # every copy is a vertex of the hierarchy; isolated ones have no effect on the matching
    h4 = quad(h)
    Vq = {4 * v + i for v in V for i in range(4)}
    G = nx.Graph()
    G.add_nodes_from(Vq)
    G.add_edges_from(Es)
    a = {e: rng.randrange(1, P) for e in Es}
    own = assign_edges(h4, Es, st)
    adj = {v: sorted(G[v]) for v in Vq}
    _, piv, _ = eliminate(h4, own, a, h4.root, Vq, st, P, 'ok', True)
    mate = find_matching(h4, own, a, set(piv), adj, st, P)
    for x, y in mate.items():
        if mate.get(y) != x or (min(x, y), max(x, y)) not in a:
            st['FAIL.not_a_matching'] += 1
    kappa = len(mate) // 2 - len(Vp) - (1 if wrong else 0)
    # independent value: unit vertex capacities on a split digraph
    D = nx.DiGraph()
    for v in Vp:
        D.add_edge((v, 0), (v, 1), capacity=1)
    for u, v in arcs:
        if u == s_ and v in Vp:
            D.add_edge('s', (v, 0), capacity=1)
        elif v == t_ and u in Vp:
            D.add_edge((u, 1), 't', capacity=1)
        elif u in Vp and v in Vp:
            D.add_edge((u, 1), (v, 0), capacity=1)
    D.add_node('s')
    D.add_node('t')
    val = nx.maximum_flow_value(D, 's', 't')
    st['chk.paths'] += 1
    st['max.kappa'] = max(st['max.kappa'], val)
    if kappa != val:
        st['FAIL.paths_value'] += 1
    # arcs of the matching form paths and cycles; a path counts if it uses a at its start and z at its end
    succ, pred = {}, {}
    for u in Vp:
        y = mate.get(4 * u)
        if y is not None and y % 4 == 1 and y // 4 != u:
            succ[u], pred[y // 4] = y // 4, u
    real, none_ = 0, 0
    for x in Vp:
        if x in pred:
            continue
        y = x
        while y in succ:
            y = succ[y]
        if x == y and mate.get(4 * x) == 4 * x + 1:
            continue                                    # self edge
        ha, hz = mate.get(4 * x + 1) == 4 * x + 2, mate.get(4 * y) == 4 * y + 3
        real += int(ha and hz)
        none_ += int(not ha and not hz)
    if real != val:
        st['FAIL.paths_real'] += 1
    if none_:
        st['FAIL.paths_with_no_end'] += 1
    # the separating set of Section 6.1, from the cover of Koenig on H
    if (s_, t_) in arcs:
        return
    cert = certificate(h4, own, a, Es, set(piv), adj, len(Vq), len(mate) // 2, st, rng, P)
    if cert is None:
        return
    Dp, Ap, _, _ = cert
    cover = Ap | {x for x in Vq - Dp - Ap if x % 4 in (0, 2)}
    if any(x not in cover and y not in cover for x, y in Es):
        st['FAIL.sep_not_cover'] += 1
    if len(cover & {4 * v + i for v in Vp for i in range(4)}) != len(Vp) + val:
        st['FAIL.sep_cover_size'] += 1
    both = {v for v in Vp if 4 * v in cover and 4 * v + 1 in cover}
    Sp = both | {v for v in Vp if 4 * v + 2 in cover or 4 * v + 3 in cover}
    Dg = nx.DiGraph()
    Dg.add_nodes_from(V)
    Dg.add_edges_from(arcs)
    def cut(R):
        K = Dg.copy()
        K.remove_nodes_from(R)
        return not nx.has_path(K, s_, t_)
    st['chk.sep'] += 1
    if len(Sp) != val:
        st['FAIL.sep_size'] += 1
    if not cut(Sp):
        st['FAIL.sep_not_separating'] += 1
    st['ctl.sep_extra_copy_used'] += int(Sp != both)
    st['ctl.sep_both_only_fails'] += int(not cut(both))


def paths_lane(seed, secs, wrong=False):
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    while time.time() - t0 < secs:
        name, (V, E) = sample_tw(rng) if rng.random() < 0.5 else sample(rng, False)
        if len(V) < 3:
            continue
        h = build_tw(V, E, rng, rng.choice([1, 2, 4]), rng.choice([1, 2, 3, 6]))
        arcs = []
        p_ = rng.choice([0.5, 0.8, 1.0])
        for u, v in E:
            if rng.random() < p_:
                arcs.append((u, v))
            if rng.random() < p_:
                arcs.append((v, u))
        s_, t_ = rng.sample(sorted(V), 2)
        paths_one(V, arcs, s_, t_, h, rng, st, wrong)
        st['runs'] += 1
        st['max.n'] = max(st['max.n'], len(V))
    return {k: int(v) for k, v in st.items()}


# ---------------------------------------------------------------- region bags
def region_setup():
    rp = os.environ.get('SSSP_REPO') or os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ExactShortestPathsAndFlowsOnPlanarGraphs')
    sys.path.insert(0, os.path.join(rp, 'sim', 'diameter'))
    import diam
    return diam


def from_region(eng):
    V, S, kids, parent, depth = {}, {}, {}, {}, {}
    for b, B in eng.bags.items():
        V[b] = set(B['X'])
        ks = B.get('kids') or []
        kids[b] = list(ks)
        S[b] = set(B['q']) if ks else set(B['X'])
        parent[b] = B['parent'] if b != 0 else None
        depth[b] = B['depth']
    return H(V, S, kids, parent, depth, 0)


def region_instance(diam, s, rng, big, drop=None):
    r = diam.instance(s, big, rng)
    if r is None:
        return None
    g, name = r
    if not nx.is_connected(g.G):
        return None
    root = rng.randrange(g.n)
    eng = diam.Bags(g, diam.virtual_candidates(g.pos, g.ends), random.Random(s + 1),
                    dict(leaf=rng.choice([6, 8, 14]), tries=30, modes={'bal': 1.0}, zall=0.0, swap=0.3,
                         degenerate=False, txmode='bfs', stop=True, root=root))
    eng.run()
    return g, name, eng


def region_lane(seed, secs, big=False):
    diam = region_setup()
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    s = seed * 1000
    while time.time() - t0 < secs:
        s += 1
        r = region_instance(diam, s, rng, big)
        if r is None:
            continue
        g, name, eng = r
        h = from_region(eng)
        full = sorted((min(int(u), int(v)), max(int(u), int(v))) for u, v in g.ends)
        V = set(range(g.n))
        # drop edges to vary the deficiency; bags stay valid only for subgraphs of the region graphs
        p_drop = rng.choice([0, 0.3, 0.5, 0.7])
        E = [e for e in full if rng.random() >= p_drop]
        G = nx.Graph()
        G.add_nodes_from(V)
        G.add_edges_from(E)
        st['fam.' + name] += 1
        st['max.n'] = max(st['max.n'], g.n)
        hier_checks(h, full, st)
        run_one(V, E, h, rng, st)
    return dict(st)


def hier_checks(h, E, st):
    """The part of (H1) to (H4) that the round count of the note uses."""
    for b, vs in h.V.items():
        ks = h.kids[b]
        if not ks:
            continue
        cnt = collections.Counter(v for k in ks for v in h.V[k])
        for v in vs:
            if v in h.S[b]:
                if cnt[v] > 3:
                    st['FAIL.hub_in_more_than_3_children'] += 1
            elif cnt[v] != 1:
                st['FAIL.vertex_not_in_one_child'] += 1
        st['chk.hier'] += 1
        Q = h.Qp[b] | h.S[b]
        tot = sum(len(h.V[k] & Q) for k in ks)
        st['max.sum_boundary_over_Q'] = max(st['max.sum_boundary_over_Q'], round(tot / max(1, len(Q)), 3))


def scale():
    diam = region_setup()
    from geo import FAMS, drawing_ok
    rows = []
    for k in (6, 10, 14, 18, 24, 30):
        rng = random.Random(k)
        pos, E = FAMS['grid'](k, dict(k=k))
        g = diam.PG(pos, E, seed=k)
        eng = diam.Bags(g, diam.virtual_candidates(g.pos, g.ends), random.Random(k + 1),
                        dict(leaf=8, tries=30, modes={'bal': 1.0}, zall=0.0, swap=0.3,
                             degenerate=False, txmode='bfs', stop=True, root=0))
        eng.run()
        h = from_region(eng)
        st = collections.Counter()
        E2 = sorted((min(int(u), int(v)), max(int(u), int(v))) for u, v in g.ends)
        G = nx.Graph(E2)
        D = nx.diameter(G)
        run_one(set(range(g.n)), E2, h, rng, st)
        rows.append(dict(k=k, n=g.n, D=D, words=st['max.words_in_bag'], words_over_D2=round(st['max.words_in_bag'] / D ** 2, 2),
                         solve_words=st['max.solve_words'], hubs=st['max.hubs'], R=st['max.R'], retained=st['max.retained'],
                         fails=sum(v for w, v in st.items() if w.startswith('FAIL'))))
    return rows


if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == 'ctl':
        print(json.dumps(controls(int(a[1]), float(a[2])), indent=0, sort_keys=True))
    elif a[0] == 'region':
        print(json.dumps(region_lane(int(a[1]), float(a[2]), len(a) > 3), indent=0, sort_keys=True))
    elif a[0] == 'tw':
        print(json.dumps(tw_lane(int(a[1]), float(a[2])), indent=0, sort_keys=True))
    elif a[0] == 'twctl':
        r = tw_lane(int(a[1]), float(a[2]), 'fltbad')
        print(json.dumps({k: v for k, v in r.items() if k.startswith('FAIL') or k == 'runs'}, sort_keys=True))
    elif a[0] == 'paths':
        print(json.dumps(paths_lane(int(a[1]), float(a[2])), indent=0, sort_keys=True))
        r = paths_lane(int(a[1]) + 1, min(10.0, float(a[2])), True)
        print('control, count off by one:', json.dumps({k: v for k, v in r.items() if k.startswith('FAIL') or k == 'runs'}, sort_keys=True))
    elif a[0] == 'tiny':
        print(json.dumps(tiny_lane(int(a[1]), float(a[2])), indent=0, sort_keys=True))
    elif a[0] == 'scale':
        for row in scale():
            print(json.dumps(row))
    else:
        print(json.dumps(lane(int(a[0]), float(a[1]), len(a) > 2), indent=0, sort_keys=True))
