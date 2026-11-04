"""Proposition and Lemma 4 of notes/DOMINATORS.md, all path choices at every problem, overwrite rule, by vertex removal. No repo code, no planarity needed.
python3 -I -B prop.py N [SAMPLES SEED]"""
import itertools, json, random, sys
sys.setrecursionlimit(10000)


def reach(arcs, src, allowed):
    seen = {s for s in src if s in allowed}
    st = list(seen)
    while st:
        u = st.pop()
        for v in arcs[u]:
            if v in allowed and v not in seen:
                seen.add(v)
                st.append(v)
    return seen


def paths(z, Q, arcs):
    stack = [[z]]
    while stack:
        p = stack.pop()
        yield p
        for v in arcs[p[-1]]:
            if v in Q and v not in p:
                stack.append(p + [v])


def truth(Q, E, arcs):
    doms = {y: set() for y in Q}
    for w in Q:
        got = reach(arcs, E - {w}, Q - {w})
        for y in Q - got - {w}:
            doms[y].add(w)
    return {y: (max(doms[y], key=lambda d: len(doms[d])) if doms[y] else None) for y in Q}


class Ctx:
    def __init__(self, arcs):
        self.arcs = arcs
        self.memo = {}
        self.cases = 0
        self.fail = 0
        self.bad = None

    def solve(self, Q, E, z):
        key = (frozenset(Q), frozenset(E), z)
        if key in self.memo:
            return self.memo[key]
        arcs = self.arcs
        true = truth(Q, E, arcs)
        self.memo[key] = true
        for R in paths(z, Q, arcs):
            self.cases += 1
            O = Q - set(R)
            # last dominator on R, by removal only
            last = {y: None for y in Q}
            for j, p in enumerate(R):
                got = reach(arcs, E - {p}, Q - {p})
                for y in Q - got - {p}:
                    last[y] = p
            # classes
            k = len(R)
            key_h = {}
            for i, p in enumerate(R):
                for h in arcs[p]:
                    if h in O:
                        key_h[h] = (k - i, h)      # later arcs overwrite, so the greatest index gives the least first coordinate
            left, final = set(O), dict(last)
            for h in sorted(key_h, key=key_h.get):
                if h not in left:
                    continue
                K = reach(arcs, [h], left)
                left -= K
                EK = {v for v in K if v in E or any(v in arcs[u] for u in Q - K)}
                if h not in EK:
                    self.fail += 1
                sub = self.solve(K, EK, h)
                for y in K:
                    if sub[y] is not None:
                        final[y] = sub[y]
            if left:
                self.fail += 1
            if final != true:
                self.fail += 1
                self.bad = (sorted(Q), sorted(E), R)
        return true


def main():
    n = int(sys.argv[1])
    pairs = [(u, v) for u in range(n) for v in range(n) if u != v]
    tot = cases = fail = 0
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    it = range(1 << len(pairs)) if len(sys.argv) <= 2 else (rng.getrandbits(len(pairs)) & rng.getrandbits(len(pairs)) for _ in range(int(sys.argv[2])))
    for mask in it:
        arcs = {u: [] for u in range(n)}
        for b, (u, v) in enumerate(pairs):
            if mask >> b & 1:
                arcs[u].append(v)
        c = Ctx(arcs)
        for r in range(n):
            Q = reach(arcs, [r], set(range(n)))
            c.solve(Q, {r}, r)
        tot += 1
        cases += c.cases
        fail += c.fail
        if c.fail and fail < 5:
            print('FAIL', arcs, c.bad)
    print(json.dumps({'n': n, 'digraphs': tot, 'path_choices': cases, 'fail': fail}))


main()
