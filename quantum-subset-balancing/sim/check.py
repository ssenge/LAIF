"""Tests the combinatorial steps on real instances over [-d:d], with the quantum searches replaced by exhaustive classical
ones: every equal-sum pair is a real solution, X != Y, the representations of a minimum-support solution have distinct
sums, and working residues exist under the cap. It checks the construction, not any quantum speedup."""
import math, random
from collections import Counter
from itertools import product
import numpy as np
from opt import Scheme, wide_labels, profile


def is_prime(m):
    return m > 1 and all(m % p for p in range(2, int(m**.5) + 1))


def round_row(masses, total):
    """Integers summing to total, within 1 of the masses scaled to total."""
    s = sum(masses)
    raw = [m/s*total for m in masses] if s > 0 else [0.0]*len(masses)
    out = [int(r) for r in raw]
    for i in sorted(range(len(raw)), key=lambda i: out[i] - raw[i])[:total - sum(out)]:
        out[i] += 1
    return out


def table(S, q, D):
    """Integer counts of (L, x, y) per coordinate value c of D, following the kernel of q."""
    counts = Counter(D)
    nu = {}
    for c, m in counts.items():
        cells = np.where(S.c == c)[0]
        for i, k in zip(cells, round_row(list(q[cells]), m)):
            nu[i] = k
    return nu


def perms(multi):
    """All distinct arrangements of a multiset given as {symbol: count}."""
    keys = sorted(multi)
    n = sum(multi.values())
    def rec(left, cur):
        if len(cur) == n:
            yield tuple(cur)
            return
        for k in keys:
            if left[k]:
                left[k] -= 1
                cur.append(k)
                yield from rec(left, cur)
                cur.pop()
                left[k] += 1
    yield from rec(dict(multi), [])


def lists(S, nu, D, y, rng, pin):
    """Assign coordinates to labels as a good partition, then build the typed lists X and Y. The pinned coordinate
    carries D[pin] in every X and 0 in every Y, and has no label."""
    lab_of, plant_x, plant_y, reps = {}, {}, {}, 1
    by_c = {}
    for i, c in enumerate(D):
        if i != pin:
            by_c.setdefault(c, []).append(i)
    for c, idx in by_c.items():
        rng.shuffle(idx)
        it = iter(idx)
        groups = {}
        for cell, k in nu.items():
            if S.c[cell] == c:
                for _ in range(k):
                    i = next(it)
                    lab_of[i] = S.L[cell]
                    plant_x[i], plant_y[i] = S.x[cell], S.y[cell]
                    groups.setdefault(S.L[cell], []).append(k)
    coords = {}
    for i, L in lab_of.items():
        coords.setdefault(L, []).append(i)
    tx = {L: Counter(int(plant_x[i]) for i in I) for L, I in coords.items()}
    ty = {L: Counter(int(plant_y[i]) for i in I) for L, I in coords.items()}
    def build(types, at_pin):
        parts = [[(I, p) for p in perms(types[L])] for L, I in sorted(coords.items())]
        for choice in product(*parts):
            vec = [0]*len(D)
            vec[pin] = at_pin
            for I, p in choice:
                for i, v in zip(I, p):
                    vec[i] = v
            yield sum(a*b for a, b in zip(vec, y)), tuple(vec)
    return list(build(tx, D[pin])), list(build(ty, 0)), (tx, ty, coords)


def in_R(S, nu, coords, X, D):
    """The joint counts of (x, y) on each label of the pair (X, X - D) equal the layout, as in the definition of R."""
    want = Counter({(int(S.L[c]), int(S.x[c]), int(S.y[c])): k for c, k in nu.items() if k})
    have = Counter((int(L), X[i], X[i] - D[i]) for L, I in coords.items() for i in I)
    return want == have


def varying(S, nu):
    """Size of F: coordinates in classes (L, c) with at least two positive counts."""
    classes = {}
    for cell, k in nu.items():
        if k:
            classes.setdefault((S.L[cell], S.c[cell]), []).append(k)
    return sum(sum(v) for v in classes.values() if len(v) > 1)


def min_support(y, d):
    h = len(y)//2
    left = {}
    for e in product(range(-d, d + 1), repeat=h):
        v, s = sum(a*b for a, b in zip(e, y)), sum(1 for a in e if a)
        if s:
            left[v] = min(s, left.get(v, 99))
        left.setdefault(v, 99)
    left[0] = min(left.get(0, 99), 0 + left.get(0, 99))
    best = 99
    zero_left = 0
    for e in product(range(-d, d + 1), repeat=len(y) - h):
        v, s = sum(a*b for a, b in zip(e, y[h:])), sum(1 for a in e if a)
        if s and v == 0:
            best = min(best, s)
        if -v in left and left[-v] < 99:
            best = min(best, s + left[-v])
    return best


def primes_near(m, count, rng):
    """Up to count distinct random primes of [m, 2m]."""
    pool = [p for p in range(m, 2*m + 1) if is_prime(p)]
    return rng.sample(pool, min(count, len(pool)))


def run(d, n, w, q, S, seed, st, heavy=False):
    """heavy puts pairs (g, (d + 1) g) on the coordinates: these give many equal sums inside the lists, since a difference
    with entries (d + 1, -1) is outside the coefficient set, and no solution by themselves."""
    rng = random.Random(seed)
    pi = profile(d, w)
    D = []
    for c, m in zip([0] + [x for k in range(1, d + 1) for x in (k, -k)], [w[0]] + [w[k]/2 for k in range(1, d + 1) for _ in (0, 1)]):
        D += [c]*round(m*n)
    D = (D + [0]*n)[:n]
    if len(set(D)) < 2:
        return
    y = [rng.getrandbits(3*n) for _ in range(n)]
    pivot = next(i for i in range(n) if D[i] in (1, -1)) if any(abs(c) == 1 for c in D) else None
    if pivot is None:
        st["no unit coefficient"] += 1
        return
    if heavy:
        rest = [i for i in range(n) if i != pivot]
        rng.shuffle(rest)
        for a, b in zip(rest[::2], rest[1::2]):
            g = rng.getrandbits(2*n)
            y[a], y[b] = g, (d + 1)*g
    y[pivot] = 0
    y[pivot] = -D[pivot]*sum(a*b for a, b in zip(D, y))
    order = list(range(n))
    rng.shuffle(order)
    y, D = [y[i] for i in order], [D[i] for i in order]
    assert sum(a*b for a, b in zip(D, y)) == 0
    supp = sum(1 for c in D if c)
    if min_support(y, d) != supp:
        st["discarded, smaller solution"] += 1
        return
    pin = rng.choice([i for i in range(n) if D[i]])
    nu = table(S, q, D[:pin] + D[pin + 1:])
    X, Y, (tx, ty, coords) = lists(S, nu, D, y, rng, pin)
    if not X or not Y or len(X)*len(Y) > 4e9:
        st["skipped, too large"] += 1
        return
    st["runs"] += 1
    st["max list"] = max(st["max list"], len(X), len(Y))
    sx = {}
    for v, t in X:
        sx.setdefault(v, []).append(t)
    checked = 0
    for v, t in Y:
        for u in sx.get(v, ()):
            dif = [a - b for a, b in zip(u, t)]
            assert all(-d <= e <= d for e in dif), "difference outside the coefficient set"
            assert any(dif), "X == Y despite the pin"
            checked += 1
    st["pairs verified"] += checked
    # representations of D: every (X, Y) in the lists with X - Y = D
    Yset = {t for _, t in Y}
    vals = []
    for v, t in X:
        other = tuple(a - c for a, c in zip(t, D))
        if other in Yset and in_R(S, nu, coords, t, D):
            vals.append(v)
    st["reps"] += len(vals)
    assert vals, "no representation of the planted solution"
    if len(vals) != len(set(vals)):
        assert varying(S, nu) >= supp, "two representations with equal sums while |F| < |supp D|"
        st["equal sums with |F| >= |supp D|"] += 1
    K = len(vals)
    U = max(len(X), len(Y))
    for P in primes_near(max(5, K), 8, rng):
        bx, by = {}, {}
        for v, t in X:
            bx.setdefault(v % P, []).append(v)
        for v, t in Y:
            by.setdefault(v % P, []).append(v)
        T = 4*n*U//P + 1 if not heavy else max(1, U//P)
        good = sum(1 for r in {v % P for v in vals} if set(bx[r][:T]) & set(by[r][:T]))
        for v in set(vals):         # Lemma 4 on any window: few other sums in both bins put an element of sum v in both windows
            bin_x, bin_y = bx[v % P], by[v % P]
            if 2*sum(u != v for u in bin_x) <= T and 2*sum(u != v for u in bin_y) <= T:
                assert v in bin_x[:T] and v in bin_y[:T], "the cap lost the representation"
                st["cap cases"] += 1
        st["capped bins"] += sum(len(b) > T for b in bx.values()) + sum(len(b) > T for b in by.values())
        st["primes"] += 1
        st["primes with a working residue"] += good >= 1
        st["working residues"] += good


def planted_vector(d, n, w, rng):
    D = []
    for c, m in zip([0] + [x for k in range(1, d + 1) for x in (k, -k)], [w[0]] + [w[k]/2 for k in range(1, d + 1) for _ in (0, 1)]):
        D += [c]*round(m*n)
    D = (D + [0]*n)[:n]
    rng.shuffle(D)
    return D


def run_exchange(d, n, w, q, S, seed, st):
    """The converse side of Lemma 2. Plant a second dependency equal to the difference E = X - X' of two representations,
    so that two representations have equal sums. Then E must lie in [-d:d]^n, with support in F, and must be a real
    solution. Here D need not have minimum support, which is the case Lemma 2 excludes."""
    rng = random.Random(seed)
    D = planted_vector(d, n, w, rng)
    if not any(D):
        return
    pin = rng.choice([i for i in range(n) if D[i]])
    nu = table(S, q, D[:pin] + D[pin + 1:])
    y = [0]*n
    X, Y, (tx, ty, coords) = lists(S, nu, D, y, rng, pin)
    if len(X)*len(Y) > 4e9:
        return
    Yset = {t for _, t in Y}
    reps = [t for _, t in X if tuple(a - c for a, c in zip(t, D)) in Yset and in_R(S, nu, coords, t, D)]
    assert reps, "no representation of the planted solution"
    if len(reps) < 2:
        st["fewer than two representations"] += 1
        return
    A, B = rng.sample(reps, 2)
    E = [a - b for a, b in zip(A, B)]
    assert any(E) and all(abs(e) <= d for e in E), "exchange outside the coefficient set"
    lab = {i: L for L, I in coords.items() for i in I}
    pos = {}
    for cell, k in nu.items():
        if k:
            pos.setdefault((S.L[cell], S.c[cell]), []).append(k)
    F = {i for i in lab if len(pos[lab[i], D[i]]) > 1}
    assert all(i in F for i, e in enumerate(E) if e), "exchange outside F"
    assert not E[pin]
    p = next(i for i, e in enumerate(E) if e)
    r = next(i for i, c in enumerate(D) if c and not E[i])      # the pin qualifies
    m = (E[p]*D[r])**2
    y = [m*rng.getrandbits(3*n) for _ in range(n)]
    y[p] = y[r] = 0
    y[p] = -sum(a*b for a, b in zip(E, y))//E[p]
    y[r] = -sum(a*b for a, b in zip(D, y))//D[r]
    assert sum(a*b for a, b in zip(E, y)) == 0 and sum(a*b for a, b in zip(D, y)) == 0
    assert sum(a*b for a, b in zip(A, y)) == sum(a*b for a, b in zip(B, y))
    assert varying(S, nu) >= sum(1 for e in E if e)
    assert min_support(y, d) <= sum(1 for e in E if e)
    st["equal sums planted"] += 1


if __name__ == "__main__":
    cases = [(2, [1/5, 2/5, 2/5]), (2, [.1377, .2962, .5661]), (2, [.3, .4, .3]), (3, [1/7, 2/7, 2/7, 2/7]), (3, [.0942, .1897, .2343, .4818]), (3, [.3, .3, .2, .2])]
    for d, w in cases:
        S = Scheme(d, wide_labels(d))
        v, q = S.solve(profile(d, w), starts=4)
        print(f"d={d} w={[round(x, 3) for x in w]} L={v:.4f} margin={S.support_margin(q, profile(d, w)):.3f}", flush=True)
        for heavy in (False, True):
            for n in (8, 10, 12):
                st = Counter()
                for seed in range(12):
                    run(d, n, w, q, S, 1000*n + seed, st, heavy)
                print(f"  n={n} {'heavy' if heavy else 'random'} {dict(st)}", flush=True)
        st = Counter()
        for seed in range(40):
            run_exchange(d, 12, w, q, S, seed, st)
        print(f"  n=12 exchange {dict(st)}", flush=True)
