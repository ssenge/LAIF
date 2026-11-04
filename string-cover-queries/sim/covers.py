"""Shortest cover and all covers of a string with Õ(sqrt n) queries. The algorithm of ../README.md.

Q counts queries: one per character read, and for a search the applications of BBHT sampled from the exact Grover
law, stopping after budget * sqrt(N). The outer search over blocks is charged a fixed cost per application,
pred_cap, since a device must fix it in advance. Its marked set comes from the simulator's own knowledge of the
string, and check.py tests that against the inner algorithm. No circuits here; see qiskit_check.py.
Limits: statistical, and costs on these families carry no guarantee beyond ../README.md.
"""
import math
from dataclasses import dataclass
import numpy as np


class Q:
    def __init__(self, s, rng, budget=16):
        self.s, self.rng, self.budget = np.asarray(s), rng, budget
        self.n = len(s)
        self.spent = 0
        self._z = None

    def read(self, i):
        self.spent += 1
        return self.s[i]

    def search(self, marked, w=2):
        """BBHT on a boolean array, w queries per application. Returns a uniformly random marked index, or None."""
        N = marked.size
        if N == 0:
            return None
        hits = np.flatnonzero(marked)
        t = len(hits)
        if N <= 16:  # reading a tiny set costs less than the budget, and cannot fail
            self.spent += N * w
            return int(hits[self.rng.integers(t)]) if t else None
        theta = math.asin(math.sqrt(t / N))
        limit = self.budget * math.sqrt(N)
        m, used = 1.0, 0
        while used <= limit:
            j = int(self.rng.integers(0, int(m)))
            used += 2 * j + 1
            if t and self.rng.random() < math.sin((2 * j + 1) * theta) ** 2:
                self.spent += used * w
                return int(hits[self.rng.integers(t)])
            m = min(m * 8 / 7, math.sqrt(N) + 1)
        self.spent += used * w
        return None

    def first(self, marked, w=2):
        """Durr-Hoyer: the smallest marked index, or None."""
        cur = self.search(marked, w)
        if cur is None:
            return None
        while True:
            k = self.search(marked[:cur], w)
            if k is None:
                return cur
            cur = k

    def last(self, marked, w=2):
        k = self.first(marked[::-1], w)
        return None if k is None else marked.size - 1 - k

    def z(self):
        """Simulator's knowledge, no queries: z[i] is the longest common prefix of s and s[i:]."""
        if self._z is None:
            s, n = self.s, self.n
            z = [0] * n
            z[0] = n
            l = r = 0
            for i in range(1, n):
                k = min(r - i, z[i - l]) if i < r else 0
                while i + k < n and s[k] == s[i + k]:
                    k += 1
                z[i] = k
                if i + k > r:
                    l, r = i, i + k
            self._z = np.array(z)
        return self._z


def lce(q, i, j, limit):
    """Length of the longest common prefix of s[i:] and s[j:], up to limit, by doubling and first()."""
    limit = min(limit, q.n - max(i, j))
    if limit <= 0 or i == j:
        return max(limit, 0)
    r = 1
    while True:
        r = min(r, limit)
        k = q.first(q.s[i:i + r] != q.s[j:j + r], 4)
        if k is not None:
            return k
        if r == limit:
            return limit
        r *= 2


def lce_back(q, i, j, limit):
    """Longest common suffix of s[:i] and s[:j], up to limit."""
    limit = min(limit, i, j)
    if limit <= 0:
        return 0
    r = 1
    while True:
        r = min(r, limit)
        k = q.first(q.s[i - r:i][::-1] != q.s[j - r:j][::-1], 4)
        if k is not None:
            return k
        if r == limit:
            return limit
        r *= 2


def sample(q, l, w):
    """Vishkin's sample of the prefix of length l for alignments [0, w). Returns (period or None, w, s, columns).

    An alignment a survives if s[x - a] = c for all columns (x, c). Columns are found between the lowest and highest
    survivor, so they lie inside every survivor. If those two agree everywhere, their difference is a period: restart
    with the gcd. Keeping a fair coin's choice of the two chars at least halves the survivors with probability 1/2.
    """
    per = None
    while True:
        cols = []
        while True:
            if cols:
                A = np.arange(w)
                ok = np.ones(w, dtype=bool)
                for x, c in cols:
                    idx = x - A
                    good = (idx >= 0) & (idx < l)
                    ok &= good
                    ok[good] &= q.s[idx[good]] == c
                a, b = q.first(ok, 2 * len(cols)), q.last(ok, 2 * len(cols))
                if a is None and b is None:  # false none: survivors always exist
                    break
                a, b = (b if a is None else a), (a if b is None else b)
            else:
                a, b = 0, w - 1
            if a == b:
                return per, w, a, cols
            if len(cols) >= 16 * math.ceil(math.log2(q.n)):  # too many unlucky coins: redraw
                break
            d = b - a
            i = q.search(q.s[:l - d] != q.s[d:l], 4)
            if i is None:
                per = d if per is None else math.gcd(per, d)
                w = per
                break
            cols.append((i + b, q.read(i + d) if q.rng.random() < 0.5 else q.read(i)))


@dataclass
class Ctx:
    """What is known about the prefix of length l before any search over the text."""
    l: int
    p: int = None      # smallest period when at most l/8
    qlen: int = 0      # length of the prefix the sample belongs to
    w: int = 0
    s: int = 0
    cols: tuple = ()


def prepare(q, l):
    if l < 16:
        q.spent += l
        return Ctx(l)
    per, w, s, cols = sample(q, l, l // 8)
    if per is None:
        return Ctx(l, None, l, w, s, tuple(cols))
    _, w, s, cols = sample(q, 4 * per, per)
    return Ctx(l, per, 4 * per, w, s, tuple(cols))


def passes(q, c, lo, hi):
    """Which starts in [lo, hi] pass the sample."""
    ok = np.ones(hi - lo + 1, dtype=bool)
    for x, ch in c.cols:
        ok &= q.s[lo + x - c.s: hi + x - c.s + 1] == ch
    return ok


def candidates(q, c, lo, hi):
    """At most two starts in a block of at most c.w, leftmost and rightmost pass. Nothing else can be an occurrence."""
    ok = passes(q, c, lo, hi)
    w = 2 * len(c.cols)
    a = q.first(ok, w)
    if a is None:
        return []
    b = q.last(ok, w)
    return [lo + a] if b is None or a == b else [lo + a, lo + b]


def occ(q, c, lo, hi):
    """Occurrences of the prefix of length c.l with start in [lo, hi], where hi - lo + 1 <= c.l / 2.

    Returns (starts, run end). starts is a range or a list. run end is set only for a range.
    """
    l = c.l
    hi = min(hi, q.n - l)
    if lo > hi:
        return [], None
    if l < 16:
        q.spent += hi - lo + l
        return [t for t in range(lo, hi + 1) if (q.s[t:t + l] == q.s[:l]).all()], None
    if c.p is None:
        out = set()
        for b in range(lo, hi + 1, c.w):
            for t in candidates(q, c, b, min(hi, b + c.w - 1)):
                if lce(q, t, 0, l) == l:
                    out.add(t)
        return sorted(out), None
    p = c.p
    y = None
    for t in candidates(q, c, max(lo, hi - p + 1), hi):
        if lce(q, t, 0, c.qlen) == c.qlen:
            y = t
    if y is None:
        return [], None
    end = y + p + lce(q, y, y + p, 2 * l)
    start = y - lce_back(q, y, y + p, l)
    first = y - (y - max(start, lo)) // p * p
    return range(first, min(hi, end - l) + 1, p), end


def borders_in_group(q, L):
    """Border lengths in [L, 2L), increasing."""
    n = q.n
    if L > n:
        return []
    top = min(2 * L - 1, n)
    if top == L:
        return [L] if lce(q, 0, n - L, L) == L else []
    c = prepare(q, L)
    f = None
    out = []
    lo, hi = n - top, n - L
    size = max(1, L // 2)
    for b in range(lo, hi + 1, size):
        ts, end = occ(q, c, b, min(hi, b + size - 1))
        if isinstance(ts, range):
            if len(ts) == 0:
                continue
            if f is None:
                f = c.p + lce(q, 0, c.p, 2 * L)
            if end >= n:
                out += [n - t for t in ts if n - t <= f]
            elif (end - f) in ts and lce(q, end - f, 0, n - end + f) == n - end + f:
                out.append(n - end + f)
        else:
            out += [n - t for t in ts if lce(q, t, 0, n - t) == n - t]
    return sorted(set(out))


def blocks(n, l):
    s = (l + 1) // 2
    return s, (n - l) // s + 1


def pred(q, c, j):
    """Inner algorithm: is there a gap larger than l visible from block j? Looks at blocks j, j + 1, j + 2."""
    s, _ = blocks(q.n, c.l)
    last = q.n - c.l
    ts = []
    for b in (j, j + 1, j + 2):
        lo = b * s
        if lo <= last:
            ts.append((lo, occ(q, c, lo, lo + s - 1)[0]))
    starts = [t for _, r in ts for t in r]
    if any(y - x > c.l for x, y in zip(starts, starts[1:])):
        return True
    in_first = list(ts[0][1])
    return bool(in_first) and starts[-1] == in_first[-1] and starts[-1] != last


def pred_truth(q, l):
    """The same predicate for all blocks, from the simulator's knowledge."""
    s, J = blocks(q.n, l)
    st = np.flatnonzero(q.z()[: q.n - l + 1] >= l)
    marked = np.zeros(J, dtype=bool)
    for x, y in zip(st[np.flatnonzero(np.diff(st) > l)], st[np.flatnonzero(np.diff(st) > l) + 1]):
        j0 = x // s
        marked[j0] = True
        for j in (j0 - 1, j0 - 2):
            if j >= 0 and y < (j + 3) * s:
                marked[j] = True
    return marked


def pred_cap(q, c):
    """Queries a device must allow for one evaluation of pred, compute and uncompute. A device truncates at this."""
    B = q.budget + 2
    l = c.l
    if l < 16:
        return 2 * 3 * (l + (l + 1) // 2)
    first = lambda N, w: w * B * math.sqrt(N)
    lce_cap = lambda r: 4 * B * (4.42 * math.sqrt(r) + 2)  # doubling, at worst just above a power of 2
    m = max(2 * len(c.cols), 1)
    if c.p is None:
        each = 6 * (2 * first(c.w, m) + 2 * lce_cap(l))
    else:
        each = 2 * first(c.p, m) + 2 * lce_cap(c.qlen) + lce_cap(2 * l) + lce_cap(l)
    return int(2 * 3 * each)


def is_cover(q, l, c=None):
    """Does the border of length l cover the string? Search the blocks for a visible gap."""
    if l == q.n:
        return True
    c = c or prepare(q, l)
    return q.search(pred_truth(q, l), pred_cap(q, c)) is None


def shortest_cover(q):
    L = 1
    while L <= q.n:
        g = borders_in_group(q, L)
        if g and is_cover(q, g[0]):
            return g[0]
        L *= 2
    return q.n


def all_covers(q):
    """All covers. In a group they are a prefix of the increasing border lengths, so bisect."""
    out = []
    L = 1
    while L <= q.n:
        g = borders_in_group(q, L)
        if g and is_cover(q, g[0]):
            lo, hi = 0, len(g) - 1
            while lo < hi:
                mid = (lo + hi + 1) // 2
                if is_cover(q, g[mid]):
                    lo = mid
                else:
                    hi = mid - 1
            out += g[: lo + 1]
        L *= 2
    return out
