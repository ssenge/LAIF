"""Learning a nested matrix and recognizing threshold and chain graphs with few queries.

The algorithm of ../README.md. Q counts queries: one per entry read, and for a search the oracle applications of
BBHT sampled from the exact Grover law, stopping after budget * sqrt(N) as a device would. No circuits here;
see qiskit_check.py. Limits: statistical, and counts on these families carry no guarantee beyond ../README.md.
"""
import math
import numpy as np


class Budget(Exception):
    pass


class Q:
    def __init__(self, A, rng, budget=16, limit=None):
        self.A, self.rng, self.budget, self.limit = A, rng, budget, limit
        self.reads = self.apps = 0

    def total(self):
        return self.reads + self.apps

    def _spend(self):
        if self.limit is not None and self.total() > self.limit:
            raise Budget

    def row(self, r, C):
        self.reads += len(C)
        self._spend()
        return self.A[r, C]

    def col(self, R, c):
        self.reads += len(R)
        self._spend()
        return self.A[R, c]

    def block(self, R, C):
        self.reads += len(R) * len(C)
        self._spend()
        return self.A[np.ix_(R, C)]

    def search(self, marked):
        """BBHT on a boolean array of candidates. Returns a uniformly random marked index, or None after the budget."""
        N = marked.size
        if N == 0:
            return None
        hits = np.flatnonzero(marked)
        t = len(hits)
        if N <= 16:  # reading a tiny set costs less than the budget, and cannot fail
            self.reads += N
            self._spend()
            return int(hits[self.rng.integers(t)]) if t else None
        theta = math.asin(math.sqrt(t / N))
        limit = self.budget * math.sqrt(N)
        m, spent = 1.0, 0
        while spent <= limit:
            j = int(self.rng.integers(0, int(m)))
            spent += 2 * j + 1
            if t and self.rng.random() < math.sin((2 * j + 1) * theta) ** 2:
                self.apps += spent
                self._spend()
                return int(hits[self.rng.integers(t)])
            m = min(m * 8 / 7, math.sqrt(N) + 1)
        self.apps += spent
        self._spend()
        return None


def holding(q, R, C, val):
    """All columns of C with some entry val in rows R: repeatedly find one outside the known set and read its row."""
    known = np.zeros(len(C), dtype=bool)
    while True:
        free = np.flatnonzero(~known)
        hit = q.search(q.A[np.ix_(R, C[free])] == val)
        if hit is None:
            return known
        r = R[hit // len(free)]
        known |= q.row(r, C) == val


def holding_rows(q, R, C, val):
    known = np.zeros(len(R), dtype=bool)
    while True:
        free = np.flatnonzero(~known)
        hit = q.search(q.A[np.ix_(R[free], C)] == val)
        if hit is None:
            return known
        c = C[hit % len(C)]
        known |= q.col(R, c) == val


def trim(q, H, R, C):
    """Fix every row and column of the block that is constant, and return what is left."""
    if not (len(R) and len(C)):
        return R, C
    keep_r, keep_c = np.ones(len(R), dtype=bool), np.ones(len(C), dtype=bool)
    for val in (0, 1):
        some_c, some_r = holding(q, R, C, val), holding_rows(q, R, C, val)
        H[np.ix_(R[~some_r], C)] = 1 - val
        H[np.ix_(R, C[~some_c])] = 1 - val
        keep_r &= some_r
        keep_c &= some_c
    return R[keep_r], C[keep_c]


def learn_nested(q, H, R, C):
    """Fill H on R x C, correctly whenever the rows of the block are nested."""
    if not (len(R) and len(C)):
        return
    if len(R) * len(C) <= 4 * (len(R) + len(C)):
        H[np.ix_(R, C)] = q.block(R, C)
        return
    x, w = R[q.rng.integers(len(R))], C[q.rng.integers(len(C))]
    in_x, in_w = q.row(x, C) == 1, q.col(R, w) == 1
    C1, C0, R1, R0 = C[in_x], C[~in_x], R[in_w], R[~in_w]
    if q.A[x, w]:
        H[np.ix_(R0, C0)] = 0
        parts = [(R0, C1), (R1, C1), (R1, C0)]
    else:
        H[np.ix_(R1, C1)] = 1
        parts = [(R0, C1), (R0, C0), (R1, C0)]
    for a, b in parts:
        learn_nested(q, H, *trim(q, H, a, b))


def learn_threshold(q, H, S):
    """Split the vertices in two, learn the cross block, recurse. Each pair falls in exactly one block."""
    if len(S) < 2:
        return
    S = q.rng.permutation(S)
    a, b = S[: len(S) // 2], S[len(S) // 2:]
    learn_nested(q, H, a, b)
    H[np.ix_(b, a)] = H[np.ix_(a, b)].T
    learn_threshold(q, H, a)
    learn_threshold(q, H, b)


def is_threshold(A):
    """Classical, no queries: peel isolated or dominating vertices."""
    n = len(A)
    deg = A.sum(1).astype(int)
    order = np.argsort(deg)
    lo, hi, dom = 0, n - 1, 0
    while lo <= hi:
        if deg[order[lo]] == dom:
            lo += 1
        elif deg[order[hi]] == dom + hi - lo:
            hi -= 1
            dom += 1
        else:
            return False
    return True


def is_nested(M):
    """Classical, no queries: rows sorted by size must form a chain under inclusion."""
    rows = M[np.argsort(M.sum(1))].astype(bool)
    return bool((rows[:-1] <= rows[1:]).all()) if len(rows) > 1 else True


def recognize_threshold(A, rng, budget=16, factor=256):
    """Returns (answer, q). Learn a hypothesis, then search all pairs for a disagreement."""
    n = len(A)
    lg = max(1, math.ceil(math.log2(max(n, 2))))
    q = Q(A, rng, budget, factor * n * lg ** 4)
    H = np.zeros((n, n), dtype=A.dtype)
    try:
        learn_threshold(q, H, np.arange(n))
        if not is_threshold(H):
            return False, q
        return q.search((H != A)[np.triu_indices(n, 1)]) is None, q
    except Budget:
        return False, q


def recognize_nested(M, rng, budget=16, factor=256):
    """The same for a rectangular matrix: are its rows a chain under inclusion?"""
    a, b = M.shape
    q = Q(M, rng, budget, factor * (a + b) * max(1, math.ceil(math.log2(a + b))) ** 3)
    H = np.zeros_like(M)
    try:
        learn_nested(q, H, np.arange(a), np.arange(b))
        if not is_nested(H):
            return False, q
        return q.search((H != M).ravel()) is None, q
    except Budget:
        return False, q


def sides(q, n):
    """Bipartition of the non-isolated vertices of a chain graph, or None if there is no edge."""
    iu = np.triu_indices(n, 1)
    hit = q.search(q.A[iu] == 1)
    if hit is None:
        return None
    V = np.arange(n)
    X = V[q.col(V, int(iu[1][hit])) == 1]  # contains the top of its side, so two more steps reach everything
    Y = V[holding(q, X, V, 1)]
    return V[holding(q, Y, V, 1)], Y


def recognize_chain(A, rng, budget=16, factor=256):
    """Is the graph bipartite with nested neighbourhoods on one side (chain graph, plus isolated vertices)?"""
    n = len(A)
    lg = max(1, math.ceil(math.log2(max(n, 2))))
    q = Q(A, rng, budget, factor * n * lg ** 3)
    try:
        s = sides(q, n)
        if s is None:
            return True, q
        X, Y = s
        if set(X) & set(Y):
            return False, q
        H = np.zeros((n, n), dtype=A.dtype)
        learn_nested(q, H, X, Y)
        if not is_nested(H[np.ix_(X, Y)]):
            return False, q
        H[np.ix_(Y, X)] = H[np.ix_(X, Y)].T
        return q.search((H != A)[np.triu_indices(n, 1)]) is None, q
    except Budget:
        return False, q


def from_sequence(seq, perm=None):
    """Threshold graph from a creation sequence: seq[i] = 1 joins vertex i to all earlier ones."""
    n = len(seq)
    A = np.zeros((n, n), dtype=np.int8)
    for j in range(n):
        if seq[j]:
            A[j, :j] = A[:j, j] = 1
    return A if perm is None else A[np.ix_(perm, perm)]


def nested_from_tokens(tokens, seed=0):
    """tokens is a string of r and c, low to high: entry 1 when the row lies above the column. Rows and columns shuffled."""
    pos_r = [i for i, t in enumerate(tokens) if t == "r"]
    pos_c = [i for i, t in enumerate(tokens) if t == "c"]
    M = np.array([[int(p > q) for q in pos_c] for p in pos_r], dtype=np.int8).reshape(len(pos_r), len(pos_c))
    r = np.random.default_rng(seed)
    return M[np.ix_(r.permutation(len(pos_r)), r.permutation(len(pos_c)))]
