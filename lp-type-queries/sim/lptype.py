"""Quantum Clarkson for LP-type problems, on the smallest enclosing ball of n points in R^d. See ../README.md.

Q counts queries: one per constraint (a point) read, and for a search the applications of BBHT sampled from the exact
Grover law, stopping after budget * sqrt(N). One weight evaluation costs one query and one uncompute, as a single
query returns the whole point. The classical solver on the sample costs no queries.
Limits: statistical, floating point with a tolerance, and small fixed dimension.
"""
import math
import numpy as np

TOL = 1e-9


class Q:
    def __init__(self, P, rng, budget=16):
        self.P, self.rng, self.budget = P, rng, budget
        self.n = len(P)
        self.spent = 0

    def search(self, marked):
        """BBHT on a boolean array. Returns a uniformly random marked index, or None after the budget."""
        N = marked.size
        hits = np.flatnonzero(marked)
        t = len(hits)
        if N <= 16:
            self.spent += N
            return int(hits[self.rng.integers(t)]) if t else None
        theta = math.asin(math.sqrt(t / N))
        limit = self.budget * math.sqrt(N)
        m, used = 1.0, 0
        while used <= limit:
            j = int(self.rng.integers(0, int(m)))
            used += 2 * j + 1
            if t and self.rng.random() < math.sin((2 * j + 1) * theta) ** 2:
                self.spent += 2 * used
                return int(hits[self.rng.integers(t)])
            m = min(m * 8 / 7, math.sqrt(N) + 1)
        self.spent += 2 * used
        return None

    def find_all(self, marked):
        """All marked indices, by repeated search, each time excluding those already found."""
        marked = marked.copy()
        out = []
        while True:
            i = self.search(marked)
            if i is None:
                return out
            out.append(i)
            marked[i] = False


def ball_of(R, d):
    """The ball with the points of R on its boundary, in their affine hull."""
    if len(R) == 0:
        return np.zeros(d), -1.0
    a = R[0]
    if len(R) == 1:
        return a.copy(), 0.0
    A = R[1:] - a
    G = 2 * A @ A.T
    b = (A * A).sum(1)
    x = np.linalg.lstsq(G, b, rcond=None)[0]
    v = A.T @ x
    return a + v, float(v @ v)


def solve(P):
    """Exact smallest enclosing ball by Welzl with move to front. No queries."""
    P = np.asarray(P, dtype=float)
    d = P.shape[1]
    order = list(np.random.default_rng(len(P)).permutation(len(P)))

    def rec(k, R):
        c, r2 = ball_of(P[R], d) if R else (np.zeros(d), -1.0)
        if len(R) == d + 1:
            return c, r2
        for pos in range(k):
            i = order[pos]
            if r2 < 0 or ((P[i] - c) ** 2).sum() > r2 * (1 + TOL) + TOL:
                c, r2 = rec(pos, R + [i])
                order.insert(0, order.pop(pos))
        return c, r2

    return rec(len(P), [])


def violates(P, c, r2):
    return ((P - c) ** 2).sum(1) > r2 * (1 + 1e-7) + 1e-7


def weights(P, balls):
    e = np.zeros(len(P), dtype=np.int64)
    for c, r2 in balls:
        e += violates(P, c, r2)
    return 2.0 ** e


def poisson(q, w, s, W):
    """Each i independently with probability min(1, s w_i / W), by a new random function per call and find_all."""
    pi = np.minimum(1.0, s * w / W)
    marked = q.rng.random(q.n) < pi
    out = np.array(q.find_all(marked), dtype=np.int64)
    q.spent += len(out)  # read those points
    return out, pi


def clarkson(q, rounds=None):
    """Returns the ball, the number of rounds used, and the largest sample."""
    n, d = q.n, q.P.shape[1]
    delta = d + 1  # combinatorial dimension of the smallest enclosing ball
    s = 2 * delta * delta
    T = rounds or int(12 * delta * math.log(max(n, 3))) + 1
    if n <= 4 * s:
        q.spent += n
        return solve(q.P), 0, n
    balls = []
    Wt = float(n)
    largest = 0
    for t in range(T):
        w = weights(q.P, balls)
        s2 = 64  # estimate the total weight within a constant factor, Horvitz-Thompson
        idx, pi = poisson(q, w, s2, 2 * Wt)
        est = (w[idx] / pi[idx]).sum()
        Wt = max(est / 2, 1.0)
        idx, _ = poisson(q, w, s, Wt)
        largest = max(largest, len(idx))
        c, r2 = solve(q.P[idx]) if len(idx) else (np.zeros(d), -1.0)
        if q.search(violates(q.P, c, r2)) is None:
            return (c, r2), t + 1, largest
        balls.append((c, r2))
    return None, T, largest
