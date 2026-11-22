"""Multicast game on a ring (arXiv 1507.04222, Sec. 2): edges a_0..a_n counter-clockwise, players 0..n-1, player i
between edge i and edge i+1; left = edges 0..i, right = edges i+1..n. Fair cost sharing. Myopic sequential play:
players arrive in order pi, each takes a best response in the game of the players so far (ties: `tie` picks).
Network cost = sum of used edges. OPT = total - max edge (all edges but one)."""
from fractions import Fraction as F
from itertools import permutations


def left(i): return range(0, i + 1)
def right(i, n): return range(i + 1, n + 1)


def play(a, pi, tie=None):
    """Max (worst) network cost over all tie choices along the order pi, and one decision map attaining it."""
    n = len(a) - 1; a = [F(x) for x in a]; best = [None, None]

    def rec(k, u, dec):
        if k == len(pi):
            c = sum(a[e] for e in range(n + 1) if u[e])
            if best[0] is None or c > best[0]: best[0], best[1] = c, dict(dec)
            return
        i = pi[k]
        cl = sum(a[e] / (u[e] + 1) for e in left(i)); cr = sum(a[e] / (u[e] + 1) for e in right(i, n))
        for d, rng_ in (("L", left(i)), ("R", right(i, n))):
            if (d == "L" and cl <= cr) or (d == "R" and cr <= cl):
                v = list(u)
                for e in rng_: v[e] += 1
                dec[i] = d; rec(k + 1, v, dec)
    rec(0, [0] * (n + 1), {})
    return best[0], best[1]


def opt(a): return sum(map(F, a)) - max(map(F, a))


def perms_AB(a, o=None):
    """The two orders of [Thm 5.4]: OPT omits edge o (largest), WLOG left part >= right part (else mirror)."""
    n = len(a) - 1
    if o is None: o = max(range(n + 1), key=lambda k: a[k])
    A = list(range(n - 1, o - 1, -1)) + list(range(0, o)); B = list(range(n - 1, -1, -1))
    return A, B, o


def mirror(a): return list(reversed(a))


def best_two(a):
    n = len(a) - 1; o = max(range(n + 1), key=lambda k: a[k])
    b, ob = (a, o) if sum(a[:o]) >= sum(a[o + 1:]) else (mirror(a), n - o)   # o moves with the mirror
    A, B, _ = perms_AB(b, ob)
    worst = lambda pi: play(b, pi)[0]   # worst tie choices
    return min(worst(A), worst(B)) / opt(b)


def best_all(a):
    n = len(a) - 1
    return min(play(a, pi)[0] for pi in permutations(range(n))) / opt(a)


def check():
    # 26/19 example of the paper: 3 players, weights 6, 10, 3, 10 (/19); order (0,1,2) gives 26/19, opposite gives 1
    a = [6, 10, 3, 10]
    c, _ = play(a, [0, 1, 2]); assert c / opt(a) == F(26, 19), c
    c2, _ = play(a, [2, 1, 0]); assert c2 == opt(a)
    print("ring check ok:", c / opt(a), "best-of-all", best_all(a))


if __name__ == "__main__":
    check()
