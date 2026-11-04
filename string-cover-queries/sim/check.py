"""Against brute force, and how the queries grow. Run with python check.py (numpy; qiskit and qiskit-aer for the circuits)
Limits: small strings exhaustive, larger ones from the families below, fixed budget, so asymptotics are indicative.
"""
import itertools
import sys
import numpy as np
from covers import *


def brute(s):
    n = len(s)
    out = []
    for l in range(1, n + 1):
        c = s[:l]
        st = [i for i in range(n - l + 1) if s[i:i + l] == c]
        if st[-1] == n - l and all(y - x <= l for x, y in zip(st, st[1:])):
            out.append(l)
    return out


def codes(s):
    return np.frombuffer(s.encode(), dtype=np.uint8).astype(np.int64)


def covered(c, n, r):
    """A string of length about n with cover c, overlaps chosen at random among the borders of c."""
    b = [k for k in range(1, len(c)) if c[:k] == c[len(c) - k:]] + [0]
    s = c
    while len(s) < n:
        s += c[r.choice(b):]
    return s


def fib(n):
    a, b = "a", "ab"
    while len(b) < n:
        a, b = b, b + a
    return b[:n]


def families(n, seed):
    r = np.random.default_rng(seed)
    letters = lambda k: "".join(r.choice(list("ab"), k))
    yield "a^n", "a" * n
    yield "one b", "a" * (n // 2) + "b" + "a" * (n - n // 2 - 1)
    yield "random", letters(n)
    yield "fibonacci", fib(n)
    c = "aba" if n < 64 else "abaab" + "a" * 3 + "abaab"
    yield "small cover", covered(c, n, r)
    k = max(2, int(n ** 0.5))
    u = letters(k)
    yield "root cover", covered(u + u[:k // 2 + 1] + "b" + u + u[:k // 2 + 1], n, r)
    u = letters(n // 3 + 1)
    yield "long cover", u + u[: n // 8] + u
    s = covered("aab", n, r)
    i = int(r.integers(len(s)))
    yield "flip", s[:i] + ("a" if s[i] == "b" else "b") + s[i + 1:]


def truth_cover(s, q):
    """Shortest cover from the Z array, which is the same check as brute without the quadratic cost."""
    z, n = q.z(), len(s)
    for l in range(1, n + 1):
        if z[n - l] == l:
            st = np.flatnonzero(z[: n - l + 1] >= l)
            if (np.diff(st) <= l).all():
                return l


def inner_vs_truth(q, l, seen):
    c = prepare(q, l)
    seen["periodic" if c.p else "aperiodic"] += 1
    t = pred_truth(q, l)
    for j in range(len(t)):
        before = q.spent
        assert pred(q, c, j) == t[j], (l, j)
        yield 2 * (q.spent - before), pred_cap(q, c), l


def main():
    rng = np.random.default_rng(1)
    cnt = 0
    for n in range(1, 15):
        for t in itertools.product("abc" if n <= 8 else "ab", repeat=n):
            s = "".join(t)
            b = brute(s)
            q = Q(codes(s), rng, 32)
            assert shortest_cover(q) == b[0], s
            assert all_covers(Q(codes(s), rng, 32)) == b, s
            cnt += 1
    print("all strings up to n = 14:", cnt, "agreed with brute force, shortest and all covers")

    cnt = fails = worst = worst16 = 0
    seen = {"periodic": 0, "aperiodic": 0}
    for n in (20, 33, 64, 100, 257, 512, 1000, 2048):
        for seed in range(6):
            for name, s in families(n, seed):
                b = brute(s)
                assert shortest_cover(Q(codes(s), rng, 32)) == b[0], (name, n, seed)
                assert all_covers(Q(codes(s), rng, 32)) == b, (name, n, seed)
                cnt += 1
                q = Q(codes(s), rng, 32)
                borders = [k for k in range(1, n) if s[:k] == s[n - k:]]
                long_b = [k for k in borders if k >= 16]
                for l in borders[:4] + long_b[:: max(1, len(long_b) // 6)]:
                    for spent, cap, l in inner_vs_truth(q, l, seen):
                        fails += spent > cap
                        worst = max(worst, spent / cap)
                        if l >= 16:
                            worst16 = max(worst16, spent / cap)
    assert seen["periodic"] > 0
    print("families up to n = 2048:", cnt, "agreed; inner predicate agreed with the truth on every block, contexts", seen)
    print(f"two-way inner cost above pred_cap in {fails} evaluations; largest ratio {worst:.2f}, and {worst16:.2f} for l >= 16")

    wrong = 0
    print("\nqueries / sqrt(n), budget 16, mean of 3; last column: fitted exponent")
    sizes = [2 ** k for k in range(8, 19, 2)]
    print(f"{'family':14}" + "".join(f"{n:>11}" for n in sizes) + "   exponent")
    for name in ("a^n", "one b", "random", "fibonacci", "small cover", "root cover", "long cover", "flip"):
        row = []
        for n in sizes:
            qs = []
            for seed in range(3):
                s = dict(families(n, seed))[name]
                q = Q(codes(s), np.random.default_rng(seed), 16)
                got = shortest_cover(q)
                wrong += got != truth_cover(s, q)
                qs.append(q.spent)
            row.append(np.mean(qs))
        e = np.polyfit(np.log(sizes), np.log(row), 1)[0]
        print(f"{name:14}" + "".join(f"{x / n ** 0.5:11.0f}" for x, n in zip(row, sizes)) + f"{e:11.3f}", flush=True)
    print("wrong answers in those runs:", wrong)
    print("ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
