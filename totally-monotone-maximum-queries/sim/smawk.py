"""Classical baseline: SMAWK row maxima, counting distinct entries read. Each answer is checked against M.max().

Limits: these families, sizes up to 4096. This measures SMAWK as written here, with a cache so that a repeated read
of an entry counts once, and is not a lower bound on classical algorithms.
"""
import sys
import numpy as np
from monge import random_monge, hard, warped


def smawk_max(M):
    seen = set()

    def at(i, j):
        seen.add((i, j))
        return M[i, j]

    def rec(rows, cols):
        if not rows:
            return {}
        stack = []
        for c in cols:  # reduce: keep at most len(rows) columns
            while stack:
                r = rows[len(stack) - 1]
                if at(r, stack[-1]) < at(r, c):  # c beats the top on this row and on all rows below it
                    stack.pop()
                else:
                    break
            if len(stack) < len(rows):
                stack.append(c)
        best = rec(rows[1::2], stack)
        pos, out, k = 0, dict(best), 0
        for i in range(0, len(rows), 2):
            r = rows[i]
            hi = best[rows[i + 1]] if i + 1 < len(rows) else stack[-1]
            bj, bv = None, None
            while k < len(stack):
                c = stack[k]
                v = at(r, c)
                if bv is None or v > bv:
                    bj, bv = c, v
                if c == hi:
                    break
                k += 1
            out[r] = bj
        return out

    n, m = M.shape
    res = rec(list(range(n)), list(range(m)))
    return max(M[i, j] for i, j in res.items()), len(seen)


def main(top):
    fams = {"monge": lambda n, s: random_monge(n, s), "warped": warped, "hard1": lambda n, s: hard(n, (np.arange(n) == s % n).astype(np.int64))}
    ns = [2 ** k for k in range(4, top + 1)]
    print(f"{'family':8} " + " ".join(f"{n:>7}" for n in ns) + "   reads, mean of 10; then reads/n at the largest size")
    for name, f in fams.items():
        ys = []
        for n in ns:
            reads = []
            for s in range(10):
                M = f(n, s)
                v, c = smawk_max(M)
                assert v == M.max(), (name, n, s)
                reads.append(c)
            ys.append(float(np.mean(reads)))
        print(f"{name:8} " + " ".join(f"{y:7.0f}" for y in ys) + f"   {ys[-1] / ns[-1]:.2f}", flush=True)


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 12)
