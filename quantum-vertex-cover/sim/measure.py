"""Tests condition (M1) and the size of the cut trees in Theorem 1, for the measure B = x^budget on the branching of tree.py, and
the level scan of Lemma 2 on disjoint unions. (M1) is tested by the largest antichain sum, A(v) = max(B(v), sum of A over
children). At x = 1.4656, the root of the branching vector (1, 3), it stays at B(root), and at x = 1.1 it fails, which shows that
the test can fail. The scan is compared with the true sum of minimum covers, on feasible and on infeasible budgets."""
import math
import random
import sys
from tree import Tree, TooLarge, random_regular, minimum_cover

X = 1.4656
LOGX = math.log(X)


def antichain_ratio(t, x):
    """Largest antichain sum of B over B(root). Children come after their parent in the order of Tree."""
    best = [0.0]*t.T
    for v in range(t.T - 1, -1, -1):
        best[v] = max(x**max(t.budget[v], 0), sum(best[y] for y in t.kids[v]))
    return best[0]/x**max(t.budget[0], 0)


def cut_size(t, delta):
    """Inner nodes of the tree cut where log B has dropped by delta from the root."""
    limit = max(t.budget[0], 0)*LOGX - delta
    return sum(1 for v in range(t.T) if max(t.budget[v], 0)*LOGX > limit)


def scan(parts, k):
    """Lemma 2 on parts with budget k. Returns the decision, and the largest level used while two parts were unsolved."""
    unsolved, used, b, top = list(parts), 0, 0, 0.0
    while len(unsolved) > 1:
        if 2*b > k - used:                      # each of two unsolved parts needs at least budget b
            return False, top
        top = b*LOGX
        for p in list(unsolved):
            if len(unsolved) > 1 and Tree(p, b).has_marked():
                used += minimum_cover(p)
                unsolved.remove(p)
        if used > k:
            return False, top
        b += 1
    return Tree(unsolved[0], k - used).has_marked() if k >= used else False, top


if __name__ == "__main__":
    rng = random.Random(5)
    bad, checks, top_ratio, low_ratio, cut_ratio = 0, 0, 0.0, 0.0, 0.0
    for d, sizes in ((3, (20, 30, 40, 50)), (4, (16, 20, 24)), (6, (14, 18, 22)), (8, (14, 18))):
        for size in sizes:
            adj = random_regular(size, d, rng)
            for frac in (.4, .5, .6, .7):
                try:
                    t = Tree(adj, int(frac*size), limit=3000)
                except TooLarge:
                    continue
                if t.T < 5:
                    continue
                checks += 1
                top_ratio = max(top_ratio, antichain_ratio(t, X))
                low_ratio = max(low_ratio, antichain_ratio(t, 1.1))
                for delta in (1, 2, 3):
                    cut_ratio = max(cut_ratio, cut_size(t, delta)/((max(t.depth) + 1)*math.exp(delta)))
    bad += top_ratio > 1 + 1e-9 or low_ratio <= 1.5 or cut_ratio > 1
    print(f"(M1): {checks} trees; largest antichain sum over B(root) is {top_ratio:.3f} at x = {X} and {low_ratio:.3f} at x = 1.1")
    print(f"cut trees: largest size over depth * e^delta is {cut_ratio:.3f}")
    yes = no = wrong = 0
    worst = -math.inf
    for seed in range(60):
        r = random.Random(seed)
        parts = [random_regular(r.choice((6, 8, 10)), 3, r) for _ in range(r.choice((2, 3, 4)))]
        truth = sum(minimum_cover(p) for p in parts)
        for k in (truth - 1, truth, truth + 1):
            ans, top = scan(parts, k)
            wrong += ans != (truth <= k)
            yes += truth <= k
            no += truth > k
            worst = max(worst, top - k*LOGX/2)
    bad += wrong + (worst > 1e-9)
    print(f"scan: {yes} feasible and {no} infeasible budgets on unions, {wrong} wrong; largest level minus half the log measure {worst:.3f}")
    print(f"{bad} failed checks")
    sys.exit(1 if bad else 0)
