"""Bases of the quantum monotone local search corollaries, and a numerical check of the bound
max_k min_t C(n,t)/C(k,t) c^(k-t) <= (2 - 1/c)^n poly(n) (Lemma 2.2 of Fomin, Gaspers, Lokshtanov, Saurabh)
together with its square root, the cost of the quantum version."""
import math

CASES = [  # problem, extension base c, source of the extension algorithm
    ("Feedback Vertex Set", 3.460, "Iwata-Kobayashi, highest-degree branching"),
    ("Cluster Vertex Deletion", 1.811, "Tsur, branching"),
    ("3-Hitting Set, weighted", 2.168, "Shachnai-Zehavi, branching"),
    ("Proper Interval Vertex Deletion", 6.0, "Cao, branching on small obstructions"),
    ("Multicut on Trees", math.sqrt(math.sqrt(2) + 1), "Kanj et al., branch and search"),
    ("Min-Ones 3-SAT", 3.0, "branching on an unsatisfied clause"),
    ("Min-Ones 4-SAT, 4-Hitting Set", 4.0, "branching on an unsatisfied clause"),
    ("Min-Ones 5-SAT, 5-Hitting Set", 5.0, "branching on an unsatisfied clause"),
]


def up(x, d=4):
    return math.ceil(x * 10**d - 1e-12) / 10**d


def lchoose(a, b):
    return math.lgamma(a + 1) - math.lgamma(b + 1) - math.lgamma(a - b + 1)


def worst(n, c):
    """max over k of min over t of log(C(n,t)/C(k,t) c^(k-t)), exact over integers."""
    return max(min(lchoose(n, t) - lchoose(k, t) + (k - t) * math.log(c) for t in range(k + 1))
               for k in range(n + 1))


if __name__ == "__main__":
    for name, c, src in CASES:
        b = 2 - 1 / c
        q = up(math.sqrt(b))
        assert math.sqrt(b) <= q
        print(f"{name:32s} c = {c:.6f} ({src}); classical 2-1/c = {b:.6f}; quantum sqrt = {math.sqrt(b):.6f} <= {q}")
        for n in (50, 200, 1000, 3000):
            w = worst(n, c)
            excess = w - n * math.log(b)          # must stay O(log n)
            assert excess <= 2 * math.log(n + 1), (name, n, excess)
            # quantum: sum over k of sqrt(term) <= (n + 1) sqrt(max term)
            print(f"    n = {n:5d}: log(max min) - n log(2-1/c) = {excess:+.3f}  (2 log(n+1) = {2*math.log(n+1):.3f})")
    print("all bounds hold")
