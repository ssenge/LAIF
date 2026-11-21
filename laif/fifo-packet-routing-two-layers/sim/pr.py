"""FIFO packet routing game on linear multigraphs (Werth model, UFR equilibria, makespan objective).

Instance: layers[j] = list of transit times (positive ints) of the parallel edges from v_j to v_{j+1}; n unit
packets at s at time 0; every edge releases at most one packet per step (capacity 1), FIFO, ties by player index.
A packet reaching the tail at time a leaves the queue at d = max(a, d_prev + 1) and reaches the head at d + tau.

In an equilibrium players arrive at every node in index order, so player i's latencies depend only on players < i
(sequential best response; equilibria differ only in tie choices). worst() enumerates all tie choices exactly
(small n) and greedy() is the greedy-queue policy (tie -> longest queue, then lowest edge index), which the paper
shows to be the worst equilibrium. opt() is the quickest-flow makespan, by the temporally repeated successive
shortest paths and, as a check, by a time-expanded max flow."""
import itertools

import networkx as nx


def load(layers, paths):
    """Network loading of a state (paths[i][j] = edge index of player i in layer j). Returns arrival times at d.
    Players are processed in index order per layer, in order of (arrival time, index), as FIFO requires."""
    n = len(paths)
    arr = [0] * n
    for j, lay in enumerate(layers):
        last = [-1] * len(lay)
        new = [0] * n
        for i in sorted(range(n), key=lambda i: (arr[i], i)):
            e = paths[i][j]
            d = max(arr[i], last[e] + 1)
            last[e] = d
            new[i] = d + lay[e]
        arr = new
    return arr


def is_ufr(layers, paths):
    """UFR equilibrium: no player reaches any node on her route earlier by a unilateral path change."""
    n, m = len(paths), len(layers)

    def node_times(ps, i):
        t, out = 0, []
        # arrival of player i at v_1..v_m under state ps
        arr = [0] * n
        for j, lay in enumerate(layers):
            last = [-1] * len(lay)
            new = [0] * n
            for k in sorted(range(n), key=lambda k: (arr[k], k)):
                e = ps[k][j]
                d = max(arr[k], last[e] + 1)
                last[e] = d
                new[k] = d + lay[e]
            arr = new
            out.append(arr[i])
        return out

    for i in range(n):
        base = node_times(paths, i)
        for alt in itertools.product(*[range(len(l)) for l in layers]):
            ps = list(paths)
            ps[i] = alt
            t = node_times(ps, i)
            if any(t[j] < base[j] for j in range(m)):
                return False
    return True


def _seq(layers, n, choose):
    """Sequential best response; choose(i, j, ties, last, a) picks among the min-latency edges."""
    paths = [[0] * len(layers) for _ in range(n)]
    lasts = [[-1] * len(l) for l in layers]
    arr = [0] * n
    for i in range(n):
        a = 0
        for j, lay in enumerate(layers):
            lat = [max(a, lasts[j][e] + 1) + lay[e] for e in range(len(lay))]
            mn = min(lat)
            ties = [e for e in range(len(lay)) if lat[e] == mn]
            e = choose(i, j, ties, lasts[j], a)
            paths[i][j] = e
            lasts[j][e] = max(a, lasts[j][e] + 1)
            a = mn
        arr[i] = a
    return paths, arr


def greedy(layers, n):
    """Greedy queue policy: ties -> longest queue at entry (latest last departure), then lowest index."""
    return _seq(layers, n, lambda i, j, ties, last, a: max(ties, key=lambda e: (last[e] - a, -e)))


def best_first(layers, n):
    return _seq(layers, n, lambda i, j, ties, last, a: ties[0])


def worst(layers, n):
    """Exact worst and best equilibrium makespan over all tie choices (exponential; small instances)."""
    best = [None, None]

    def rec(i, lasts, mx):
        if i == n:
            best[0] = mx if best[0] is None else max(best[0], mx)
            best[1] = mx if best[1] is None else min(best[1], mx)
            return

        def walk(j, a, lasts):
            if j == len(layers):
                rec(i + 1, lasts, max(mx, a))
                return
            lay = layers[j]
            lat = [max(a, lasts[j][e] + 1) + lay[e] for e in range(len(lay))]
            mn = min(lat)
            for e in range(len(lay)):
                if lat[e] == mn:
                    nl = [list(x) for x in lasts]
                    nl[j][e] = max(a, lasts[j][e] + 1)
                    walk(j + 1, mn, nl)

        walk(0, 0, lasts)

    rec(0, [[-1] * len(l) for l in layers], 0)
    return best[0], best[1]


def opt(layers, n):
    """Quickest makespan: least T with sum_k max(0, T + 1 - tau(P_k)) >= n, P_k = k-th shortest edge per layer
    (successive shortest paths of a linear multigraph), k up to the smallest layer size."""
    srt = [sorted(l) for l in layers]
    K = min(len(l) for l in layers)
    tau = [sum(s[k] for s in srt) for k in range(K)]
    lo, hi = tau[0] - 1, tau[0] + n  # f(lo) = 0 < n <= f(hi); f(T) = packets delivered by T
    while hi - lo > 1:
        mid = (lo + hi) // 2
        lo, hi = (lo, mid) if sum(max(0, mid + 1 - t) for t in tau) >= n else (mid, hi)
    return hi


def opt_flow(layers, n):
    """Time-expanded max flow check of opt(): least T with n packets at d by time T (holdover at s only is enough,
    but holdover is allowed everywhere)."""
    T = 0
    while True:
        G = nx.DiGraph()
        for t in range(T + 1):
            for v in range(len(layers) + 1):
                if t < T:
                    G.add_edge((v, t), (v, t + 1), capacity=n)
            for j, lay in enumerate(layers):
                for e, tau in enumerate(lay):
                    if t + tau <= T:
                        G.add_edge((j, t), ("e", j, e, t), capacity=1)
                        G.add_edge(("e", j, e, t), (j + 1, t + tau), capacity=1)
        G.add_edge("S", (0, 0), capacity=n)
        if (len(layers), T) in G and nx.maximum_flow_value(G, "S", (len(layers), T)) >= n:
            return T
        T += 1


def check():
    ex = [[1, 2], [2]]
    assert load(ex, [(0, 0), (1, 0), (0, 0)]) == [3, 4, 5]  # Figure 1 of the source
    import random
    rng = random.Random(1)
    for _ in range(300):
        m = rng.randint(1, 3)
        layers = [[rng.randint(1, 5) for _ in range(rng.randint(1, 3))] for _ in range(m)]
        n = rng.randint(1, 6)
        pg, ag = greedy(layers, n)
        w, b = worst(layers, n)
        assert load(layers, pg) == ag and max(ag) == w, (layers, n, ag, w)
        if n <= 4 and sum(len(l) for l in layers) <= 6:
            assert is_ufr(layers, pg) and is_ufr(layers, best_first(layers, n)[0])
        assert opt(layers, n) == opt_flow(layers, n), (layers, n)
    print("pr check ok")


if __name__ == "__main__":
    check()
