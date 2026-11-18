"""Classical replica-exchange MCMC for maximum independent set with a structure-aware proposal, on the animal interaction
graphs of arXiv:2602.06171 (QOBLIB / Network Repository). The chain stays on independent sets: a proposal picks a uniform
vertex v; if v is in the set it is removed, otherwise v is added and its neighbours in the set are removed. Energy -|I|,
Metropolis acceptance, 5 replicas on the temperature ladder of that paper (0.01, 0.11, 0.21, 0.51, 1.01), neighbour exchange
every 10 iterations, start from the empty set. One iteration = one proposal per replica = 5 cost evaluations.
Counts iterations until some replica first reaches the optimum (CP-SAT), over many independent runs.
Usage: python -I mis_mcmc.py <graph file (.gph or .edges)> [runs]"""
import sys, time, numpy as np
from numba import njit
from ortools.sat.python import cp_model

def load(p):
    """Vertices 1..max id (isolated ids kept, as in the paper's 117-node instance); simple undirected edges."""
    L = [l.split() for l in open(p) if l.strip() and l[0] not in "c%p"]
    E = {(min(u, v), max(u, v)) for u, v in ((int(a[-2]), int(a[-1])) if a[0] == "e" else (int(a[0]), int(a[1])) for a in L) if u != v}
    n = max(max(e) for e in E)
    hdr = [l.split() for l in open(p) if l.startswith("p ")]
    if hdr: n = max(n, int(hdr[0][2]))
    return n, sorted((u - 1, v - 1) for u, v in E)

def optimum(n, E):
    m = cp_model.CpModel(); x = [m.NewBoolVar("") for _ in range(n)]
    for u, v in E: m.Add(x[u] + x[v] <= 1)
    m.Maximize(sum(x)); s = cp_model.CpSolver(); s.parameters.num_workers = 1
    assert s.Solve(m) == cp_model.OPTIMAL
    return int(s.ObjectiveValue())

@njit(cache=True)
def run(ptr, nbr, n, target, T, max_it, swap_every, seed):
    np.random.seed(seed); R = len(T)
    ins = np.zeros((R, n), np.bool_); conf = np.zeros((R, n), np.int64)   # conf[r, v] = neighbours of v in the set
    size = np.zeros(R, np.int64); temp = np.arange(R)                      # temp[r] = ladder index of replica r
    for it in range(1, max_it + 1):
        for r in range(R):
            v = np.random.randint(n)
            dE = 1 if ins[r, v] else conf[r, v] - 1
            if dE <= 0 or np.random.random() < np.exp(-dE / T[temp[r]]):
                if ins[r, v]:
                    ins[r, v] = False; size[r] -= 1
                    for k in range(ptr[v], ptr[v + 1]): conf[r, nbr[k]] -= 1
                else:
                    for k in range(ptr[v], ptr[v + 1]):
                        u = nbr[k]
                        if ins[r, u]:
                            ins[r, u] = False; size[r] -= 1
                            for j in range(ptr[u], ptr[u + 1]): conf[r, nbr[j]] -= 1
                    ins[r, v] = True; size[r] += 1
                    for k in range(ptr[v], ptr[v + 1]): conf[r, nbr[k]] += 1
            if size[r] == target:
                for a in range(n):                                          # check: the state is an independent set
                    if ins[r, a]:
                        for k in range(ptr[a], ptr[a + 1]): assert not ins[r, nbr[k]]
                return it
        if it % swap_every == 0:
            for a in range(R - 1):                                          # exchange between neighbouring temperatures
                ra = np.argmax(temp == a); rb = np.argmax(temp == a + 1)
                d = (1 / T[a] - 1 / T[a + 1]) * (size[ra] - size[rb])     # energies are -size
                if d <= 0 or np.random.random() < np.exp(-d):
                    temp[ra], temp[rb] = a + 1, a
    return -1

if __name__ == "__main__":
    n, E = load(sys.argv[1]); runs = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
    opt = optimum(n, E)
    adj = [[] for _ in range(n)]
    for u, v in E: adj[u].append(v); adj[v].append(u)
    ptr = np.cumsum([0] + [len(a) for a in adj]); nbr = np.array([x for a in adj for x in a], np.int64)
    T = np.array([0.01, 0.11, 0.21, 0.51, 1.01])
    run(ptr, nbr, n, opt, T, 10, 10, 0)                                     # compile
    t0 = time.perf_counter(); its = np.array([run(ptr, nbr, n, opt, T, 200_000, 10, s) for s in range(runs)]); dt = (time.perf_counter() - t0) / runs
    assert (its > 0).all()
    print(f"{sys.argv[1].split('/')[-1]}: n={n} edges={len(E)} MIS={opt} runs={runs} iterations to optimum: median={np.median(its):.0f} "
          f"p95={np.percentile(its, 95):.0f} max={its.max()}; cost evaluations (5 per iteration): median={5 * np.median(its):.0f} p95={5 * np.percentile(its, 95):.0f}; wall time per run {1e3 * dt:.3f} ms")
