"""Time-memory curve of the nested quantum k-tuple sieve, k = 3..6 (cost model of k4_chain.time_k, free chain angles).
For each memory bound M, minimize time over configurations with memory <= M; write curve.csv (M, k, time, memory, x).
Checks: k = 3 at the minimal 3-tuple memory gives 0.284551; k = 4 at the minimal 4-tuple memory gives 0.304495.
Run: python curve.py [seeds] (single core, about 30 minutes per seed)"""
import csv, sys
from math import log2, sqrt
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from k_general import evaluate
from scipy.optimize import differential_evolution

KNOWN = [(0.1395, 0.29893), (0.1887, 0.2846), (0.2075, 0.2563)]      # KMPM19 Table 2, 2510.08473, BCSS23

def known_best(M):
    return min(t for mem, t in KNOWN if mem <= M + 1e-9)

def best_time(k, M, x0=None, seed=0):
    def f(x):                             # soft penalty: the feasible set at minimal memory is a single point
        t, mem = evaluate(x, k)
        return 9 if mem is None else t + 20 * max(0.0, mem - M)
    r = differential_evolution(f, [(0.01, 0.99)] * (2 * (k - 1)), seed=seed, tol=1e-10, maxiter=3000, popsize=25,
                               x0=x0, polish=True)
    t, mem = evaluate(r.x, k)
    return (t, mem, r.x) if mem is not None and mem <= M + 1e-6 else (9, mem, r.x)

if __name__ == "__main__":
    SEEDS = int(sys.argv[1]) if len(sys.argv) > 1 else 1    # optimizer seeds per point (seed 0 warm-started)
    t3, m3 = evaluate([1 / 3, 1 / sqrt(3), 0.347606, 0.427124], 3)       # 2510.08473, Theorem 3.1
    assert abs(t3 - 0.284551) < 2e-6 and abs(m3 - 0.25 * log2(27 / 16)) < 1e-9, t3
    t4, m4 = evaluate([1 / 4, 1 / sqrt(6), sqrt(3 / 8), 0.23294119, 0.42108008, 0.42108008], 4)
    assert abs(t4 - 0.304495) < 1e-6 and abs(m4 - log2(256 / 125) / 6) < 1e-9, t4
    grid = [round(0.160 + 0.0025 * i, 4) for i in range(15)]           # 0.160 .. 0.195
    rows, prev = [], {}
    for M in grid:
        best = None
        for k in (3, 4, 5, 6):
            t, mem, x = min((best_time(k, M, prev.get(k) if sd == 0 else None, seed=sd) for sd in range(SEEDS)),
                            key=lambda r: r[0])
            if t < 9:
                prev[k] = x
                rows.append((M, k, t, mem, list(x)))
                if best is None or t < best[1]:
                    best = (k, t, mem)
        kb = known_best(M)
        print(f"M {M:.4f}: best k={best[0]} time {best[1]:.6f} (memory {best[2]:.6f}); known {kb:.4f}; gain {kb - best[1]:+.6f}", flush=True)
    with open("curve.csv", "w", newline="") as fh:
        w = csv.writer(fh); w.writerow(["M", "k", "time", "memory", "params"])
        for M, k, t, mem, x in rows:
            w.writerow([M, k, f"{t:.6f}", f"{mem:.6f}", " ".join(f"{v:.6f}" for v in x)])
    print("checks passed; curve.csv written")
