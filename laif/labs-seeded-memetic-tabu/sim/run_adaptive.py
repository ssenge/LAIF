"""Capped, sequential run of the rand and bestR arms of run_arms.py at one N, for the median statistic of arXiv:2511.04553
Sec. IV A (median over seeds per replicate, then the median over replicates).
Each MTS run stops at CAP children; a capped run is recorded with capped = true and counts as "above the cap", so every
median below the cap is exact (checked: the capped fraction must stay below 1/2). CAP = 4 x the larger of the two arms'
median children extrapolated log-linearly from N - 5 .. N - 1 in out.jsonl. Replicates come in batches of B per arm (same
seeds and populations as run_arms.py, so records are interchangeable); after each batch (from RMIN on) the two-stage
bootstrap 95% CIs of both arms' median-of-medians are compared, and the run stops once they are disjoint or at RMAX.
Already recorded (N, arm, r, s) are skipped. Usage: python -I run_adaptive.py N out.jsonl [Sd B RMIN RMAX]"""
import os, sys, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from mts import mts, best_random, E_OPT

S, K = 100_000, 100

def load(out):
    recs = []
    if os.path.exists(out):
        for l in open(out):
            if l.strip(): recs.append(json.loads(l))
    return recs

def cap_for(recs, N, arms):
    """4 x the larger arm's median children, extrapolated from the five sizes below N (log-linear least squares)."""
    best = 0.0
    for arm in arms:
        Ns = [n for n in range(N - 5, N) if any(r["N"] == n and r["arm"] == arm for r in recs)]
        y = [np.log(np.median([r["children"] for r in recs if r["N"] == n and r["arm"] == arm])) for n in Ns]
        a, b = np.polyfit(Ns, y, 1); best = max(best, np.exp(a * N + b))
    return int(np.ceil(4 * best))

def medmed(X):                                          # X: (R, Sd) children, capped runs at +inf
    return np.median(np.median(X, 1))

def boot_ci(X, rng, B=1000):
    R, Sd = X.shape; v = np.empty(B)
    for b in range(B):
        Y = X[rng.integers(0, R, R)]; Y = np.take_along_axis(Y, rng.integers(0, Sd, (R, Sd)), 1); v[b] = medmed(Y)
    return np.percentile(v, [2.5, 97.5]), v

def table(recs, N, arm, Sd):
    by = {}
    for r in recs:
        if r["N"] == N and r["arm"] == arm: by.setdefault(r["r"], {})[r["s"]] = np.inf if r.get("capped") else r["children"]
    full = sorted(k for k, v in by.items() if len(v) == Sd)
    return np.array([[by[k][s] for s in range(Sd)] for k in full]) if full else np.zeros((0, Sd))

def run(N, out, Sd=50, B=5, RMIN=10, RMAX=50, arms=("rand", "bestR")):
    recs = load(out); cap = cap_for(recs, N, arms); done = {(r["N"], r["arm"], r["r"], r["s"]) for r in recs}
    print(f"N={N} cap {cap} children", flush=True)
    with open(out, "a") as f:
        for r0 in range(0, RMAX, B):
            for arm in arms:
                for r in range(r0, r0 + B):
                    todo = [s for s in range(Sd) if (N, arm, r, s) not in done]
                    if not todo: continue
                    if arm == "rand":
                        pop = np.random.default_rng(10_000 * N + r).choice([-1, 1], (K, N)).astype(np.int64); e0 = None
                    else:
                        s0, e0 = best_random(N, S, 10_000 * N + r); pop = np.tile(s0, (K, 1)); e0 = int(e0)
                    for s in todo:
                        cn, e = mts(pop, E_OPT[N], cap, 1_000_000 * N + 1000 * r + s, 0); capped = bool(cn[0] < 0)
                        assert capped or e == E_OPT[N]
                        rec = {"N": N, "arm": arm, "r": r, "s": s, "tts": None if capped else int(cn[0]), "steps": int(cn[1]),
                               "children": int(cn[2]), "seed_cost": 0 if arm == "rand" else S, "seed_energy": e0,
                               "capped": capped, "cap": cap}
                        f.write(json.dumps(rec) + "\n"); recs.append(rec)
                    f.flush()
            if r0 + B < RMIN: continue
            rng = np.random.default_rng(N); T = {a: table(recs, N, a, Sd) for a in arms}; ci = {}
            for a in arms:
                X = T[a]; frac = float(np.isinf(X).mean()); (lo, hi), v = boot_ci(X, rng); ci[a] = (lo, hi, v)
                print(f"N={N} {a} R={len(X)} median-of-medians {medmed(X):.0f} CI [{lo:.0f}, {hi:.0f}] capped {frac:.3f}", flush=True)
                assert frac < 0.5, "median not exact: half the runs are capped"
            ratio = ci["bestR"][2] / ci["rand"][2]
            print(f"N={N} R={r0 + B} ratio bestR/rand {medmed(T['bestR']) / medmed(T['rand']):.3f} "
                  f"CI [{np.percentile(ratio, 2.5):.3f}, {np.percentile(ratio, 97.5):.3f}]", flush=True)
            a, b = arms
            if ci[a][1] < ci[b][0] or ci[b][1] < ci[a][0]:
                print(f"N={N} separated at R={r0 + B}", flush=True); return
    print(f"N={N} not separated at R={RMAX}", flush=True)

if __name__ == "__main__":
    if sys.argv[1] == "test":                           # a capped run counts as above the cap; medians below it are exact
        X = np.array([[1.0, 2, np.inf], [3, np.inf, np.inf], [1, 1, 2]]); assert medmed(X) == 2
        rng = np.random.default_rng(0); (lo, hi), _ = boot_ci(np.array([[5.0] * 4] * 6), rng, 50); assert lo == hi == 5
        cn, e = mts(np.random.default_rng(0).choice([-1, 1], (K, 27)).astype(np.int64), E_OPT[27], 3, 1, 0)
        assert cn[0] < 0 and cn[2] == 3                 # cap = 3 children: not solved, flagged
        print("run_adaptive self-checks passed"); sys.exit()
    a = sys.argv[3:]; run(int(sys.argv[1]), sys.argv[2], *map(int, a))
