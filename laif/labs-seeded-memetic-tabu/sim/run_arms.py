"""Time-to-solution of memetic tabu search on LABS, N = 27..37, for three initial populations (see mts.py): rand, bestR and
sa, with S = 100 000 seed evaluations for bestR and sa (the shot count of the DCQO seeds in arXiv:2511.04553). R replicates
(distinct initial populations) x Sd MTS seeds each. Output: one JSON line per run. Runs already in out.jsonl (same N, arm, r, s; every run is deterministic in these) are skipped, so a stopped run resumes.
Usage: python -I run_arms.py R Sd out.jsonl [Nmin Nmax [arms]]"""
import os, sys, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from mts import mts, best_random, sa, E_OPT

R, Sd, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]; NS = range(int(sys.argv[4]), int(sys.argv[5]) + 1) if len(sys.argv) > 5 else range(27, 38); ARMS = sys.argv[6].split(",") if len(sys.argv) > 6 else ("rand", "bestR", "sa"); S = 100_000; K = 100
done = set()
if os.path.exists(out):
    for l in open(out):
        if l.strip(): d = json.loads(l); done.add((d["N"], d["arm"], d["r"], d["s"]))
with open(out, "a") as f:
    for N in NS:
        for arm in ARMS:
            t0 = time.perf_counter()
            for r in range(R):
                todo = [s for s in range(Sd) if (N, arm, r, s) not in done]
                if not todo: continue
                if arm == "rand":
                    pop = np.random.default_rng(10_000 * N + r).choice([-1, 1], (K, N)).astype(np.int64); e0 = None
                else:
                    s0, e0 = (best_random if arm == "bestR" else sa)(N, S, 10_000 * N + r)
                    pop = np.tile(s0, (K, 1)); e0 = int(e0)
                for s in todo:
                    cn, e = mts(pop, E_OPT[N], 10**9, 1_000_000 * N + 1000 * r + s, 0); c = cn[0]
                    assert c > 0 and e == E_OPT[N]
                    f.write(json.dumps({"N": N, "arm": arm, "r": r, "s": s, "tts": int(c), "steps": int(cn[1]), "children": int(cn[2]), "seed_cost": 0 if arm == "rand" else S,
                                        "seed_energy": e0}) + "\n")
                f.flush()
            f.flush(); print(f"N={N} {arm}: {time.perf_counter() - t0:.0f} s", flush=True)
