"""Per-N median-of-medians (median over the Sd seeds of each replicate, then over the R replicates) of both arms, their ratio,
the log-linear fit of each arm and the N where the two fit lines cross. Capped runs count as above the cap.
Usage: python -I per_n.py runs.jsonl[.gz] [unit]"""
import sys, json, gzip, collections
import numpy as np

def main(path, unit="children"):
    T = collections.defaultdict(dict)
    for l in (gzip.open(path, "rt") if path.endswith(".gz") else open(path)):
        if l.strip():
            d = json.loads(l); T[d["N"], d["arm"]].setdefault(d["r"], []).append(np.inf if d.get("capped") else d[unit])
    Ns = sorted({n for n, _ in T}); M = {}
    for a in ("rand", "bestR"):
        M[a] = np.array([np.median([np.median(v) for v in T[N, a].values()]) for N in Ns])
        assert np.all(np.isfinite(M[a]))                # every median lies below the cap
    f = {a: np.polyfit(Ns, np.log(M[a]), 1) for a in M}
    for N, r, b in zip(Ns, M["rand"], M["bestR"]): print(f"N={N}  rand {r:.0f}  bestR {b:.0f}  ratio {b / r:.2f}")
    for a in f: print(f"{a}: base {np.exp(f[a][0]):.4f}")
    print(f"fit lines cross at N = {(f['bestR'][1] - f['rand'][1]) / (f['rand'][0] - f['bestR'][0]):.1f}")
    return Ns, M

if __name__ == "__main__":
    if sys.argv[1] == "test":
        import tempfile, os
        p = os.path.join(tempfile.mkdtemp(), "t.jsonl")
        with open(p, "w") as fh:
            for N in (27, 28, 29):
                for a, c in (("rand", 10), ("bestR", 20)):
                    for r in range(3):
                        for s in range(3): fh.write(json.dumps({"N": N, "arm": a, "r": r, "s": s, "children": c * 2 ** N}) + "\n")
        Ns, M = main(p); assert np.allclose(M["bestR"] / M["rand"], 2)
        print("per_n self-checks passed"); sys.exit()
    Ns, M = main(*sys.argv[1:])
    print("seeded arm slower at every N:", bool(np.all(M["bestR"] > M["rand"])))
