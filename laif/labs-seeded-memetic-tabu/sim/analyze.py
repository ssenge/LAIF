"""Scaling base kappa of the TTS of each seeding arm, as in arXiv:2511.04553 Sec. IV A: per-replicate median over seeds,
quantile Q_p over replicates, log Q_p = alpha + N log kappa over N = 27..37, two-stage bootstrap (replicates, then seeds
within each) for 95% CIs. Column 'incl': TTS + seed cost (S evaluations for bestR and sa).
unit: 'tts' (objective evaluations, default) or 'children' / 'steps'. Runs flagged capped (run_adaptive.py) count as +inf,
so a quantile is exact only while it stays below every cap; R may differ between N. A quantile whose point value or more
than 2.5% of bootstrap draws hit +inf is reported as not exact.
Usage: python -I analyze.py runs.jsonl[.gz] [B [unit]];  python -I analyze.py test"""
import sys, json, gzip, collections, tempfile, os
import numpy as np

def fit(Ns, Q):
    b, a = np.polyfit(Ns, np.log(Q), 1); r = np.log(Q) - (a + b * np.array(Ns))
    return np.exp(b), 1 - r.var() / np.log(Q).var()

def main(path, B=2000, unit="tts"):
    D = collections.defaultdict(lambda: collections.defaultdict(list))
    for l in (gzip.open(path, "rt") if path.endswith(".gz") else open(path)):
        if not l.strip(): continue
        d = json.loads(l); D[d["arm"], d["N"]][d["r"]].append((np.inf if d.get("capped") else d[unit], d["seed_cost"]))
    arms = sorted({a for a, _ in D}, key=["rand", "bestR", "sa"].index); Ns = sorted({n for _, n in D})
    rng = np.random.default_rng(0); out = {}
    for arm in arms:
        Sd = max(len(v) for n in Ns for v in D[arm, n].values())        # complete replicates only
        Y = {n: np.array([[t for t, _ in D[arm, n][r]] for r in sorted(D[arm, n]) if len(D[arm, n][r]) == Sd], float) for n in Ns}   # (R, Sd)
        S = D[arm, Ns[0]][0][0][1]
        for incl in (False, True):
            if incl and (S == 0 or unit != "tts"): continue                # seed cost is in evaluations
            for p in (0.1, 0.5, 0.9):
                Q = [np.quantile(np.median(Y[n] + S * incl, 1), p, method="lower") if np.isinf(Y[n]).any() else np.quantile(np.median(Y[n] + S * incl, 1), p) for n in Ns]
                if not np.all(np.isfinite(Q)): print(f"{arm:6s} Q{p:.2f}: not exact (above the cap at some N)"); continue
                k, R2 = fit(Ns, Q); ks = []
                for _ in range(B):
                    Qb = []
                    for n in Ns:
                        R, Sd = Y[n].shape; rr = rng.integers(0, R, R)
                        Yb = np.take_along_axis(Y[n][rr], rng.integers(0, Sd, (R, Sd)), 1) + S * incl
                        Qb.append(np.quantile(np.median(Yb, 1), p))
                    ks.append(fit(Ns, Qb)[0] if np.all(np.isfinite(Qb)) else np.nan)
                ks = np.array(ks); bad = np.isnan(ks).mean()
                if bad > 0.025: print(f"{arm:6s} Q{p:.2f}: not exact ({bad:.1%} of draws above the cap)"); continue
                lo, hi = np.quantile(np.where(np.isnan(ks), np.inf, ks), [0.025, 0.975])
                out[arm, incl, p] = (k, lo, hi, R2, Q)
                print(f"{arm:6s} {'incl' if incl else 'excl'} Q{p:.2f}: kappa {k:.4f} [{lo:.4f}, {hi:.4f}] R2 {R2:.3f}  "
                      f"Q({Ns[0]}) {Q[0]:.3g} Q({Ns[-1]}) {Q[-1]:.3g}")
    print("R x Sd per N:", {n: Y[n].shape for n in Ns})
    return out

if __name__ == "__main__":
    if sys.argv[1] == "test":                           # synthetic data with TTS = 3 * 1.3^N exactly: the fit returns 1.3
        p = os.path.join(tempfile.mkdtemp(), "t.jsonl")
        with open(p, "w") as f:
            for N in range(27, 32):
                for r in range(4):
                    for s in range(3): f.write(json.dumps({"N": N, "arm": "rand", "r": r, "s": s, "tts": 3 * 1.3 ** N, "seed_cost": 0}) + "\n")
        o = main(p, 20)
        for p_ in (0.1, 0.5, 0.9): k, lo, hi, R2, _ = o["rand", False, p_]; assert abs(k - 1.3) < 1e-9 and abs(lo - 1.3) < 1e-9 and abs(hi - 1.3) < 1e-9
        with open(p, "a") as f: f.write(json.dumps({"N": 31, "arm": "rand", "r": 4, "s": 0, "tts": 1, "capped": True, "seed_cost": 0}) + "\n")
        assert ("rand", False, 0.5) in main(p, 20)          # an incomplete replicate is left out
        print("analyze self-checks passed"); sys.exit()
    main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 2000, sys.argv[3] if len(sys.argv) > 3 else "tts")
