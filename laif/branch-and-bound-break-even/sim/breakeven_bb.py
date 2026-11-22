"""Break-even logical clock rates for quantum tree search on measured SCIP trees (QOBLIB instances).

Quantum cost, lower bound (favourable to the quantum side):
  detection of a marked node in a tree of T nodes and depth d by the quantum backtracking walk, phase-estimation depth
  32 sqrt(T d) walk steps (b = 1/32, [arXiv:1810.05582, Sec. 4.1]; the K = 79 repetitions run in parallel and are not counted).
  Finding the optimum of a branch-and-bound needs this at least once on the tree pruned at the optimal value.
  Each walk step evaluates the node bound at least twice (compute and uncompute): 2 * G logical-T depth per step.
Classical cost: wall time of the faster of SCIP and CP-SAT (one core each) on the full solve.
Per-node quantum cost model G: (LP iterations per node) * C_PIV, C_PIV = 1e3 T-depth per pivot (one 32-bit division and
  a comparison tree, an optimistic floor), and at least C_PIV per node.
Hybrid: classical root and top levels down to depth h, quantum search on each subtree below, either on one QPU in
  sequence (sum over subtrees) or on one QPU per subtree in parallel (max over subtrees)."""
import json, sys, math, os
import numpy as np

C_WALK = 32.0
C_PIV = 1e3

def analyse(r):
    T, d = r["nodes"], max(r["maxdepth"], 1)
    sc = r["time"] if r["status"] == "optimal" else math.inf
    cp = r["cpsat"]["wall"] if "OPTIMAL" in str(r["cpsat"].get("status")) else math.inf
    tc = min(sc, cp)
    iters = r.get("lp_iters", 0) / max(T, 1)
    G = max(iters, 1.0) * C_PIV
    W = C_WALK * math.sqrt(T * d)
    out = {"file": r["file"], "T": T, "d": d, "t_scip": sc, "t_cpsat": cp, "t_classical": tc, "lp_iters_per_node": iters,
           "G_model": G, "walk_steps": W,
           "f_breakeven_Hz": 2 * W * G / tc,                     # clock at which the quantum detection depth equals tc
           "G_star_at_10MHz": 1e7 * tc / (2 * W)}                # per-node T-depth budget at a 10 MHz logical clock
    best_par, best_seq = None, None
    for h, v in r["frontier"].items():
        h = int(h)
        t_top = r["t_root"] + v["top_nodes"] * sc / max(T, 1)
        if t_top >= tc:
            continue
        for kind, Wh in (("parallel", C_WALK * v["max_sqrt_Td"]), ("sequential", C_WALK * v["sum_sqrt_Td"])):
            f = 2 * Wh * G / (tc - t_top)
            cand = {"h": h, "n_qpu": v["n_sub"] if kind == "parallel" else 1, "f_breakeven_Hz": f}
            if kind == "parallel" and (best_par is None or f < best_par["f_breakeven_Hz"]):
                best_par = cand
            if kind == "sequential" and (best_seq is None or f < best_seq["f_breakeven_Hz"]):
                best_seq = cand
    out["hybrid_sequential"], out["hybrid_parallel"] = best_seq, best_par
    return out

if __name__ == "__main__":
    if sys.argv[1] == "test":                     # T = 100, d = 4: 32 sqrt(400) = 640 walk steps; 2 * 640 * 1e3 / 0.064 s = 2e7 Hz
        a = analyse({"file": "t", "nodes": 100, "maxdepth": 4, "time": 0.064, "status": "optimal", "cpsat": {"status": "x"}, "lp_iters": 50, "frontier": {}, "t_root": 0})
        assert abs(a["walk_steps"] - 640) < 1e-9 and abs(a["f_breakeven_Hz"] - 2e7) < 1e-3, a
        print("breakeven_bb self-check passed"); sys.exit()
    rows = [json.loads(l) for l in open(sys.argv[1])]
    cls = {l.split()[3].split("/")[-1]: l.split()[0] for l in open(sys.argv[2] if len(sys.argv) > 2 else "instances.txt")}
    res = []
    for r in rows:
        cp_ok = "OPTIMAL" in str(r["cpsat"].get("status"))
        if r["status"] != "optimal" and not cp_ok:
            print("skip (neither solver finished in the limit)", r["file"], r["status"], r["nodes"]); continue
        if r["nodes"] < 2:
            print("skip (solved at the root, no tree)", r["file"]); continue
        a = analyse(r); a["class"] = cls.get(r["file"], "?")
        a["tree_partial"] = r["status"] != "optimal"     # SCIP stopped: T is a lower bound, so f* is a lower bound too
        res.append(a)
    with open(os.path.join(os.path.dirname(sys.argv[1]), "breakeven_bb.jsonl"), "w") as f:
        for a in res:
            f.write(json.dumps(a) + "\n")
    print(f"{'class':15s} {'file':22s} {'T':>9s} {'d':>4s} {'t_c[s]':>8s} {'it/node':>7s} {'f* [Hz]':>9s} {'G*@10MHz':>9s} {'seq f*':>9s} {'par f* (QPUs)':>16s}")
    for a in sorted(res, key=lambda a: (a["class"], a["T"])):
        hp = a["hybrid_parallel"]; hs = a["hybrid_sequential"]
        print(f"{a['class']:15s} {a['file'][:22]:22s} {a['T']:9d} {a['d']:4d} {a['t_classical']:8.3f} {a['lp_iters_per_node']:7.1f} {a['f_breakeven_Hz']:9.2e} {a['G_star_at_10MHz']:9.2e} "
              f"{(hs['f_breakeven_Hz'] if hs else float('nan')):9.2e} {(hp['f_breakeven_Hz'] if hp else float('nan')):9.2e} ({hp['n_qpu'] if hp else '-'})")
