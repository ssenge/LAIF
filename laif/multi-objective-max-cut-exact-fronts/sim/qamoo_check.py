"""Exact Pareto sets of the 42-node benchmark instances of arXiv:2503.22797 (data: github.com/stefan-woerner/qamoo).
Usage: python -I qamoo_check.py <dir>, where <dir>/3o and <dir>/4o hold the files problem_graph_<j>.json and
lower_bounds.json (the hypervolume reference point) of data/problems/42q/problem_set_42q_0s_3o_0 and ..._4o_0."""
import json, os, sys, time
import numpy as np, moocore
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pareto_dp import load, pareto
from hv3 import hv3

BEST = {3: (43471.704, 2067), 4: (1266143.350, 30419)}     # best HV stated in [1]; points of the DPA-a set [1] and annealing [2]
for m in (3, 4):
    d = os.path.join(sys.argv[1], f"{m}o")
    nodes, E, W = load([os.path.join(d, f"problem_graph_{j}.json") for j in range(m)])
    assert (len(nodes), len(E), W.shape[1]) == (42, 46, m)
    t = time.process_time(); w, F = pareto(nodes, E, W); cpu = time.process_time() - t
    r = np.array(json.load(open(os.path.join(d, "lower_bounds.json"))))
    hv = moocore.hypervolume(F, ref=r, maximise=True)
    if m == 3: assert abs(hv - hv3(F, r)) < 1e-6 * hv
    assert len(F) == BEST[m][1] and abs(hv - BEST[m][0]) < 1e-3, (len(F), hv)
    np.save(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data", f"front_42q_{m}o.npy"), F)
    print(f"m={m} width={w} pareto_points={len(F)} HV={hv:.4f} cpu_s={cpu:.1f}")
