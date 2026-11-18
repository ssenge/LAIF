"""Exact ground energies of the public benchmark instances of Kipu Quantum
(https://github.com/Kipu-Quantum-GmbH/benchmark-instances), loaded from that repository at run time: the two 156-variable
HUBO instances on the Marrakesh coupling map and the weighted regular Max-Cut instances, by the eliminator of hubo.py
(instances whose elimination width exceeds WMAX are skipped). Usage: python -I kipu_benchmark.py"""
import os, sys, re, json, time, itertools, urllib.request
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from hubo import Eliminator, energy

BASE = "https://raw.githubusercontent.com/Kipu-Quantum-GmbH/benchmark-instances/main/"
FILES = ["HUBO/hubo1_marrakesh.json", "HUBO/hubo2_marrakesh.json", "maxcut/maxcut_regular_3_100_nodes_weighted.json",
         "maxcut/maxcut_regular_3_140_nodes_weighted.json", "maxcut/maxcut_regular_3_150_nodes_weighted.json",
         "maxcut/maxcut_regular_4_130_nodes_weighted.json"]
WMAX = 22

for f in FILES:
    raw = json.loads(urllib.request.urlopen(BASE + f, timeout=60).read().decode()); terms = []; const = 0.0
    for k, v in raw.items():
        idx = tuple(int(x) for x in re.findall(r"-?\d+", k))
        if idx: terms.append((tuple(sorted(idx)), float(v)))
        else: const += float(v)
    n = 1 + max(max(i) for i, _ in terms); El = Eliminator(n, terms)
    w = 0; G = nx.Graph()                                               # width of the order, without building tables
    G.add_nodes_from(range(n))
    for idx, _ in terms: G.add_edges_from(itertools.combinations(idx, 2))
    for v in El.order: nb = list(G[v]); w = max(w, len(nb) + 1); G.add_edges_from(itertools.combinations(nb, 2)); G.remove_node(v)
    if w > WMAX: print(f"{f}: n = {n}, elimination width {w} > {WMAX}, skipped", flush=True); continue
    t0 = time.perf_counter(); e0, z = El.ground(); dt = time.perf_counter() - t0
    assert abs(energy(terms, z)[0] - e0) < 1e-9
    print(f"{f}: n = {n}, {len(terms)} terms, elimination width {w}, exact ground energy {e0 + const:.4f} ({1e3 * dt:.0f} ms)", flush=True)
