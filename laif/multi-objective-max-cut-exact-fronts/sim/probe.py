import sys, time, resource, numpy as np
sys.path.insert(0, ".")
from pareto_dp import pareto
from heavyhex import rows
import networkx as nx
k, m, seed = map(int, sys.argv[1:4]); kind = sys.argv[4] if len(sys.argv) > 4 else "hh"
if kind == "hh": G = rows(k)
else:                                          # square lattice, k rows of 12 (k = 10: 120 qubits)
    G = nx.convert_node_labels_to_integers(nx.grid_2d_graph(k, 12), label_attribute="xy")
    nx.set_node_attributes(G, {v: (G.nodes[v]["xy"][1], G.nodes[v]["xy"][0]) for v in G}, "pos")
E = sorted(tuple(sorted(e)) for e in G.edges())
W = np.random.default_rng(1000 * k + 10 * m + seed + (0 if kind == 'hh' else 7919)).normal(size=(len(E), m))
st = {}; t = time.process_time()
w, F = pareto(list(G.nodes()), E, W, coords=nx_pos if (nx_pos := {v: G.nodes[v]["pos"] for v in G}) else None, stats=st)
print(f"{kind} k={k} n={G.number_of_nodes()} m={m} seed={seed} width={w} front={len(F)} max_labels={st['max_labels']} cpu_s={time.process_time()-t:.1f} rss_mb={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/2**20:.0f}", flush=True)
