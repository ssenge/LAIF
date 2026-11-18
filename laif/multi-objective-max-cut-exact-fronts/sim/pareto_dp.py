"""Exact Pareto set of multi-objective weighted Max-Cut by frontier dynamic programming.
Usage: python -I pareto_dp.py graph_0.json graph_1.json ...  (node-link JSON, edge attr 'weight')."""
import json, sys, time, itertools
import numpy as np
import networkx as nx
import moocore

def load(paths):
    gs = [nx.node_link_graph(json.load(open(p)), edges="links") if "links" in open(p).read() else nx.node_link_graph(json.load(open(p))) for p in paths]
    E = sorted({tuple(sorted(e)) for e in gs[0].edges()})
    W = np.array([[g.edges[u, v].get("weight", 1.0) for g in gs] for u, v in E])
    return list(gs[0].nodes()), E, W

def nondom(P):
    """Rows of P not weakly dominated by another row (maximization); duplicates kept once."""
    P = np.unique(P, axis=0)
    return P[moocore.is_nondominated(P, maximise=True)]

def order(nodes, E, coords=None):
    """Vertex order with a small frontier: BFS orders, plus coordinate sweeps if coordinates are given."""
    G = nx.Graph(E); G.add_nodes_from(nodes); best = None
    def bfs_all(s):                            # BFS from s, then the other components
        o = list(nx.bfs_tree(G, s)); seen = set(o)
        for c in nx.connected_components(G):
            if not c & seen: o += list(nx.bfs_tree(G, min(c)))
        return o
    cands = [bfs_all(s) for s in nodes]
    if coords:
        cands += [sorted(nodes, key=lambda v: (coords[v][0], coords[v][1])),
                  sorted(nodes, key=lambda v: (coords[v][1], coords[v][0]))]
    for o in cands:
        assert sorted(o, key=str) == sorted(nodes, key=str)
        pos = {v: i for i, v in enumerate(o)}
        last = {v: max([pos[v]] + [pos[u] for u in G[v]]) for v in o}
        w = max(sum(1 for v in o[:i + 1] if last[v] > i) for i in range(len(o)))
        if best is None or w < best[0]: best = (w, o, last, pos)
    return best

def pareto(nodes, E, W, coords=None, stats=None):
    m = W.shape[1]; w, o, last, pos = order(nodes, E, coords)
    adj = {v: [] for v in nodes}
    for k, (u, v) in enumerate(E): adj[u].append((v, k)); adj[v].append((u, k))
    states = {(): np.zeros((1, m))}; front = []
    for i, v in enumerate(o):
        new = {}
        for key, P in states.items():
            asg = dict(zip(front, key))
            for b in ((0,) if i == 0 else (0, 1)):   # fix the first vertex: cut symmetry
                add = np.zeros(m)
                for u, k in adj[v]:
                    if u in asg and asg[u] != b: add += W[k]
                nf = front + [v]; nk = key + (b,)
                keep = [j for j, x in enumerate(nf) if last[x] > i]
                kk = tuple(nk[j] for j in keep)
                new.setdefault(kk, []).append(P + add)
        front = [x for x in front + [v] if last[x] > i]
        states = {k: nondom(np.vstack(L)) for k, L in new.items()}
        if stats is not None:
            stats["max_labels"] = max(stats.get("max_labels", 0), sum(len(P) for P in states.values()))
    assert list(states) == [()]
    return w, states[()]

def selftest():
    rng = np.random.default_rng(1)
    G = nx.grid_2d_graph(3, 4); G = nx.convert_node_labels_to_integers(G)
    E = sorted(tuple(sorted(e)) for e in G.edges()); W = rng.normal(size=(len(E), 3))
    vals = []
    for bits in itertools.product((0, 1), repeat=G.number_of_nodes()):
        vals.append(sum(W[k] for k, (u, v) in enumerate(E) if bits[u] != bits[v]) + np.zeros(3))
    ref = nondom(np.array(vals)); _, got = pareto(list(G.nodes()), E, W)
    assert len(ref) == len(got) and np.allclose(np.sort(ref, axis=0), np.sort(got, axis=0)), (len(ref), len(got))

if __name__ == "__main__":
    selftest(); print("selftest ok")
    nodes, E, W = load(sys.argv[1:]); t = time.process_time()
    w, F = pareto(nodes, E, W)
    print(f"n={len(nodes)} m_edges={len(E)} objectives={W.shape[1]} frontier_width={w} pareto_points={len(F)} cpu_s={time.process_time()-t:.1f}")
    np.save(sys.argv[1] + ".front.npy", F)
