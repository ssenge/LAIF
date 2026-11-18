"""Instances of arXiv:2611.05883: the N = 144 heavy-hex graph whose edges are the two-vertex blocks of its Table II, and
the N = 1064 graph made of a 3 x 3 array of copies (the heavy-hex subdivision of a 9 x 21 hexagonal patch), with the
49-vertex blocks of Table II repeated in every copy (36 blocks)."""
import json, os
import numpy as np, networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
TABLE = json.load(open(os.path.join(HERE, "..", "data", "table2_blocks.json")))

def heavy(H):
    G = nx.Graph()
    for u, v in H.edges(): m = ("m",) + tuple(sorted((u, v))); G.add_edge(u, m); G.add_edge(m, v)
    return G

def g144():
    """Vertices 0..143 (Table II index minus 1); the 49-vertex blocks of Table II."""
    E = sorted({tuple(sorted((u - 1, v - 1))) for fam in ("2A", "2B") for u, v in TABLE[fam]})
    blocks = [[v - 1 for v in B] for B in TABLE["49A"]]
    G = nx.Graph(E)
    assert G.number_of_nodes() == 144 and len(E) == 164 and nx.is_connected(G)
    assert nx.is_isomorphic(G, heavy(nx.hexagonal_lattice_graph(3, 7)))
    assert all(len(B) == 49 and G.subgraph(B).number_of_edges() == 54 for B in blocks)
    return 144, E, blocks

def cells_of(H, rows, cols):
    """Hexagonal faces of nx.hexagonal_lattice_graph(rows, cols) as a rows x cols grid: a face with least node (i, j)
    lies in column i and row j // 2."""
    C = [[None] * cols for _ in range(rows)]
    for c in nx.minimum_cycle_basis(H):
        assert len(c) == 6
        i, j = min(v[0] for v in c), min(v[1] for v in c); C[j // 2][i] = frozenset(c)
    assert all(f is not None for r in C for f in r)
    return C

def g1064():
    n, E144, B144 = g144(); G144 = nx.Graph(E144)
    H = nx.hexagonal_lattice_graph(9, 21); C = cells_of(H, 9, 21)
    big = heavy(H); idx = {v: i for i, v in enumerate(sorted(big.nodes(), key=str))}
    blocks = []
    for P in range(3):
        for Q in range(3):
            hexes = [C[r][c] for r in range(3 * P, 3 * P + 3) for c in range(7 * Q, 7 * Q + 7)]
            base = set().union(*hexes)
            sub = heavy(H.subgraph(base).edge_subgraph([(u, v) for u, v in H.subgraph(base).edges()
                                                         if any({u, v} <= h for h in hexes)]))
            assert sub.number_of_nodes() == 144 and sub.number_of_edges() == 164
            m = nx.vf2pp_isomorphism(G144, sub); assert m is not None
            blocks += [[idx[m[v]] for v in B] for B in B144]
    E = sorted({tuple(sorted((idx[u], idx[v]))) for u, v in big.edges()})
    G = nx.Graph(E)
    assert G.number_of_nodes() == 1064 and len(E) == 1252 and len(blocks) == 36
    assert all(len(B) == 49 and G.subgraph(B).number_of_edges() == 54 for B in blocks)
    assert len(set().union(*map(set, blocks))) == 1064
    return 1064, E, blocks

if __name__ == "__main__":
    for f in (g144, g1064):
        n, E, B = f(); print(f.__name__, n, len(E), len(B), "blocks of", {len(b) for b in B})
