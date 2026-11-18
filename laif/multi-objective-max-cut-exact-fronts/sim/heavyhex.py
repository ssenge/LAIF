"""Heavy-hex lattice of 156-qubit processors (8 rows of 16, 4 bridge qubits between rows) with coordinates."""
import networkx as nx

def heron156():
    G = nx.Graph(); pos = {}
    for r in range(8):
        for c in range(16):
            q = 20 * r + c; pos[q] = (c, 2 * r)
            if c: G.add_edge(q - 1, q)
        if r < 7:
            cols = (3, 7, 11, 15) if r % 2 == 0 else (1, 5, 9, 13)
            for j, c in enumerate(cols):
                b = 20 * r + 16 + j; pos[b] = (c, 2 * r + 1)
                G.add_edge(20 * r + c, b); G.add_edge(b, 20 * (r + 1) + c)
    nx.set_node_attributes(G, pos, "pos")
    return G

def rows(k):
    """Connected patch: the first k rows and their bridges."""
    G = heron156()
    keep = [q for q in G if G.nodes[q]["pos"][1] <= 2 * (k - 1)]
    return G.subgraph(keep).copy()

if __name__ == "__main__":
    G = heron156(); assert G.number_of_nodes() == 156 and G.number_of_edges() == 176 and max(d for _, d in G.degree()) == 3
    for k in range(2, 9): H = rows(k); print(k, H.number_of_nodes(), H.number_of_edges(), nx.is_connected(H))
