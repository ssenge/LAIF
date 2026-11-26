"""Check of the reduction from a Gomory-Hu tree on all vertices to one on the terminals, by brute force.
A random weighted graph has terminals V and extra vertices K. A Gomory-Hu tree of the whole graph is computed,
and every node holding no terminal is merged into its neighbour along its heaviest tree edge, until every node
holds exactly one terminal. Asserted for every pair of terminals u, v: the smallest weight on the tree path
equals the minimum u-v cut value, and the side of that edge is a minimum u-v cut.
"""
import itertools, random
import networkx as nx

def cut(g, S):
    return sum(d["capacity"] for a, b, d in g.edges(data=True) if (a in S) != (b in S))

def terminal_tree(g, terms):
    T = nx.gomory_hu_tree(g, capacity="capacity")
    groups = {x: {x} for x in T.nodes}
    while True:
        bare = [x for x in T.nodes if not (groups[x] & terms)]
        if not bare:
            return T, groups
        y = bare[0]
        z = max(T.neighbors(y), key=lambda z: T[y][z]["weight"])
        for a in list(T.neighbors(y)):
            if a != z:
                T.add_edge(z, a, weight=T[y][a]["weight"])
        groups[z] |= groups.pop(y)
        T.remove_node(y)

random.seed(3)
pairs = 0
for trial in range(1500):
    nv, nk = random.randint(3, 7), random.randint(1, 4)
    nodes = list(range(nv + nk)); terms = set(range(nv))
    g = nx.Graph(); g.add_nodes_from(nodes)
    for a, b in itertools.combinations(nodes, 2):
        if random.random() < 0.6:
            g.add_edge(a, b, capacity=random.randint(1, 6))
    if not nx.is_connected(g):
        continue
    T, groups = terminal_tree(g, terms)
    assert all(len(groups[x] & terms) == 1 for x in T.nodes) and nx.is_tree(T)
    rep = {next(iter(groups[x] & terms)): x for x in T.nodes}
    for u, v in itertools.combinations(sorted(terms), 2):
        lam = nx.minimum_cut_value(g, u, v, capacity="capacity")
        path = nx.shortest_path(T, rep[u], rep[v])
        a, b = min(zip(path, path[1:]), key=lambda e: T[e[0]][e[1]]["weight"])
        assert T[a][b]["weight"] == lam
        T2 = T.copy(); T2.remove_edge(a, b)
        side = set().union(*[groups[x] for x in nx.node_connected_component(T2, rep[u])])
        assert u in side and v not in side and cut(g, side) == lam
        pairs += 1
print(f"{pairs} terminal pairs passed")
assert pairs >= 5000
