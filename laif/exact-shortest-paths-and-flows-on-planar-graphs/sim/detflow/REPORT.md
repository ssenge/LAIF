# Checks of the Root Cut Lemma and of the deterministic flow chain

Scripts for `notes/DETFLOW.md`. All runs use exact integer arithmetic. Logs are in `logs/`.

| Script | What it checks | Instances | Failures |
|---|---|---|---|
| `disks.py 11 600` | Parts 1 to 4 of the lemma; for every bag, values through the exact port metrics of its children equal the distances in the bag; at the root, the distances in G between the vertices of S | 42,413 graphs, 62.3 million bag values, 1.50 million root values | 0 |
| `disks.py 12 120 bal0 nofree` | Controls: unbalanced first cuts are counted; without free moves at a vertex the root values must be wrong | 9,417 graphs; 6,519 unbalanced first cuts; 72,684 wrong root values caught | 0 |
| `stress.py 31 300` | Any tree containing S minus ab, with the root anywhere (DFS-like and random trees); per level the connected skeleton, ports on one cycle of ψ, tour cycle equal to the bag, genus 0, port, gap and hub counts, walk lengths in bags, congestion, pair property, balance from level 1 on, height; all root hub values | 79,578 graphs, 5.62 million root values | 0 |
| `pipeline.py 21 600` | The whole chain on flow instances: the network N, the hierarchy with S as first cut, Lemma N(5) on the root values, perturbed values, Lemma N(6), Step Lemma, exact finish; value against an independent maximum flow; feasibility, antisymmetry and conservation | 3,449 flows, 23,468 scaling passes, 659,306 portal bounds | 0 |
| `pipeline.py 22 900 big` | As above on larger networks, slit cycles up to 104 nodes | 1,121 flows, 8,342 scaling passes, 524,833 portal bounds | 0 |

Families: grids, wheels and wheel rims, Delaunay triangulations and sparse subgraphs, outerplanar graphs,
trees with extra edges, cycles with and without chords, fans, chains of K4, ladders, subdivisions, pendant
trees, and the networks N of `notes/MAXFLOW.md` §4. Lengths are random and directed, from 1 to 10⁶, some
with 1 in one direction and the maximum in the other. The largest hierarchy had 14 levels, within 1 + 3k.

Not covered: rounds, messages and knowledge; the cited realizations and labels, which are replaced by
exact port metrics and, in `pipeline.py`, by a perturbation of the root values within [d, (1+ε)d].
