# Deterministic exact maximum flow, with the flow on every edge, in Õ(D) rounds

**Status.** Claim, written 21 Nov 2026. Proofs below, simulation in `sim/detflow/`. Parts 1 to 3 of the
Root Cut Lemma, part 4 for the vertices on the tree paths from x and y to the root, and the bound of
part 5 are formalized in `lean/SsspFlow/ForcedCut.lean`, for any rooted
tree and any prescribed first cut of two corners with b = 1. The phases of the levels and of the values with
this first cut, and the values of the root between the vertices on these tree paths in the memory of every
node, are formalized in `lean/SsspFlow/Output.lean` (`forced_root_values`); the facts about the face S, the
program that takes the two corners as local input with its round count, and the chain from (L3) to the flow
are not. The result improves the deterministic bound for exact maximum flow in directed planar networks
from Õ(D²) to Õ(D), and it gives the flow on every edge, which [3] asks for.

The model is CONGEST on a connected directed planar network with n vertices and hop diameter D, with
rotation lists of a planar embedding as input. Õ hides factors polylogarithmic in n. Statement names are
those of the README and of `notes/MAXFLOW.md`.

## 1. Result

**Deterministic Flow Theorem.** Let G be a directed planar network with terminals s ≠ t and integer
capacities in {0,…,U}, U = n^{O(1)}. Assume the three cited results of the Label Theorem: the
realization of metrics with the crossing inequalities by disks [4, Thm 1], the distance labels of
planar digraphs [5, Thm 3.16 and Thm 2.7] and face identifiers [2, Lemma 5.11], which are deterministic
by [6, Lemma 3.17] and [7, Thm 1.5]. Then every vertex learns
the value of a maximum st-flow, and the integer flow of a maximum st-flow on each of its edges, in Õ(D)
rounds, with messages of polylogarithmically many bits. Given the embedding, the algorithm is
deterministic. Local computation is not polynomial, as for the Label Theorem.

A minimum st-cut follows by reachability in the residual network. A path gives Ω(D), so the bound is
optimal up to polylogarithmic factors.

**Comparison.** The best deterministic bound for exact maximum flow with the flow on every edge was
Õ(D²), from [2] with the deterministic separator of [6]. `notes/NEGATIVE.md` gives Õ(D) with high
probability. [3] gives the value and a cut of a
(1−o(1))-approximate flow in undirected networks deterministically in Õ(D) rounds and asks for the flow
assignment.

**Proof.** `notes/MAXFLOW.md` proves the theorem from the Label Hypothesis and the extension (L3), with
every step deterministic relative to the labels. The Label Hypothesis is the Label Theorem, proved from
the three cited results by the disks of `notes/DISKS.md` (`labelHypothesis_of_boxes` in Lean). (L3)
follows from the same disks with a prescribed first cut, which is the Root Cut Lemma below. ∎

## 2. The Root Cut Lemma

We use the notation of `notes/DISKS.md`: the doubled map M, levels, the split, the cone, marks, the walks
up the tree, and `next`. Let S be a simple cycle that bounds a face F of G and consists of a path from b to a and one edge ab,
and let T be a rooted spanning tree of G of height h that contains this path and has its root on it.
Let x be the corner of F at a and y the corner of F at b, that is, the darts (d, 1) of M with d on the
boundary walk of F at a and at b.

**The sequence.** Γ_0 = {w_0}, with w_0 a corner with b = 1 at the root, Γ_1 = next(Γ_0, {x, y}), and
Γ_{d+1} = next(Γ_d, C_d) for d ≥ 1, where C_d is the cut of the rule of `notes/DISKS.md` §4 for every bag
of Γ_d.

**Root Cut Lemma.** Let 2n < 2^k.
1. Every Γ_d is a level. Every cut has at most two corners in each bag, and the pair property.
2. The counts of `notes/DISKS.md` §5 hold: a bag at depth d has at most 1 + d(2+4h) ports and at most
   1 + 2d gaps, two vertices of a bag are joined inside it by a walk of Õ(D) arcs when h = O(D), at most
   two bags of one depth contain an edge, and each bag has at most 1 + (H+1)(2+4h) hubs.
3. No vertex is without a corner in Γ_{1+3k}. So the hierarchy has height H ≤ 1 + 3k.
4. Every vertex of S has a corner in Γ_1. So every vertex of S is a hub of the root bag.
5. For hubs u, v of the root, the value δ(u, v) of the root bag satisfies
   dist(u, v) ≤ δ(u, v) ≤ (1 + 1/e)·dist(u, v), and every vertex of G computes all these values
   locally from the records that the algorithm gathers at depth 0, which have Õ(De) words.

*Proof.* (1) Γ_0 is a level. {x, y} has corners with b = 1 only, so the pair property holds, and both
lie in the one bag of Γ_0, which is all of M. So `IsLevel.next` applies at the first step, and the rule
gives the rest, as in `notes/DISKS.md`. The proof of the rule (`isCut_sel`) uses of the level only that
it is a level and contains w_0.

(2) Every count of §5 is proved by induction over the levels from the pair property and from at most two
corners per bag, and from the bound 2 + 4h on the corners that one cut adds to a bag (`card_railsUp_le`).
The balance of a cut is not used. The first cut adds two corners and two walks up the tree, as any cut.

(3) The number of marks of a component does not grow with the level (`npOf_mono`), so every component of
the split at Γ_1 has at most 2n marks. From Γ_1 on, every cut is balanced, so a component of the split at
Γ_{1+j} has at most 2n·(3/4)^j marks, and none after j = 3k levels, as in `Decomp.final`. Only the first
cut may be unbalanced, and in general it is: the side of F holds no vertex, so the other child keeps
the marks of all vertices off S.

(4) The walk up T from a corner adds the rails of every vertex on the path from it to the first vertex
with a corner, and the root has the corner w_0. The root lies on the path of S from b to a, which is a
path of T, so this path is the union of the paths from a and from b to the root. Each vertex on these paths gets its rails, unless it
already has a corner, and a, b get x, y.

(5) The values of the root are the values of `notes/DISKS.md` §6 for the bag of depth 0. Its subgraph is
all of G, so the bound is that of the estimates, with the distance along the arcs of the bag equal to
dist. In the algorithm the value call of depth 0 gathers the records of the ports of the children of the
root, at most 3 + 4h of them with labels of Õ(e) words each, in the memory of every node
(`values_of_run` in `lean/SsspFlow/NetValues.lean`), and every node computes the values from them. The
outputs of the Label Theorem export only the estimates of each vertex, so (L3) uses the memory, not the
outputs. ∎

**From the lemma to (L3).** In `notes/MAXFLOW.md` §4, S is the slit cycle of the network N, which bounds
a face of N, and T is S minus one edge plus a BFS forest of N from S, of height O(D) (Lemma N(3), (4)),
rooted at a vertex of S. N is simple once parallel edges are merged into one edge with the lightest arc
in each direction, as there.
Every vertex of N computes the values of the root of N, and these include δ on the corners of S, which
is (L3) with ε = 1/e. Section 5 of `notes/MAXFLOW.md`, which derives (L3) from the construction in
`notes/LEMMA15.md`, is not needed on this route.

**Rounds.** The first cut is decided locally: with the root on S, a dart is in Γ_1 if it is w_0, x, y,
or a rail of a vertex of S other than the root, and every vertex of N knows whether it lies on S, and
which of its edges are on S, after the broadcast of R. The names of the bags of Γ_1 come from the flood
of `notes/DISKS.md` §7.
Everything else is the algorithm of `notes/DISKS.md` §7, so the labels take Õ(De) rounds on N, and
Õ(De) rounds on G by Lemma N(1). With e = 12 and O(log nU) passes of the scaling, the total is Õ(D).

## 3. Checks

`sim/detflow/disks.py` implements the levels, the split, the cone, the tour of the marks and the rule as
in `lean/SsspFlow`, with the prescribed first cut. On grids, wheels, triangulations, sparse Delaunay
graphs, outerplanar graphs and trees with extra edges, with random directed lengths, it checks parts 1 to
4 of the lemma, and, with exact port metrics, that for every bag the least walks between its hubs through
the metrics of its children, with free moves at a vertex, equal the distances in the bag. At the root
these are the distances in G between the vertices of S. Two controls fire: about two thirds of the
prescribed first cuts are unbalanced, and without the free moves the values at the root are wrong.

`sim/detflow/pipeline.py` runs the whole chain on flow instances: the network N of `notes/MAXFLOW.md` §4,
the hierarchy with S as first cut, in every pass the values of the root of N on the corners of S, the
check of Lemma N(5) on them, a perturbation within [d, (1+ε)d] in place of the error of the labels, the
bounds of Lemma N(6), the Step Lemma and the exact finish. The value is compared with an independent
maximum flow, and feasibility, antisymmetry and conservation are checked on every edge. Results are in
`sim/detflow/REPORT.md`.

Not covered: rounds, messages and knowledge are not simulated. The cited results enter only through the
bound on the values; the scripts use exact port metrics and a perturbation, not realizations and labels.
Local computation is not polynomial.

## References

1. S. Senge. Exact shortest paths and flows on planar graphs. arXiv:2611.02256, and the README of this
   repository.
2. Y. Abd-Elhaleem, M. Dory, M. Parter, O. Weimann. Distributed Maximum Flow in Planar Graphs. PODC 2025,
   arXiv:2411.11718.
3. Y. Abd-Elhaleem, M. Dory, O. Weimann. Õptimal Distributed Maximum Flow Approximation in Undirected
   Planar Graphs. DISC 2026, arXiv:2608.09500.
4. Y. Chen, Z. Tan. Paths and Intersections: Characterization of Quasi-metrics in Directed
   Okamura-Seymour Instances. SODA 2025, arXiv:2410.19246.
5. M. Thorup. Compact oracles for reachability and approximate distances in planar digraphs. J. ACM 51(6),
   2004.
6. Y. Abd-Elhaleem, M. Dory, O. Weimann. A Simple Distributed Deterministic Planar Separator. SIROCCO
   2026, arXiv:2602.22916.
7. M. Ghaffari, B. Haeupler. Low-Congestion Shortcuts for Graphs Excluding Dense Minors.
   arXiv:2008.03091.
