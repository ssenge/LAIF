# Exact distance labels and offsets in Õ(D²) rounds, with no hypothesis

**Status.** Claim, written 3 Nov 2026. Proof below, simulation in `sim/labels.py`, the distance formula of Lemma 1 in Lean (`lean/PlanarMatching/Labels.lean`). No human has checked it. Importance: modest. The method is the classical bottom-up one. Labels are in [1] for undirected networks, and [2, Lemma 4] states directed shortest paths from a set S of sources in Õ(D² + D·|S|) rounds. What this note adds is a complete proof for digraphs, whose proof [2] defers to its full version, and the use of the labels with arbitrary offsets, which keeps the bound free of the number of sources.

The model is CONGEST on a connected planar network G with n vertices and hop diameter D. Õ hides factors polylogarithmic in n. A *digraph on G* has its arcs on edges of G, with nonnegative integer lengths of polynomial size, zero allowed.

## 1. Results

**Lemma 1 (exact labels).** Fix a BDD of G with the properties (B1) to (B4) of `notes/MATCHING.md`. Let sep⁺(X) be sep(X) together with the separators of all ancestors of X. In Õ(D²) rounds, for every bag X, every vertex v of X and every a in sep⁺(X) ∩ V(X), the vertex v learns the distances d_X(a, v) and d_X(v, a) in the part of the digraph inside X. This is deterministic relative to the BDD.

**Theorem 2 (offsets).** After Lemma 1, for any offsets φ(u), each a nonnegative integer of polynomial size or ∞ and known to its own vertex, every vertex v learns min_u (φ(u) + d_G(u, v)) in Õ(D) further rounds. So one such query with new lengths takes Õ(D²) rounds in all, however many vertices have finite offsets.

**Corollary 3 (weighted matching).** The Weighted Matching Theorem of `notes/MATCHING.md` holds in Õ(D³) rounds with its digraph SSSP replaced by Theorem 2, so it no longer depends on a proof deferred to a full version.

**Corollary 4 (no hypothesis).** `notes/NEGATIVE.md` of the planar SSSP repository shows that an oracle for Theorem 2 taking T rounds gives exact SSSP with negative weights in Õ(T + D) rounds, and perfect matching, prescribed degrees and maximum flow in Õ(T + D) rounds if the oracle runs on its auxiliary planar network Ĝ. `notes/DMST.md` there does the same for minimum arborescences and maximum branchings. With T = Õ(D²), and with no Label Hypothesis, all of these take Õ(D²) rounds with high probability. For maximum flow and perfect matching this is known or follows from `notes/MATCHING.md`. For minimum arborescences and prescribed degrees we found no earlier bound of this form on planar networks, which is not proof that none exists. For primal negative weights, the bound is stated in [3, Sec. 1.1] with no proof that we could find.

## 2. Proof of Lemma 1

Write B(X) = sep⁺(X) ∩ V(X). Then |B(X)| = Õ(D) by (B1), since the tree has height O(log n). If Y is a child of X, then B(X) ∩ V(Y) ⊆ B(Y), since sep⁺(X) ⊆ sep⁺(Y).

Induct from the leaves. A leaf has Õ(D) vertices by (B4), and so Õ(D) arcs by planarity. It broadcasts them over a BFS tree of the leaf in Õ(D) rounds, and each vertex computes the distances.

Let X be an inner bag with children Y₁, ..., Y_k, and assume the claim for the children. Let Q be the digraph on B(X) with an arc from a to b of length min_j d_{Y_j}(a, b), over the children that hold both. Each a in B(X) knows these values for its children, and it lies on at most three of them if it is on sep(X) and on one otherwise, by (B3). It broadcasts them over a BFS tree of X. That is Õ(D²) words in all, so Õ(D²) rounds, for all bags of a depth in parallel by (B2). Each vertex of X now knows Q and computes its all-pairs distances d_Q.

*d_Q = d_X on B(X).* An arc of Q is a walk in a child, and a child is a subgraph of X, so d_X ≤ d_Q. Conversely, cut a shortest path of X from a to b at its vertices in B(X). Each piece has no inner vertex on sep(X), since sep(X) ⊆ B(X). So by Fact 1 of `notes/MATCHING.md` it lies in one child, and its length is at least that of the arc of Q.

*The vertices.* For v in V(X) and a in B(X):

    d_X(a, v) = min over children Y holding v, and b in B(X) ∩ V(Y), of d_Q(a, b) + d_Y(b, v),

with d_X(a, v) = d_Q(a, v) if v is in B(X), and symmetrically for d_X(v, a). The value on the right is the length of a walk in X. For the other direction, take a shortest path from a to v and let b be its last vertex in B(X). If b = v we are done. Otherwise the rest has no inner vertex on sep(X), and v is not on it either, so by Fact 1 this rest lies in the one child that holds v. So the formula attains d_X(a, v). The vertex v knows d_Y(b, v) by induction and d_Q from the broadcast, so this needs no further messages.

There are O(log n) depths. ∎

## 3. Proof of Theorem 2

Use the Virtual Source Lemma of the planar SSSP repository, Section 3 of its paper, with ε = 0 and with the hierarchy of the BDD: hubs H_X = sep(X), and A_X the arcs in X. Its condition (V1) holds since the root is G, (V2) is (B3), and (V3) follows from (B2). Lemma 1 provides the values it asks for, since d_G ≤ d_X, so ε = 0 is allowed. Then

    A_X(h) = min over u with X on the chain of u, of φ(u) + d_X(u, h),
    d(v) = min over X on the chain of v, and h in sep(X), of A_X(h) + d_X(h, v).

For each bag there are Õ(D) values A_X(h). One pipelined convergecast and one broadcast over a BFS tree of X take Õ(D) rounds, for all bags of a depth in parallel, and there are O(log n) depths. ∎

For a self-contained reading: the lower bound of the lemma is the triangle inequality. For the upper bound, take a best u and a shortest path P to v, and descend from the root while P avoids the separator. By Fact 1 of `notes/MATCHING.md`, P stays in one child, which is on the chains of u and of v, and by (B4) it must meet a separator, at a hub h of a bag X that holds all of P.

*Trees.* With positive lengths each vertex takes a tight in-arc. Zero lengths go away by ℓ′ = (n + 1)ℓ + 1 and φ′ = (n + 1)φ, with d = ⌊d′/(n + 1)⌋.

## 4. Proof of Corollary 3

The Weighted Matching Theorem needs per insertion one SSSP from h on the bag X, as its own network, over the inner BDD of its Section 4, with all lengths known to their tails. Theorem 2 with φ(h) = 0 gives this in Õ(D²) rounds. There are Õ(D) insertions per depth and O(log n) depths. ∎

## 5. Why the bound stays at D²

Q has Θ(|B|²) values in general, and the broadcast is what costs D². The Label Hypothesis of the planar SSSP repository replaces exact labels by labels that are computed in Õ(D) rounds, at the price of a hypothesis, and it gives Õ(D) for the query.

## 6. Checks

`sim/labels.py` runs the rule of Lemma 1 bottom up on the decompositions of `sim/mm.py`, on all planar families of `sim/gm.py`, with lengths that include zeros and absent arcs. It compares each label with Dijkstra in the bag, and each query with Dijkstra in G from a virtual source, for offsets on one vertex, a few, a random set and all vertices.

| Lane | Runs | Label checks | Query checks | Largest n | Largest B(X) | Failures |
|---|---:|---:|---:|---:|---:|---:|
| `labels.py 4001 300` | 21,199 | 253,306,012 | 2,658,054 | 206 | 75 | 0 |
| `labels.py 4002 300 big` | 5,322 | 305,486,566 | 1,239,402 | 348 | 122 | 0 |

The word count of the code is no test of the bound. Its option `closure` puts a separator into every child, against (B3), which gives up to 243,399 words in one bag.

Negative controls, `labels.py ctl`. Each must give wrong values on some run.

| Control | What it changes | Runs | Runs with a wrong label | Runs with a wrong query |
|---|---|---:|---:|---:|
| none | the rule above | 2,795 | 0 | 0 |
| `seponly` | sep(X) in place of sep⁺(X) | 3,120 | 1,995 | 1,782 |
| `noq` | arcs of Q with no all-pairs step | 2,881 | 1,845 | 649 |
| `noqrev` | the same term for the two ends of the backward formula | 2,812 | 2,293 | 2,104 |
| `deepest` | the query looks only at the last bag of the chain | 3,692 | not checked | 2,987 |
| `rootonly` | the query looks only at the root | 3,685 | not checked | 2,810 |
| `swap` | the query uses d_X(v, h) in place of d_X(h, v) | 3,648 | not checked | 3,374 |

**Not covered.** Rounds and messages: the code counts words, not rounds. It does not use real bags of [1]; its separators are two paths of a BFS tree, with no embedding. The proofs of the corollaries are reductions, and the code does not run them on this oracle, since it matches the oracle's output exactly. Lean: `lean/PlanarMatching/Labels.lean` proves, on the abstract decomposition of `Decomp.lean`, Fact 1 for walks whose inner vertices avoid the separator (`walk_stays`) and the distance formula of Lemma 1 with distances as least walk lengths and the hub digraph Q, under the hypothesis that the children cover the bag (`exact_labels`, `distQ_eq`). The rounds are not covered.

## References

1. J. Li, M. Parter. Planar Diameter via Metric Compression. STOC 2019.
2. M. Parter. Distributed Planar Reachability in Nearly Optimal Time. DISC 2020.
3. Y. Abd-Elhaleem, M. Dory, O. Weimann. Õptimal Distributed Maximum Flow Approximation in Undirected Planar Graphs. DISC 2026, arXiv:2608.09500.
