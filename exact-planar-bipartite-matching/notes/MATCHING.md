# Exact bipartite matching in planar networks

**Status.** Proofs written. Simulation in `sim/REPORT.md`: 863,003 runs, no failure. The combinatorial core is in Lean, see
Section 8. Section 9 states the limits of these checks.
Importance: solid, if it survives.

The model is CONGEST on a connected planar network with n vertices and hop diameter D. Õ hides
factors polylogarithmic in n.

## 1. Results

**Path Lemma.** Let G be a planar digraph whose underlying graph has hop diameter D, and let s, t be
vertices with a directed s-t path. In Õ(D) rounds every vertex learns its arcs on one simple directed
s-t path. Deterministic relative to the decomposition: [2, Lemma 16] is stated as randomized given a BDD, but its Step 1 as written
uses no randomness, and [5, Sec. 6] names the separator as the only randomized component.

**Matching Theorem.** A maximum matching of a bipartite planar network is computed in Õ(D²) rounds.
The algorithm is deterministic relative to the decomposition, and by the derandomization stated in
[5, Sec. 6] the whole bound would be deterministic. If the nodes of [3] detect termination, which we did not
check, running [3] in parallel gives min{Õ(D²), O(s\* log s\*)}, where s\* is the size of a maximum matching.

**Weighted Matching Theorem.** A maximum weight matching of a bipartite planar network with integer
weights in {0,…,n^{O(1)}}, together with an optimal integer dual, is computed in Õ(D³) rounds with the
exact labels of `notes/EXACT_LABELS.md`, which also give the digraph SSSP of [2, Lemma 4], whose proof [2] defers to its
full version, and in Õ(D²) rounds with the Exact SSSP Theorem of [6], which holds given the Label Hypothesis stated there.

**Multi-Source Lemma.** For any set S of sources in a planar digraph, every vertex learns in Õ(D)
rounds whether some source reaches it.

**Corollaries.** Minimum vertex cover and maximum independent set of a bipartite planar network in
Õ(D²) rounds. Minimum weight perfect matching, or a report that none exists, within the bounds of the
Weighted Matching Theorem.

**Context.** The bound Õ(τ⁴D+τ⁷) of [4, Theorem 4] for treewidth τ, with τ = O(D) on planar graphs,
implies Õ(D⁷) for the unweighted problem. The insertion scheme of this note with one exact SSSP of [2, Lemma 4] per insertion implies Õ(D³), also with weights, so the Matching Theorem gains a factor D on that. Neither is stated in a source that we found. Exact minimum cost flow takes n^{1/2+o(1)}D rounds on planar
graphs [7], for one s-t flow on the communication graph. Matching needs a super-source and a super-sink, and
these can break planarity: on the cube every face holds 2 of the 4 vertices of one side, so even one apex on
that side is non-planar. So the planar bound of [7] does not give matching by its statement. If its Laplacian
solver extends to G with the two apexes, then the Matching Theorem improves on it for D below about n^{1/2},
and the Õ(D³) weighted bound for D below about n^{1/4}. Two even paths whose left parts differ by one flip the
status of a middle edge, which gives Ω(D). To our knowledge no source states a bound for the weighted problem that is polynomial
in D alone.

## 2. What is used from the decomposition

All from [2], read from its text. A *BDD* is a tree of bags of height O(log n), whose root is G and in which every child is a subgraph of its parent.
The proofs below use this when they pass from ⇝ in a child to ⇝ in the parent.

- (B1) Every bag has hop diameter O(D log n), and |sep(Y)| = O(D log n).
- (B2) Every edge of a bag lies in a child of the bag, and in at most two bags per level.
- (B3) A vertex of sep(Y) lies on at most three children of Y. Any other vertex of Y lies on exactly one.
- (B4) A leaf has O(D log n) vertices and sep(Y) = V(Y).
- (B5) Let sep⁺(Y) be sep(Y) together with the separators of all ancestors of Y. By [2, Lemma 16], every
  vertex of Y knows the preserver H(Y), that is, all pairs (a,b) in sep⁺(Y) with a ⇝_Y b. By the text
  before [2, Claim 15], every vertex of Y also knows, for every child Y_j, all pairs (a,b) in sep⁺(Y)
  with a ⇝_{Y_j} b. All this takes Õ(D) rounds.
- (B6) Labels [2, Step 2]. For u with chain G_0,…,G_ℓ, where G_ℓ is the first bag with u in sep(G_ℓ), the
  label L(u) holds In(u,G_i) and Out(u,G_i), the members of sep⁺(G_i) that reach u and that u reaches in
  G_i, and the child on the chain. It has Õ(D) bits. In a leaf, u knows the vertices and arcs of the leaf; the leaf has Õ(D)
  arcs, so collecting them after every flip costs Õ(D). We read In and Out as
  reflexive: u is in In(u,G) and Out(u,G) when u is in sep⁺(G).

Bags of one level run in parallel by (B2), at a cost of a factor 2. A BFS tree T_Y of each bag costs Õ(D)
once.

**Fact 1 (cutting).** Let P be a path in Y. Cut P at its vertices in sep(Y) and at its two ends. Every
piece lies in one child of Y. Indeed, interior vertices of a piece lie off sep(Y), so each is on a unique
child by (B3), and by (B2) consecutive ones share it. A piece that is one edge lies in a child by (B2).

**Fact 2 (query).** Suppose u, v lie on a common bag G_0 of both chains, and u ⇝_{G_0} v. Then some bag G
on both chains, below or equal to G_0, has Out(u,G) ∩ In(v,G) ≠ ∅, and any such intersection gives
u ⇝_G v. To see this, descend from G_0 as long as the path avoids the separator. By Fact 1 it stays in one
child, which is on both chains. It meets a separator by (B4), and that vertex is in the intersection.

## 3. The Path Lemma

### Requests

A *request* in a bag Y is a pair (u,v) in V(Y) with u ⇝_Y v. Its *interval* is

    Int(u,v;Y) = { x in V(Y) : u ⇝_Y x and x ⇝_Y v }.

The root holds the single request (s,t). For a request (u,v) in Y let J be the digraph with node set
(sep⁺(Y) ∩ V(Y)) ∪ {u,v}, and with an arc (a,b) labelled j whenever a, b are on the child Y_j and
a ⇝_{Y_j} b. By Fact 1 there is a u-v path in J. Take a path of least hops, say

    u = y_0, y_1, …, y_k = v,

and turn each arc (y_{i-1},y_i) with label j into a request, called a *segment*, in Y_j. A fixed rule
breaks ties: least identifiers, first the node order, then the child. Every bag broadcasts the identifiers of
its children, in Õ(D) rounds, since Y is connected, so with several children each holds a vertex of sep(Y), and there are at most max(1, 3|sep(Y)|). A
leaf answers a request by a BFS path in the leaf, under the same kind of rule.

**Interior nodes are hubs.** Every y_i with 0 < i < k is in sep⁺(Y). So, by induction, a start of a
request that is not in sep⁺ of the parent is s, and an end that is not is t. In fact y_i is in sep(Y): two
consecutive arcs with one label would have a shortcut, so y_i lies on two children.

**No communication.** Broadcast L(s) and L(t) over the BFS tree of the root, Õ(D) rounds. Then every
vertex w computes the requests of every bag on w, top down, with no further messages. If w is on Y then w
is on the parent of Y, so by induction w knows the requests of the parent. Arcs of J between hubs are known
by (B5). An arc at s with s off sep⁺(Y) comes from Out(s,Y_j) ∩ sep⁺(Y), since sep⁺(Y) ⊆ sep⁺(Y_j), and an
arc at t likewise from In(t,Y_j). An arc (s,t) comes from Fact 2.

### Disjointness

**Lemma A.** Distinct requests in one bag have disjoint intervals.

*Proof.* True at the root. Let two segments lie in the child C of Y.

If they come from different requests R, R' of Y, then Int(segment;C) ⊆ Int(R;Y): a vertex x with
y_{i-1} ⇝_C x ⇝_C y_i satisfies u ⇝_Y y_{i-1} ⇝_Y x ⇝_Y y_i ⇝_Y v, because arcs of J are realized in
children of Y. So they are disjoint by induction.

If they come from one request, as segments a < b, and share x, then y_{a-1} ⇝_C x ⇝_C y_b. Hence
(y_{a-1},y_b) is an arc of J, which replaces b-a+1 ≥ 2 hops by one, against least hops. ∎

Only one property of the path is used: it has no shortcut in J.

**Lemma B.** A vertex of sep(Y) lies on W(R), defined below, for at most one request R of Y, and has at most
two visits in it.

The intervals of distinct requests are disjoint by Lemma A, and W(R) lies in the interval of R. Within R, let x
lie on segments a < b, and suppose b ≥ a+2. Either the two are in one child, against Lemma A, or x is in sep(Y) by
(B3), and then y_{a-1}, x, y_b is a J path that replaces b-a+1 ≥ 3 hops by two, against least hops. So x lies on
at most two segments, which are consecutive. Each segment path is simple, so this gives at most two visits.

### Realization, bottom up

Every request R = (u,v) of Y gets a simple directed u-v path π(R) inside Int(R;Y). In a leaf this is the
BFS path. Otherwise let W(R) be the concatenation of π over the segments of R, and let π(R) be its
chronological loop erasure: at the first vertex that repeats, jump to its last visit, and continue.

**Lemma C.** A vertex that repeats in W(R) lies in sep(Y).

*Proof.* Each π(segment) is simple. Two segments in one child are disjoint by Lemma A, as π(segment) lies
in its interval. Segments in different children meet only on vertices lying on two children, which are in
sep(Y) by (B3). ∎

Since π(R) ⊆ W(R) ⊆ Int(R;Y), the paths π of distinct requests in Y are disjoint.

Consecutive segments can meet at a hub other than their common end. It happens when a directed cycle runs
through two children and J has a tie. This is why erasure is needed.

### Doing the erasure

Fix a request R of a bag. Give an arc of a leaf path that belongs to W(R) its *key*: the sequence of segment indices along the chain of
bags from this bag down to the leaf, followed by the index on the leaf path. Keys are compared only within one request: two requests
of one bag have keys that look alike. Keys in lexicographic order follow the walk. A key has O(log² n) bits and every endpoint of the arc knows it with no communication, since it
computed the requests. The key of a visit is the key of the arc leaving it. The end v of a request needs no key
since it never repeats: if v lay on a segment a < k, then (y_{a-1},v) would be a shortcut in J. The same holds for u.

Process levels bottom up. In each bag Y, every x in sep(Y) sends the keys of its retained visits over T_Y,
and all vertices of Y compute the same erasure. By Lemma B this is at most 2|sep(Y)| keys, that is Õ(D) words
and Õ(D) rounds. An erased stretch of R is a half-open interval of keys of R, from the first visit up to the last visit, which
is kept. Each endpoint of an arc compares the key with the intervals of its own request. By Lemma C no vertex off sep(Y) needs to report anything.

At the root, the retained arcs form π(s,t), and each vertex knows its own arcs. The total is Õ(D) rounds per
level over O(log n) levels. This proves the Path Lemma. ∎

## 4. The Matching Theorem

### Outer recursion

Let the bipartition be found by BFS in O(D) rounds. Compute a BDD of G; call its bags *outer*. For an outer
bag X let X° = V(X) minus the separators of proper ancestors.

- X° sets of one depth are disjoint. If v were in both, it would lie on two children of the lowest common
  ancestor, hence on its separator.
- G[X°] ⊆ X. Each edge between non-separator vertices stays in their unique child.
- X° minus sep(X) is the disjoint union of the C° over the children C of X, with no edge between different
  C°, by the same argument.

The scheme is the sequential one of [9], as secondary sources describe it. Process depths bottom up. A leaf solves G[X°] locally, together with an optimal dual in the weighted case. In an inner bag, the matchings of the children
together are maximum on G[X° ∖ sep(X)]. Then insert the vertices of sep(X) ∩ X° one at a time, the i-th in
every bag of the depth during step i.

### One insertion

Let M be maximum on G[C] with C ⊆ X°, and h a new vertex. The maximum size grows by at most 1, and if it grows
there is an M-augmenting path starting at h (compare [4, Proposition 1], from [8]). Indeed, an augmenting path that
avoids h would lie in G[C], against maximality. So every augmenting path ends at the free vertex h, and M⊕M′, for a
maximum M′ on G[C ∪ {h}], holds at most one. Take the residual digraph on C ∪ {h}, with arcs leaving the side of h
along unmatched edges and returning along matched edges.

**Network.** Treat X as its own network, of hop diameter Õ(D) by (B1). All black boxes run with the global n: pad
X with n−|X| virtual pendant vertices at one vertex, simulated by it, which adds at most 2 to the diameter and
keeps planarity. To let edges carry messages without
being arcs, subdivide every edge of X once. An edge in the residual digraph a→b becomes a→w→b, and any other
edge a−b becomes a→w←b, where w is simulated by an endpoint. The result is a planar digraph with the same
underlying graph after every flip, whose hop diameter is at most 2·diam+2, and w with two in-arcs is a sink, so
paths never use it. Compute one BDD of this network, an *inner* BDD, once.

**Step.** Run [2, Lemma 16] on the current digraph. Broadcast L(h). Each free vertex t of the other side tests
h ⇝ t by Fact 2. Elect one t by the tree. If there is none, M stays. Otherwise broadcast L(t), run the Path Lemma,
and flip M along the resulting path. A simple path is what makes this flip correct.

**Rounds.** Õ(D) per step by (B1) and (B5), with Õ(D) steps per depth by (B1), and O(log n) depths, in Õ(D²)
total. This proves the first claim of the theorem. ∎

The inner BDD is separate on purpose. Its separators are unrelated to those of the outer recursion, and a hub of
the outer bag can be an interior vertex of an augmenting path.

## 5. The Weighted Matching Theorem

Keep integers y on the current set C with the following, where edges, sides and free vertices are those of G[C]
(and of G[C ∪ {h}] during the insertion of h):

- (D1) y ≥ 0 and y(a)+y(b) ≥ w(ab) for every edge,
- (D2) y(a)+y(b) = w(ab) on M,
- (D3) y(v) = 0 on free v.

Then M is optimal: any matching N has w(N) ≤ Σ_{uv∈N} (y(u)+y(v)) ≤ Σ y(v) = w(M).

**Insertion of h.** Say h is in A; the case of B is symmetric. Set y(h) := max(0, max_{b∼h} (w(hb)−y(b))), which
restores (D1). Use the arcs a→b on unmatched edges with length y(a)+y(b)−w(ab) ≥ 0, and b→a on matched edges with
length 0. Let d be the distance from h, and set

    δ = min( min_{free b} d(b), min_{a∈A} (d(a)+y(a)) ).

The term a = h gives δ ≤ y(h). Let z attain the minimum. Update

    y'(a) = y(a) − max(0, δ−d(a)),    y'(b) = y(b) + max(0, δ−d(b)).

- y'(a) ≥ 0, since δ ≤ d(a)+y(a). For a free b, y'(b) = 0, since δ ≤ d(b).
- Unmatched edge: if d(a) ≥ δ nothing decreases. Otherwise d(b) ≤ d(a)+ℓ gives
  y'(a)+y'(b) ≥ y(a)+y(b)−ℓ = w(ab).
- Matched edge: a ≠ h has only the in-arc from its partner, so d(a) = d(b), and the sum is unchanged.
- An arc on a shortest path with d(b) ≤ δ becomes tight. Every vertex on a shortest path to z has d ≤ d(z) ≤ δ.

Flip along a simple shortest path from h to z.

- z = h: then δ = y(h), so y'(h) = 0, and h stays free.
- z = b free: y'(z) = 0 and z becomes matched, which is allowed in any case.
- z = a ≠ h: y'(a) = 0, and a becomes free, as (D3) requires.

All of (D1) to (D3) hold on C ∪ {h}. Integers stay integers.

**Distributed.** (D1) to (D3) give y ≤ max w, also for y(h), so all lengths are at most 2·max w.
Give every edge of X, in each direction that is not a residual arc, the length L = 1 + n·(largest length), so X is
strongly connected and d ≥ L means unreachable; such a d counts as infinity in δ. Run SSSP on X, over the inner BDD. `notes/EXACT_LABELS.md` and [6] allow zero lengths. [2] does not address them, and with it they go away by
ℓ′ = (n+1)ℓ+1 and d = ⌊d′/(n+1)⌋. Elect δ and z by aggregation on the tree of X. The
update is local. Each edge sees whether it is tight under y′, so the tight arcs form a planar digraph in which any h-z path has
length d(z). Run the Path Lemma on it, over the same subdivided network as in Section 4. Since the path comes from the
Path Lemma, no parent pointers are used. Per insertion this is SSSP plus Õ(D), with Õ(D) insertions per depth. ∎

**Perfect matching.** Replace w by Kn − w with K above every weight. A maximum weight matching then has maximum
cardinality, and among those, minimum original weight.

## 6. The Multi-Source Lemma and the corollaries

For every bag Y let R(Y) be the union of Out(a,Y) ∩ sep(Y) over the sources a on Y° = V(Y) minus the separators of proper
ancestors. A vertex a in Y° has Y on its chain, so it knows this set from its label. Since R(Y) ⊆ sep(Y), an OR over T_Y
gives it to all of Y in Õ(D) rounds per level. A vertex v answers yes if v is a source, or if In(v,Y) ∩ R(Y) ≠ ∅ for some
Y on its chain.

*Correctness.* A yes is sound, with In and Out reflexive. Conversely let P be a path from a source a to v. Descend from the root as long as P avoids
the separator. By Fact 1 it stays in one child, so it meets the separator of a bag Y whose proper ancestors it avoided.
Hence a and v are in Y°, and the vertex met is in Out(a,Y) ∩ In(v,Y). ∎

**König.** Given M, let Z be the set reached from free vertices of A in the residual digraph. As usual, (A∖Z) ∪ (B∩Z) is a
vertex cover of size |M|, and its complement is a maximum independent set. The Multi-Source Lemma, run on the network of
Section 4, gives Z in Õ(D) rounds.

## 7. Open

- Õ(D²) for all polynomial weights. `notes/SMALL_WEIGHTS.md` proves it for W = Õ(D) and for weights on the vertices, and records where the method gets stuck otherwise.
- Õ(D) for matching. Batching hubs that lie on a face, by [2, Lemma 2], is the natural attempt. Augmentations interact.
- `notes/GENERAL_DFS.md` claims Õ(D) for planar DFS on digraphs, and `notes/DIRECTED.md` reproves the Path Lemma with no loop erasure.

## 8. In Lean

`lean/PlanarMatching` has no `sorry`; the axioms are listed in `lean/axioms.txt`. Proved from abstract hypotheses:

- `LoopErase`: the erasure of a walk is simple, keeps both ends and its arcs, and reports from the set of repeated vertices
  suffice.
- `Requests`: least hops gives no shortcut, Lemma A, Lemma C.
- `Decomp`: from (B2), (B3), (B4) and the inclusion of a child in its parent, Fact 1, Fact 2 and the core of the Multi-Source Lemma (`descent`, `multiSource`), the
  J path (`jpath`), and the claims on X° (`chain_comparable`, `arc_in_chain`, `no_cross`).
- `Hungarian`: weak duality, the dual update, the flip along a simple alternating path, and their combination `insertion`.

Not in Lean: planarity, the facts taken from [2], anything about rounds or knowledge, the growth by at most 1 in one insertion, that
distances satisfy the stated inequalities, and the correspondence from a simple path in the residual digraph to the list `L` of `flip`.

## 9. Remarks and limits

*What the proofs need from the bags and the keys.* The proofs use that a child lies in its parent and that the root is G. Without this, a 9-vertex instance gives a non-simple path. Keys read with no request attached erase an arc of another request of the same bag, on 8 vertices.

*How far least hops can be weakened.*

| Condition on the J path | Result |
|---|---|
| any simple path | Lemma A fails at n = 3 |
| no ≥ 2 hops replaced by one arc, no ≥ 3 hops by two | all statements hold in numerical tests, at most 2 visits |
| no shortcut only | Lemma A and Lemma C hold, three visits occur |

*Rules that are needed.* Dropping any of these gives wrong results in numerical tests: the erasure, least hops, y(h) by its formula in place of y(h) = 0, the free term in δ, the max in the update, and all bags of the chain in the Multi-Source Lemma. A larger y(h) does no harm, since δ ≤ y(h) still holds.

*Limits.* There is no CONGEST simulation. Real decompositions of [1] are not implemented, only substitutes built from two paths of a BFS tree or from fundamental cycles, and residual digraphs on them rarely make the erasure fire (312 repeats in 55,503 runs of `sim/REPORT.md`), which is the weakest coverage. The black boxes are read, not proved. These are taken as stated and not checked: the text of [3]; proofs of [2, Lemmas 10 to 13], which are not in the DISC text; [2, Lemmas 4 and 9]; the BDD construction beyond [1]'s Def. 4.1, Lemma 4.3 and Section 4.2; [6]'s theorem and its hypothesis; the separator of [5].

## References

1. J. Li, M. Parter. Planar Diameter via Metric Compression. STOC 2019.
2. M. Parter. Distributed Planar Reachability in Nearly Optimal Time. DISC 2020.
3. M. Ahmadi, F. Kuhn, R. Oshman. Distributed Approximate Maximum Matching in the CONGEST Model. DISC 2018.
4. T. Izumi, N. Kitamura, T. Naruse, G. Schwartzman. Fully Polynomial-Time Distributed Computation in Low-Treewidth Graphs. arXiv:2205.14897.
5. Y. Abd-Elhaleem, M. Dory, O. Weimann. A Simple Distributed Deterministic Planar Separator. arXiv:2602.22916.
6. S. Senge. Exact shortest paths and flows on planar graphs. https://github.com/ssenge/ExactShortestPathsAndFlowsOnPlanarGraphs
7. T. de Vos. Minimum Cost Flow in the CONGEST Model. SIROCCO 2023. arXiv:2304.01600.
8. Y. Iwata, T. Ogasawara, N. Ohsaka. On the Power of Tree-Depth for Fully Polynomial FPT Algorithms. STACS 2018. Credited in [4, Proposition 1].
9. R. J. Lipton, R. E. Tarjan. Applications of a planar separator theorem. SIAM J. Comput. 9(3), 1980.
