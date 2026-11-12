# Exact Shortest Paths and Flows on Planar Graphs

> This folder continues the repository [ExactShortestPathsAndFlowsOnPlanarGraphs](https://github.com/ssenge/ExactShortestPathsAndFlowsOnPlanarGraphs), which is no longer updated; new results are added here. Its history and the tag `arxiv-v1` that the paper refers to stay there.

This repository contains proofs, machine-checked lemmas and numerical checks for exact
single-source shortest paths (SSSP) and exact maximum flow in planar networks in the CONGEST
model. The main claims are:
- exact directed SSSP in $\tilde O(D)$ rounds (Theorem A), down from $\tilde O(D^2)$;
- exact maximum st-flow in directed planar networks in $\min\lbrace\tilde O(D^2),\ D\cdot n^{o(1)}\rbrace$
  rounds (Theorem C), down from $\tilde O(D^2)$;
- exact minimum st-cut and maximum st-flow value in undirected planar networks in
  $\tilde O(D)$ rounds (Theorem D, new), where only a $(1-o(1))$-approximation was known in
  $\tilde O(D)$. It needs two repairs of [18]: of its auxiliary graph at $s$ and $t$ (Lemma R)
  and of its recursion, which as written can miss the minimum cut (Lemma S, with the side lemma
  it needs, Lemma O).

The paper is *Exact Shortest Paths and Maximum Flow in Planar Networks in the CONGEST Model*,
[arXiv:2611.02256](https://arxiv.org/abs/2611.02256) (v1, 1 November 2026); the same PDF is in
`paper/2611.02256v1.pdf`. It covers the claims above, under a Label Hypothesis that it states.
That hypothesis is now proved in Lean from cited results; see [Status](#status).
The claims below came after the paper and are not in it.

A newer claim, after the paper and not part of it: exact maximum st-flow in directed planar networks, with the integer flow on every edge, in
$\tilde O(D)$ rounds, by scaling over the faces next to one BFS path. It needs one extension of the labels, a prescribed root cycle. See
[`notes/MAXFLOW.md`](notes/MAXFLOW.md). **Written on 2 Nov 2026. On parallel arcs of one direction the flow value can exceed $nU$, with $U$ the largest capacity, and a number of scaling steps chosen from $nU$ gives an infeasible flow, so the note chooses it from $mU$, with $m$ the number of arcs. It rests on the construction in `notes/LEMMA15.md`, not only on the Label Hypothesis; treat it as a claim.**

A newer and simpler claim, after the paper and not part of it: exact SSSP with negative weights, and exact maximum st-flow in directed planar networks with the flow on every edge, in
$\tilde O(D)$ rounds with high probability, from the Label Hypothesis alone, with no extension of the labels. Perfect matching of planar bipartite networks follows in the same bound. It replaces the reduction of [6] in Theorems B and C by a published reduction with polylogarithmic overhead (SOSA 2025, arXiv:2410.20959). **The open question in the paper on the factor $n^{o(1)}$ was already answered by that reduction, which the paper missed. The statements of Theorems B and C below are correct, but they are weaker than what follows.** See [`notes/NEGATIVE.md`](notes/NEGATIVE.md). **Written on 3 Nov 2026. One property it takes from arXiv:2303.00811 rests on a corollary there whose proof may have a small gap; the note repairs it in one line. The round bounds for negative weights and for maximum flow are proved in Lean from four cited results, see [Status](#status); the rest is a claim.**

**New claim, 3 Nov 2026:** [`notes/REPLACEMENT.md`](notes/REPLACEMENT.md). Replacement paths on planar digraphs: for every arc of a shortest st-path, the distance without it, exactly in $\tilde O(D\cdot\min(h,D))$ rounds, and $(1+\varepsilon)$-approximately on the excess in $\tilde O(D/\varepsilon)$ rounds, from the Label Hypothesis. On general networks the exact problem takes $\tilde\Theta(n)$ rounds. Undirected weighted networks take $\tilde O(D)$. Simulation in `sim/replacement/`.

**New claim, 3 Nov 2026:** [`notes/DMST.md`](notes/DMST.md). Minimum arborescence and maximum branching of a planar digraph in $\tilde O(D)$ rounds, from the Exact SSSP Theorem and the Label Hypothesis, with $O(\log n)$ oracle calls. It follows the plan of the DISC 2019 algorithm for general networks. Simulation in `sim/dmst/`.

A second newer claim, also not part of the paper: in undirected unweighted planar networks every vertex learns its exact eccentricity, so the diameter and radius are found, in
$\tilde O(D^2)$ rounds, where the best stated bound for the diameter is $\tilde O(D^3)$. It does not need the Label Hypothesis. A corollary gives every vertex its sum of distances, so closeness, a medoid and the Wiener index, in the same bound. The (1+ε)-approximate version takes $\tilde O(D + \varepsilon^{-4})$ rounds, see [`notes/APPROX_DIAMETER.md`](notes/APPROX_DIAMETER.md). See [`notes/DIAMETER.md`](notes/DIAMETER.md). **Written on 3 Nov 2026. Treat both as claims.**

The written proof of Theorem A depends on the distance labels of the recent preprint [1]. Our reading hints at a possible gap in one lemma of [1]
(Lemma 14). This repository explains it and gives a repair. A property of
the decomposition that [1] uses for its round count (Property 6) also seems not to hold for
induced bags. We repair that too, with bags that carry the region they were cut from; see [Status](#status).

## Status

Please read this before relying on anything here.
- The proofs are written up in `notes/`. See [Use of AI](#use-of-ai).
- **The Label Hypothesis in Lean.** `labelHypothesis_of_cited` in `lean/SsspFlow/AggFinal.lean` proves the Label
  Hypothesis in the message model from three cited results: realization (G3), distance labels (G5) and face
  identifiers (G6). The nodes get the rotation lists as input. The bags, their cuts along walks up a tree of shortest
  walks, the labels and the message passing are built and proved in Lean. This construction, described in
  [`notes/DISKS.md`](notes/DISKS.md), differs from the tiles of Lemma 14′. The aggregation primitive over many
  subgraphs is proved in Lean too (`aggBox`), with messages of $O(b + \log n)$ bits and $5c(s+k+1)$ rounds for
  congestion $c$, hop diameter $s$ and $k$ keys per subgraph.
  - The smoothing of [3] is proved in Lean as well (`smoothingBox` in `lean/SsspFlow/SmoothRun.lean`). It follows
    Algorithms 3 and 4 of [3] in natural numbers, with $O(\log n)$ calls of the approximate oracle and $O(\log n)$
    more bits per message. So `exactSssp_of_cited` gives the $\tilde O(D)$ round bound of Theorem A from the same
    three cited results, with exact distances and the parents of a shortest-path forest.
  - With a reduction for negative weights, `negFlow_polylog_of_cited` and `negFlow_subpoly_of_cited` give the round
    bounds for negative weights and for maximum flow, with the flow on every edge.
  - `negReduction_of_ldd` in `lean/SsspFlow/NegFinal.lean` proves this reduction, the one of arXiv:2410.20959, with a
    polylogarithmic factor, from the low-diameter decomposition of [6] with the order of its clusters. So
    `negFlow_of_cited` gives $\tilde O(D)$ rounds with high probability for negative weights and for maximum flow, from
    four cited results: realization, distance labels, face identifiers and the decomposition.
  - The cited results stay hypotheses of these theorems.
- **Correctness.** Theorems A, B, C and C′ give correct outputs given Lemma 14′, our
  replacement for [1, Lemma 14], and the black boxes listed below. Lemma 14′ is
  proved in `notes/LEMMA15.md` §3.
- **Round counts: repaired.** [1, Lemma 9 (6)] states that at
  every depth of the decomposition each edge lies in at most two induced subgraphs G[X]. As we
  read it, this does not hold on $K_{2,m}$ plus one edge, for every
  decomposition with the other properties (`notes/LEMMA15.md`, (S9)). [1] runs all bags of
  one depth in parallel because of this property. Correctness does not depend on it.
  - `notes/LEMMA15.md` §9 replaces $G[X]$ by a *region graph* $R_X$: the edges drawn in the
    part of the plane that bag $X$ was cut from. Every edge then lies in at most two region
    graphs per depth, and the tree components that [8] bounds by $O(\log n)$ are proved to
    be $O(\log^2 n)$.
  - This restores the $\tilde O(D/\varepsilon)$ bound of [1] for the labels and the
    $\tilde O(D)$ of Theorem A. The separator is our Lemma B5, a fundamental cycle found
    with prefix sums along a tour of the shallow tree $T_X$ that passes each edge twice, in
    $O(D\log^2 n)$ rounds.
    It is deterministic and adds no black box.
- **Theorem D** (2026-10-29) is new. The auxiliary graph $\hat G_\ell$ of [18], as we read its
  Remark 3.3, fails at $s$ and $t$ on small instances (smallest: 4 vertices, minimum cut 2,
  computed 0). Lemma R proves a local repair, and Lemma N proves the description of the dual
  nodes that it needs. As we read it, the recursion of [18] can miss the minimum cut (11 vertices:
  minimum 15, computed 37). Lemma S repairs this with two more shortest-path calls per level,
  and the side lemma it needs (Lemma O) is proved. The naming of sides and the cut extraction
  are in `notes/RECURSION.md`.
- **Determinism.** With Lemma B5 the decomposition is deterministic, and so is Theorem A,
  given a deterministic planar embedding and deterministic face identifiers (G6). Both are
  claimed elsewhere, not proved here: [17] and [18] use the embedding algorithm of [15] as
  deterministic (the full text of [15] was not accessible to us), and the face identification
  of [9] is randomized as written, with a one-sentence claim that it derandomizes [9, fn. 20],
  while [18, Lemma 3.17] states a deterministic version, given deterministic part-wise
  aggregation such as [20, Thm 1.5]. Theorems C′ and D are
  deterministic in the same sense: their other steps are local, use face identifiers computed
  deterministically in [18, Lemma 3.17], or are the deterministic algorithm of [18]. Theorems
  B and C use [6] and hold with high probability.
- Some steps use published results as black boxes; see [What is assumed](#what-is-assumed).

## Background

**The model.** In CONGEST the input graph is the network itself. Every vertex is a processor
that initially knows its incident edges and their weights. Computation proceeds in synchronous
rounds. In every round each vertex can send a message of $O(\log n)$ bits over each incident
edge, and local computation is free. Complexity is the number of rounds, as a function of the
number of vertices $n$ and the hop diameter $D$, which is the diameter of the underlying
undirected, unweighted graph.

Every problem below needs $\Omega(D)$ rounds even on planar networks, since information has to
cross the network. On general graphs, $\tilde\Omega(\sqrt n + D)$ rounds are needed.

**The problems.**
- **SSSP.** Given a source $s$ and integer edge weights of polynomial size, every vertex $v$
  learns $\mathrm{dist}(s,v)$ and its parent in a shortest-path tree. In the directed version
  the two directions of an edge have their own weights.
- **Maximum flow.** Given integer capacities of polynomial size and terminals $s$ and $t$,
  compute the value of a maximum $s$-$t$ flow and the flow on every edge.

**Previous bounds on planar networks.**

| Problem | Upper bound |
|---|---|
| Exact SSSP, directed, $w\ge 0$ | $\tilde O(D^2)$ [8] |
| $(1+\varepsilon)$-approximate SSSP, directed | $\tilde O(D/\varepsilon)$ [1] (preprint) |
| Exact maximum st-flow, directed | $\tilde O(D^2)$ [9] |
| SSSP in the dual graph, negative weights | $\tilde O(D^2)$ [9] |
| Maximum st-flow with $s$, $t$ on a common face | $(1-o(1))$-approximate, undirected, $D\cdot n^{o(1)}$ [9] |
| Maximum st-flow value and minimum st-cut, undirected | $(1-o(1))$-approximate, $\tilde O(D)$, deterministic [18] |

The open question at the end of [9] asks for better primal SSSP, called "the bottleneck to
overcome in order to obtain better distributed planar algorithms", and suggests to "first
improve the $\tilde O(D^2)$ bound of the (easier) directed SSSP problem (even with
non-negative weights)".

## Before and after

| Category | Problem | Before | After | Scope | Status |
|---|---|---|---|---|---|
| Distributed algorithms, CONGEST | Exact single-source shortest paths on directed planar networks, nonnegative weights | Õ(D²) [8] | Õ(D); the Label Hypothesis stated in this folder, modelled on the labels of [1], is proved in Lean from cited results; this folder also completes the proof of [1], with a repair of one lemma | Directed planar networks, polynomial integer weights, rotation lists as input; deterministic relative to the cited results | Lean, assuming three cited results: realization, distance labels, face identifiers; paper arXiv:2611.02256 |
| Distributed algorithms, CONGEST | Exact maximum st-flow on directed planar networks, with the flow on every edge | Õ(D²) [9] | min{Õ(D²), D·n^{o(1)}}; Õ(D) when s and t lie on a common face; Õ(D) with high probability in a later note | Directed planar networks, rotation lists as input | Claim; in Lean the bound of Õ(D) rounds with high probability, assuming the three cited results and a low-diameter decomposition |
| Distributed algorithms, CONGEST | Exact minimum st-cut and minimum cut value on undirected planar networks | (1 − o(1))-approximation in Õ(D) [18]; exact in Õ(D²) [9] | Õ(D), through the Exact SSSP Theorem, with two repairs of [18]: its auxiliary graph at the terminals, and its recursion, which as we read it can miss the minimum cut | Undirected planar networks | Claim; in Lean the recursion argument, and the interval form on the cut map |
| Distributed algorithms, CONGEST | Negative weights, minimum arborescences and replacement paths on planar digraphs | D·n^{o(1)} for negative weights through a general reduction; no bound in D alone known to us for the others | Õ(D) with high probability for negative weights and for arborescences; replacement paths exactly in Õ(D·min(h, D)) and within 1 + ε in Õ(D/ε) | Planar digraphs; the claims use the Label Hypothesis, proved in Lean from cited results | Negative weights in Lean, assuming four cited results; the others claims in notes, cores in Lean |
| Distributed algorithms, CONGEST | Diameter and all eccentricities of unweighted undirected planar networks | Õ(D³) [arXiv:2608.07187](https://arxiv.org/abs/2608.07187) | Õ(D²), with no hypothesis; within 1 + ε in Õ(D + 1/ε⁴) | Unweighted undirected planar networks | Claim |
| Corrections | Lemma 14 and a decomposition property of [1]; the auxiliary graph and the recursion of [18] | As stated | Counterexamples, and repairs: tiles in place of the hub network and region bags for the round count of [1]; a repaired auxiliary graph at the terminals and two more shortest-path computations per level of the recursion of [18] | As we read the texts | Counterexamples checked by scripts; repairs on paper, the recursion repair in Lean |

## Results

| Result | Rounds | Previous | Rating |
|---|---|---|---|
| Theorem A: exact SSSP, directed, $w\ge0$ | $\tilde O(D)$ | $\tilde O(D^2)$ [8] | modest to solid |
| Theorem B: exact SSSP with negative weights, or a negative cycle | $D\cdot n^{o(1)}$ | $(\sqrt n+D+n^{2/5}D^{2/5})\cdot n^{o(1)}$ on general graphs [6] | modest |
| Theorem C: exact maximum st-flow, directed | $\min\lbrace\tilde O(D^2),\ D\cdot n^{o(1)}\rbrace$ | $\tilde O(D^2)$ [9] | significant |
| Theorem C′: the same with $s$, $t$ on a common face | $\tilde O(D)$ | approximate and undirected only [9], [18] | modest |
| Theorem D: exact minimum st-cut (max-flow value), undirected; new | $\tilde O(D)$ | exact $\tilde O(D^2)$ [9]; $(1-o(1))$-approximate $\tilde O(D)$ [18] | modest to solid |
| Lemma V: distances from a virtual source, and a fix of the query of [1] | $\tilde O(D/\varepsilon)$ | | minor |
| Lemma D: the face-disjoint graph of [9], weighted, realizes dual distances | | | minor |
| A possible gap in [1, Lemma 14] | | | modest |
| A possible gap in Property 6 of [1, Lemma 9], for induced bags | | | modest |
| Region bags: Property 6 for region graphs, $O(\log^2 n)$ tree components, a deterministic separator | | | modest |
| Lemmas 14′, 15′, 16′: the repair of [1, Lemmas 14 to 16] | | | minor |

All five theorems are conditional (see [Status](#status)): their correctness on Lemma 14′,
and their round bounds also on the region bags of `notes/LEMMA15.md` §9. The proofs in Lean of the round bounds of
Theorems A, B and C need neither of these, only the cited results that they name. The ratings in short:
- **Theorem A** closes the planar exact-SSSP gap up to polylogarithmic factors and answers
  the open question of [9]. [18] (2026) still uses approximate SSSP "for the lack of
  almost-D-rounds exact distributed SSSP". The proof is short, though: the reduction of [3], the labels of
  [1], and Lemma V. Since [3, §3.1] already says its boosting works in any model that can run
  its oracle, the theorem is close to folklore once the labels of [1] are available.
- **Theorem B** is a white-box substitution into [6].
- **Theorem C** brings the main theorem of [9] from $\tilde O(D^2)$ to $D\cdot n^{o(1)}$, close
  to the $\Omega(D)$ lower bound. The new term wins once $D$ exceeds $(\log n)^{O(\sqrt{\log n})}$.
  The proof is entirely a composition of known pieces.
- **Theorem C′** is the proof of [9, Thm 1.3] with an exact oracle plugged in.
- **Theorem D** is optimal up to polylogarithmic factors for exact minimum st-cuts in
  undirected planar networks, which [18] leaves open for lack of exact SSSP. The proof puts
  Theorem A into [18], with the weighting of Lemma D.
- **The finding about [1, Lemma 14]** is a correctness gap in the main CONGEST result of an
  unrefereed preprint. The repair changes no bound.
- **The finding about Property 6** removes the round bound of the main theorem of [1] as
  written. It also shows that [8, Def. 4.1] together with [8, Lemma 4.3 (8′)] cannot hold on
  a simple family of graphs; [8] describes the intended property for the edges a bag owns,
  which is not refuted.
- **The region bags** restore that bound. The tools are standard (sides of edges, a crosscut
  argument, a non-crossing count), and the component bound is one log factor weaker than
  [8] claims.

### Theorem A (exact SSSP)

**Theorem A.** Let $G$ be a planar digraph with nonnegative integer weights in
$\lbrace 0,\dots,n^{O(1)}\rbrace$, hop diameter $D$ and source $s$. A CONGEST algorithm computes
exact distances from $s$ and a shortest-path tree in $\tilde O(D)$ rounds. The algorithm is
deterministic, given a deterministic planar embedding and deterministic face identifiers
(`notes/LEMMA15.md` §9.6; see [Status](#status)). Local computation is not polynomial: with
the realization theorem [10], which gives existence only, a bag centre finds a realization by
exhaustive search. A polynomial bound needs a realization that respects a prescribed cyclic
order of the terminals; [1, Thm 1] constructs one in polynomial time but promises no order.

The proof has three ingredients.
1. **Reduction.** By [3, Lemma 3.1, Thm 1.7, App. C.1], exact SSSP needs $O(\log^2 n)$ calls to
   an oracle for $(1+\varepsilon_0)$-approximate distances, $\varepsilon_0=\Theta(1/\log n)$.
   The calls run on the same network with new weights, some of them from a virtual source that
   is joined to every vertex with an offset. The reduction is deterministic and costs $O(1)$
   extra rounds per call. Its discretization is only sketched in [3]. Done as written, an update
   can drive a length to $-\eta$, so the base of every update has to be $\ell_i+\eta$ instead of
   $\ell_i$. `lean/SsspFlow/Boost.lean` proves the corrected version.
2. **Labels.** A BDD of height $O(\log n)$ is computed, as in [1] and [8]. For every bag $X$,
   every $v\in X$ learns $(1+\varepsilon)$-approximate distances in $G[X]$ to and from each
   hub of $X$, in $\tilde O(D/\varepsilon)$ rounds [1, Thm 9]. The estimates never
   underestimate. This is where Lemma 14′ enters.
3. **Lemma V** answers the virtual-source queries from the labels.

Two constants handle unreachable vertices and deleted edges, and the tree comes from running
the algorithm on $w'(e)=n^2w(e)+1$. Details are in `notes/NOTES.md` §3.

### Lemma V (virtual source)

**Lemma V.** Given the labels, $(1+\varepsilon)$-approximate distances from a virtual source with
offsets $\varphi$ take $\tilde O(D/\varepsilon)$ rounds.

Every bag $X$ computes $A_X(h)=\min_{u\in X}\varphi(u)+\tilde d_X(u,h)$ for each hub $h$ by a
convergecast. Leaf bags solve their part exactly. Then each $v$ takes the minimum of
$A_X(h)+\tilde d_X(h,v)$ over all bags $X\ni v$ and all their hubs, and of its leaf values.

The minimum has to run over **all** bags that contain $v$. The query in the proof of
[1, Thm 4] uses only the lowest bag that separates the two endpoints. As we read it, that can give a wrong value when
the labels store distances in $G[X]$, because a shortest path can leave that bag. A small
counterexample:
- the root separator is $\lbrace a,b\rbrace$, with children $X=\lbrace s,a,b,c,u\rbrace$ and $\lbrace w,a,b\rbrace$;
- $X$ has separator $\lbrace c\rbrace$, with children $\lbrace s,a,c\rbrace$ and $\lbrace u,b,c\rbrace$;
- the arcs are $s\to a$ (1), $a\to w$ (1), $w\to b$ (1), $b\to u$ (1), $a\to c$ (100), $c\to u$ (1) and $s\to c$ (100).

Here $d(s,u)=4$ via $w$, which lies outside $X$, but the query at $X$ returns 101. On random
instances `sim/check.py` finds the single-bag query wrong on about 6% of pairs.

### The gap in [1] and the repair

**Where the gap is.** The labels of [1] come from distance oracles for the bags, built bottom up. At
each bag the hub distances are written as a quasimetric, fitted by a linear program to a cyclic
order of the hubs, and realized by a small planar graph. [1, Lemma 14] provides the cyclic order.
It claims that cutting the bag open along a network of hub paths merges all of its holes into
one face. As we read it, this does not hold in three configurations that are consistent with all properties of the
decomposition:
1. **Separator chords.** An edge between two separator vertices, drawn inside the separator,
   splits a hole of a child bag in two. In 58 of 100 random weightings no cyclic order makes
   the linear program feasible, and the worst instance is off by a factor of 1.64.
2. **Virtual closing edges.** When separators close through edges drawn in a face of $G$, the
   cut can disconnect the bag. On a $13\times 8$ grid one vertex then cannot reach another at
   all, although their distance in $G[X]$ is 20.
3. **Holes that touch at one vertex.** The construction adds no path between them, so the two
   holes stay two faces. 53 of 60 weightings have no valid order, and the worst is off by 1.73.

A control run on 300 instances with all hubs on one face gave factor 1 every time, so these
are not artefacts of the linear program. The scripts are in `sim/counterexamples/` (`g2_chord_bfs.py`,
`g2_chord.py`, `g2_virtual.py`, `g2_pinch.py`, and the control `lp_sanity.py`).

**The repair** (`notes/LEMMA15.md`) has two layers.
- **Topological layer: tiles (§3).** A growing set $\Gamma_d$ of corners of $G$ is kept
  connected, as a subgraph of the radial graph. Its faces are the *tiles*, and since
  $\Gamma_d$ is connected, every tile is a disk. Edges are labelled by the bag they belong to.
  Each bag adds new corners where labels change around its separator, along its separator
  path, and if needed along a path to $\Gamma_d$. Nothing is cut. **Lemma 14′** states what
  the analytic layer needs:
  - one label per tile;
  - $O(D\log n)$ new corners per bag and $O(D\log^2 n)$ ports per bag;
  - every tile's piece is drawn in a disk with its ports in boundary order;
  - child tiles glue exactly into their parent tile, and into $G[X]$;
  - every step runs in $\tilde O(D)$ rounds.

  None of the three configurations above can occur with tiles (§3.6).
- **Round count: Property 6.** On $G_m=K_{2,m}$ plus the edge $uw$, every child that receives
  a petal must contain both $u$ and $w$. With separators and leaves of size $O(\log n)$, about
  $n/\log^2 n$ bags of one depth then contain the edge $uw$, not two. Correctness never uses
  this property, but the parallel schedule of [1] does.
- **Region bags (§9).** Every edge has two sides, and each bag $X$ keeps a set $E_X$ of
  sides: the part of the plane it was cut from. Its region graph $R_X$ has the edges with a
  side in $E_X$. The children of $X$ split $E_X$, so every edge lies in at most two region
  graphs per depth (Lemma B1(a)). The separation properties carry over (Lemma B1(b) to
  (d)), and so do §3 to §6 and Lemma V, with sizes one log factor larger.
  - The spanning tree $T_X$ is the BFS tree restricted to $R_X$ plus connectors. Lemma B1(e)
    bounds its components by $3+(d-1)(d+2)/2$ at depth $d$, so its diameter is
    $O(D\log^2 n)$. The proof counts how often a child meets the separator, against the
    holes of the parent's region. [8, Claim 4.6] gives one new component per level, and we see a
    possible gap there (`notes/LEMMA15.md` §1).
  - The separator is Lemma B5. A thin neighbourhood of $T_X$ has a circle as boundary, and
    non-tree edges are non-crossing chords of the outside. The number of vertices on one side
    of a fundamental cycle is read off the number of tree-edge sides along one arc of that
    circle, so all counts are prefix sums along a tour that passes each tree edge twice, computed in $O(\text{depth})$
    rounds. If no real fundamental cycle is balanced, a fan of virtual chords inside one face
    finds one, as in the classical planar
    separator theorem. Every other step is flooding or BFS inside $R_X$. We use
    this instead of [8, Thm 4.4], whose proof re-embeds an augmented graph with [15], which
    need not keep the embedding the regions refer to.
- **Analytic layer (§4 to §7).** Lemma 15 of [1] has further gaps, all fixed here:
  - with the witness suggested in the text, the error exponent doubles at every level;
  - the linear program has no triangle constraints;
  - the bit size of the solutions is not controlled;
  - two gluing steps are not proved;
  - unreachable pairs are not handled;
  - one property of the child bags is used without being stated.

  With $\varepsilon'=\varepsilon/(2(3H+1))$, where $H=O(\log n)$ is the height of the
  decomposition, the labels keep size $\tilde O(D/\varepsilon)$.
- **Realization.** In place of [1, Thm 2] we use [10, Thm 1], which is refereed: every
  quasimetric that is Monge for a prescribed circular order is realized by a plane digraph
  with $O(|T|^6)$ vertices and its terminals on the boundary in that order. CONGEST does not
  charge for local computation, so a bag's centre can find such a graph by exhaustive search.
  The proof in [10] is a greedy construction, but [10] bounds the running time only for
  finding the order, not for the construction. Polynomial local time would need that analysis,
  or [1, Thm 2], whose proof does not show the order guarantee.

### Theorem B (negative weights)

The bound below is that of the paper. [`notes/NEGATIVE.md`](notes/NEGATIVE.md) claims $\tilde O(D)$ with high probability.

**Theorem B.** Let $G$ be a planar digraph with integer weights of polynomial size, possibly
negative, hop diameter $D$ and source $s$. A CONGEST algorithm either computes exact distances
from $s$ or reports a negative cycle, in $D\cdot(\log n)^{O(\sqrt{\log n})}=D\cdot n^{o(1)}$ rounds
with high probability.

[6, Thm 2] reduces the problem to nonnegative SSSP from a virtual source, which Theorem A with
Lemma V solves in $\tilde O(D)$. In [6], the term $\sqrt n+D$ comes only from simulating
minor-aggregation steps. On planar networks these cost $\tilde O(D)$ through low-congestion
shortcuts [9, Cor. 4.6, Lemma 4.8]. Negative cycles are already reported by [6, Thm 60].

The reduction uses [6, Cor. 33]. As we read its base case, two sets of one recursion level can get
equal labels, which hints at a possible gap in its proof. A leader identifier in the label closes
this, see Section 8 of [`notes/NEGATIVE.md`](notes/NEGATIVE.md), where the paper is cited as [3].
We use the corollary in that form, and the statement of [6, Thm 2] as it stands.

### Lemma D, Theorem C and Theorem C′ (maximum flow)

The bound of Theorem C below is that of the paper. [`notes/NEGATIVE.md`](notes/NEGATIVE.md) claims $\tilde O(D)$ with high probability.

**Lemma D.** Take the face-disjoint graph $\hat G$ of [9, Sec. 3]. It has a star centre for
every vertex, a copy of the vertex for every corner, a cycle $E_R$ through the corners of each
face, one edge $E_C$ per primal edge, and star edges $E_S$. Weight it with 0 on $E_R$, the
dual dart lengths on $E_C$, and a large $M$ on $E_S$. Then $\hat G$ has a negative cycle iff the
dual graph has one, and otherwise distances between corners equal dual distances between their
faces. By [9, Props 1 to 3], $\hat G$ is planar, has hop diameter at most $3D+2$, and every
algorithm on it runs on $G$ with a factor 2 in rounds.

So primal algorithms solve dual distance problems: dual SSSP takes $\tilde O(D)$ with
nonnegative lengths (Theorem A) and $D\cdot n^{o(1)}$ with negative ones (Theorem B). Both were
$\tilde O(D^2)$ [9, Lemma 2.2]. The weights on $E_C$ are already in [9, Prop. 5]; the new parts
are the weights on $E_R$ and $E_S$ and running primal algorithms on the result.

**Theorem C.** Let $G$ be a directed planar network with integer capacities in
$\lbrace 0,\dots,\mathrm{poly}(n)\rbrace$ and terminals $s,t$. A CONGEST algorithm computes a maximum
st-flow, its value and the flow on every edge, in $\min\lbrace\tilde O(D^2),\ D\cdot n^{o(1)}\rbrace$
rounds with high probability.

The proof is the reduction of [11] as used in [9, Sec. 6.1]: a binary search on the flow value,
where each step is a dual negative-cycle test, now done with Lemma D and Theorem B. A minimum
cut follows from reachability in the residual graph, in $\tilde O(D)$.

**Theorem C′.** If $s$ and $t$ lie on a common face, the maximum st-flow is computed exactly in
$\tilde O(D)$ rounds for directed networks, deterministically given a planar embedding. This
is the method of [12]:
add a chord between $s$ and $t$ inside the face and compute one dual SSSP with nonnegative
lengths. [9, Thm 1.3] gives a $(1-o(1))$-approximation for undirected networks in
$D\cdot n^{o(1)}$ rounds, and [18] one in $\tilde O(D)$ rounds for any $s$ and $t$.

### Theorem D (exact minimum st-cut, undirected)

**Theorem D.** Let $G$ be an undirected planar network with integer capacities of polynomial
size and terminals $s,t$. A CONGEST algorithm computes the value of a minimum st-cut, which is
the maximum st-flow value, in $\tilde O(D)$ rounds; every vertex learns its side and its cut
edges. It is deterministic given the embedding algorithm of [15], as in [18], and
deterministic face identifiers (G6).

[18] computes a $(1+o(1))$-approximate minimum st-cut with a recursion: $O(\log n)$
levels of incisions in the dual, each with $O(1)$ rounds of SSSP, one source per annulus. Its correctness argument
[18, Lemma 2.7] holds unchanged with exact shortest paths. Its recursion needs one repair
(Lemma S below), and the SSSP step needs replacing. [18] runs approximate SSSP on each annulus through minor aggregation, because
annuli can have large diameter. We instead run Theorem A on the whole graph $\hat G_\ell$ of
[18, Thm 3.1], which is planar, has hop diameter at most $4D+4$ (from the bound $4D$ between
star centres of [18, Lemma 3.4]) and is simulated on $G$ with
four rounds per round. Its weights are 0 on the paths that represent dual nodes,
$K\cdot c(e)+1$ on the edges that represent dual edges of live annuli, and a large $M$ on all
other dual edges and on the star edges between copies of a vertex, from a virtual source with
one zero-weight arc per annulus. As in
Lemma D, distances below $M$ are exact annulus distances, and the $+1$ breaks ties so that
the parent choices form shortest-path trees. Details are in `notes/NOTES.md` §5.

**The endpoint repair.** [18, Remark 3.3] adjusts $\hat G_\ell$ at $s$ and $t$ through two
edges $e_0$ and $e_{\text{last}}$ next to the first and last dual nodes of the first cut path.
Read literally, it breaks [18, Thm 3.1 (1), (2)] in three ways (scripts in `sim/thmD/`):
- If a later incision passes through $e_0$ or $e_{\text{last}}$, Remark 3.3 treats that edge like
  any other incised edge. Its copies and its $E_C$ edge then attach to the plain copy of $s$ or $t$
  that belongs to the node-part on the other side of the endpoint split, so the paths of
  $\hat G_\ell$ on that face no longer match its node-parts, and the two sides of the split are
  joined at cost 0. Smallest witness: vertices 0 to 3, edges
  $\lbrace 0,3\rbrace,\lbrace 0,1\rbrace,\lbrace 1,2\rbrace,\lbrace 2,3\rbrace$ with capacity 1 and
  $\lbrace 3,1\rbrace$ with capacity 5, $s=1$, $t=2$: minimum cut 2, computed 0 in 3 of 120 runs
  that vary $f$, $g$ and the corners, those where $P_1$ runs through $e_{\text{last}}$.
- If $e_0=e_{\text{last}}$ is the edge $st$, the two endpoint rules change the copies of the same
  edge: the dual edge $(p_0^0,p_{\text{last}}^1)$ gets no $E_C$ edge and two wrong ones appear. On
  a triangle $s,t,x$ with capacity 3 on $st$ and 1 elsewhere, both ends choose $st$ in 5 of 80
  runs, and the literal graph fails its checks in each of them.
- [18, Sec. 5] lets $s$ take either edge of the face $p(p_0)$ at $s$ whose dual is off the path
  as $e_0$, but the formula fits only one of the two. In 72 of 300 random instances that edge
  lies on the path; then we use the mirrored copy.

The repair: an incised $e_0$ attaches on the cut side to a fresh copy of $s$ (and likewise
$e_{\text{last}}$ at $t$), and each dual edge joins the copies its two path edges actually
attach to. It is local at $s$ and $t$ and adds at most two vertices. The repaired graph passed
79,000 runs on 64,000 instances with exact distances, trees and cut values; every one of 1,848
graphs built for a planarity check was planar with hop diameter at most $4D+4$. The literal
graph failed in about a third of the instances. Lemma R (`notes/GHAT_REPAIR.md`, 2026-10-29)
defines the repaired graph formally and proves what Theorem D needs from it: the properties
[18, Thm 3.1 (1), (2)], planarity with an explicit rotation at every copy, the diameter bound,
and the local phase of [18, Lemma 3.17]. Its definition, its properties (1), (2) and (5), the
planarity (3) with the rotation of Table R, the hop bound and the copy count of (4), the
combinatorics of the global and local phases in (6) and the distances on the repaired graph hold in Lean (`lean/SsspFlow/GHat.lean`,
`lean/SsspFlow/GHatDist.lean`, `lean/SsspFlow/GHatProps.lean`, `lean/SsspFlow/GHatPlanar.lean`). An independent implementation of its definition
matched the tested graph on 98,000 instances. Lemma R needs a description of the dual nodes
that is not stated in [18]. Lemma N proves it, by induction over the levels, and the reduction
is correct for every legal choice at $s$ and $t$. In Lean, the pieces of Definition R are the
vertices of the split model of the incisions and its pairs are the edges, every annulus of a
level is a component of the token graph of the whole level, and so the length $\lambda_t$ of an
annulus is the distance of its two pieces in that token graph, and in the repaired graph when it
is below $M$ (`lean/SsspFlow/GHatSplit.lean`, `lean/SsspFlow/Annuli.lean`). These failures may
come from a misreading of [18] on our side. We have not checked whether they affect the approximate algorithm of [18].

**The recursion repair (Lemma S).** The recursion of [18, Alg. 3] computes the shortest
cycle $P_i$ through the middle index $i$ of an annulus with index range $[j,k]$, and then
drops every index strictly between $i_1$ and $i_2$, the least and greatest index of the first
cut path on $P_i$ ([18, Claim 2.4, Lemma 5.6]). The reason given is that $P_{i_1}$ or $P_{i_2}$
is no longer. But an annulus can hold copies of the first cut path outside $[j,k]$, so $i_1$ or
$i_2$ can lie outside the range and be dropped by another annulus. There are
instances where two drops rest on each other and no computed cycle is minimum, with exact
shortest paths that are all unique. Smallest: a simple graph with 11 vertices and 22 edges,
minimum cut 15, computed 37 (`sim/thmD/testR/logs/trace_min_simple0.txt`). The driver
`sim/thmD/thmD.py` gives 37 as well. The repair computes two more cycles in every annulus that is not
a leaf, at $i^-=\max(i_1,j)$ and $i^+=\min(i_2,k)$. That is two more SSSP calls per level, so the
round bound is unchanged. Lemma S (`notes/RECURSION.md`) proves an interval form of
[18, Claim 2.4]: a dropped index is dominated by every index between it and $i_1$, or by every
index between it and $i_2$. So one of $i^-$, $i^+$ carries the minimum. This recursion argument is
in Lean (`lean/SsspFlow/Recursion.lean`), with the interval form and Lemma O as hypotheses. The interval form is in Lean
as well (`lean/SsspFlow/WitnessInterval.lean`), and its separation step (S_1) follows from a drawing of the annulus as a
planar map with the two copies of the first cut path on one face (`lean/SsspFlow/Separation.lean`). The cut of a planar
map along a shortest path between corners of two different faces is such a drawing, so Lemma S1 holds in Lean on the cut
itself, with no hypothesis beyond the map, the path and the weights (`lean/SsspFlow/CutMap.lean`,
`lean/SsspFlow/CutAnnulus.lean`). The facts of Lemma O that the recursion uses hold in Lean as well, in a split model of
the incisions, and with them a run of the recursion on the cut computes the least $\lambda_t$
(`lean/SsspFlow/Pieces.lean`, `lean/SsspFlow/Run.lean`). With the repair the driver
is right on all 25 failing instances of the search (161 of 300 runs were wrong without it)
and on 1,440,000 sweep instances, where it made 6 errors in 1,200,000 without the repair.
Lemma S needs a side lemma (Lemma O) about one incision, which the proof of Theorem D also uses,
and the exact form of [18, Claim 2.3]. `notes/LEMMA_O.md` proves both, by an induction over the
levels in which each incision is a simple closed curve and the sides are its two sides; the
overlap rule is exact on all of $[j,i]$, from any common node. Two points of Lemma O are readings
of [18]: the bound in the overlap test is the copy of the parent's incised part, not its whole path, and a side with overlap or an empty
range gets no call (`notes/LEMMA_O.md` §9). As
we read [18], its own approximate recursion has the same defect; we have not checked whether
another reading avoids it.

## What is assumed

Beyond the results cited in the proofs, these enter as black boxes:
- **(G1) The decomposition** of [1, Lemma 9], as built in [8, Sec. 4.2]. We use the shape of
  its child bags as we read it off [8], and spanning trees of diameter $O(D\log n)$ per bag.
  [1] states height $O(D)$, which [8] does not give; the difference costs one log factor.
  This is needed only for the induced form of the labels (`notes/LEMMA15.md` §3 to §6). The
  final theorems use the region decomposition of §9, which is constructed and analysed there;
  its height bound and bag identifiers are only sketched.
- **(G3) Realization**, [10, Thm 1], with the size bound of [10, Section 5]. It gives existence
  only, so a bag centre searches exhaustively, which takes exponential local time (CONGEST does
  not count it).
- **(G4)** Distances in a graph drawn in a disk satisfy the Monge condition in boundary order.
  This is standard. The notes give the proof, and `lean/SsspFlow/Crossing.lean` proves it for
  rotation systems.
- **(G5) Distance oracles** for planar digraphs [13, Thm 3.16], as used in [1, Lemma 11], with the
  reachability labels of [13, Thm 2.7] for lengths 0.
- **(G6) Face identifiers** in $\tilde O(D)$ rounds [9, Lemma 5.11], deterministically
  [18, Lemma 3.17] with [20, Thm 1.5].

The proof in Lean of the Label Hypothesis takes (G3), (G5) and (G6) as hypotheses. It builds its decomposition
itself, so it does not use (G1), it proves what it needs of (G4), and it proves the aggregation primitive it calls.
Theorem A in Lean takes the same three as hypotheses, since the smoothing of [3] is proved as well.

## Machine-checked proofs (`lean/`)

Lean 4 (`leanprover/lean4:v4.36.0-rc1`) with Mathlib; the exact Mathlib revision is pinned in
`lean/lake-manifest.json` and in `lean/lakefile.toml`. All theorems depend only on the
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). There is no `sorry`.
`lake env lean SsspFlow/Axioms.lean` prints the axioms of every named theorem; its output is in
`lean/axioms.txt`. In a fresh clone, run
`lake exe cache get` before `lake build`, or Lake compiles all of Mathlib from source.

- `lean/SsspFlow/LemmaV.lean`, theorem `SsspFlow.Hierarchy.lemmaV`: Lemma V for an abstract bag
  hierarchy with arc lengths in $[0,\infty]$, distances as infima over walks, and estimates
  within $1+\varepsilon$ of the distances in each bag. The hypotheses on the hierarchy follow
  from the decomposition's separation property. No finiteness is assumed.
- `lean/SsspFlow/LemmaD.lean`: Lemma D.
- `lean/SsspFlow/Replacement.lean`: the crossing step, the telescoping and the two cases of the undirected formula of `notes/REPLACEMENT.md`.
- `lean/SsspFlow/Recursion.lean`: the recursion argument of Lemma S2 of `notes/RECURSION.md`, on
  an index model of [18, Alg. 3] with the conclusion of Lemma S1 and (INV) as hypotheses. With
  the two extra calls, the least computed length is the minimum (`Recursion.Rec.isLeast`);
  without them the recursion can miss it (`Recursion.miss`, on the index pattern of the
  eleven-vertex instance).
- `lean/SsspFlow/WitnessInterval.lean`: Lemma S1 of `notes/RECURSION.md`, the interval form, on the level-one annulus
  as a weighted graph with two copies of each face of $P$. The facts on $P$, (P) and the copies of its parts, are
  fields of `Annulus`, and the separation step (S_1) is the hypothesis `Annulus.Sep`. `Annulus.witness_interval`: on
  a shortest walk between the two copies of $p_i$, the least and the greatest index of a copy are
  $\min(i,x,y)$ and $\max(i,x,y)$, and every index strictly between them is dominated by every index between it
  and one of the two. `Annulus.nodeOfWalk` gives the field `dom` of a node of `Recursion.lean`.
- `lean/SsspFlow/Separation.lean`: the separation step (S_1) when the annulus is drawn as a planar map in which the
  copies $p_0^0,\dots,p_m^0,p_m^1,\dots,p_0^1$ are corners of one face in this cyclic order. A walk from $p_x^0$ to
  $p_y^1$ and a walk between the two copies of $p_t$, with $t$ strictly between $x$ and $y$, join interleaved corners
  of that face, so the crossing lemma of `Crossing.lean` gives a common vertex (`Annulus.sep_of_faceDrawn`).
  `Annulus.witness_interval_of_faceDrawn` is Lemma S1 for such an annulus.
- `lean/SsspFlow/CutMap.lean`: the cut of a rotation system $R$ along a path $p_0,\dots,p_m$ through distinct vertices,
  with corners at $p_0$ and $p_m$ on two different faces. Every edge is doubled into a digon, and the doubled map is
  split at the two corners of the slit at each $p_t$. `CutPath.psi_eq`: the first returns of the rotation and of the
  faces to these corners compose to the cycle $p_0^0,\dots,p_m^0,p_m^1,\dots,p_0^1$. `CutPath.faceDrawn`: if $R$ is
  planar and connected, the cut is planar and these copies are corners of one face in this cyclic order, at distinct
  vertices. `CutPath.isWalk_fst`: a walk of the cut is a walk of $R$.
- `lean/SsspFlow/CutAnnulus.lean`: the level-one annulus on the cut, for dart weights that agree on the two darts of each
  edge and a shortest path $P$ from $p_0$ to $p_m$ with positive weights. An edge joins two distinct vertices of the cut that a
  dart joins, with the least weight of such a dart. `CutPath.short` is (P), `CutPath.copy` gives the copies of the
  parts of $P$, and `CutPath.witness_interval` is Lemma S1 on the cut.
- `lean/SsspFlow/Incision.lean`: the cut of a disk along one chord. In the split of the doubled map at a set $\Gamma$ of
  corners, `Boundary` says that a list holds the corners of $\Gamma$ on one face of the split in their cyclic order; if
  the map is planar and connected and $\Gamma$ is connected, a corner of $\Gamma$ lies in the component of the list
  exactly if it lies on the list (`Boundary.gcomp_iff`). A `DiskChord` is a walk from the vertex of a corner $k_a$ to
  the vertex of another corner $k_b$ of one boundary $k_a,a_1,\dots,a_p,k_b,b_1,\dots,b_q$, along distinct edges that
  are not cut, through distinct inner vertices without a corner of $\Gamma$. Cutting along it adds the two digon
  corners $m_j$, $r_j$ of each edge to $\Gamma$. `DiskChord.boundary_one`, `DiskChord.boundary_two`: the cut has the
  boundaries $m_0,\dots,m_{n-1},k_b,b_1,\dots,b_q$ and $k_a,a_1,\dots,a_p,r_{n-1},\dots,r_0$, and the other
  boundaries stay. `DiskChord.gcomp_one_iff`, `DiskChord.gcomp_two_iff`, `DiskChord.not_gcomp`: these are two
  different components. `DiskChord.cut_inner`, `DiskChord.cut_start`, `DiskChord.cut_stop`: every vertex of the chord
  splits into one vertex on each side, and the other vertices stay (`DiskChord.fconnect_cut_iff`).
  `DiskChord.isWalk_one`, `DiskChord.isWalk_two`: the two copies of the chord are walks of the cut, one on each side.
- `lean/SsspFlow/Exchange.lean`: the exchange behind (C23) of `notes/LEMMA_O.md`, for dart weights that agree on the
  two darts of each edge. Let $a,b,c,d,e$ be corners in this cyclic order on one face of a planar map, and let $P$ be
  a shortest walk of finite length from the tail of $b$ through the tail of $e$ to the tail of $c$. A walk from the
  tail of $a$ to the tail of $d$ crosses both parts of $P$, and swapping in the part of $P$ between the two crossings
  gives a walk through the tail of $e$ that is no longer. So the distance from $a$ to $d$ is at least the distance
  from $a$ to $e$ plus the distance from $e$ to $d$ (`FaceDrawn.exchange`), and equal to it by the triangle inequality
  (`walkDist_triangle`).
- `lean/SsspFlow/EdgeCut.lean`: the cut of one edge whose digon corners $m$, $r$ are not in $\Gamma$, from the vertex
  of a corner $k_1$ of $\Gamma$. If the head carries no corner, the boundary $k_1,a_1,\dots,a_p$ becomes
  $k_1,a_1,\dots,a_p,m,r$ (`EdgeCut.boundary_slit`) and the head stays one vertex (`EdgeCut.cut_head_free`). If the
  head carries the corner $k_2$, the boundary $k_1,a_1,\dots,a_p,k_2,b_1,\dots,b_q$ becomes the two boundaries
  $k_1,a_1,\dots,a_p,r$ and $m,k_2,b_1,\dots,b_q$ (`EdgeCut.boundary_hi`, `EdgeCut.boundary_lo`), and the head splits
  in two (`EdgeCut.cut_head`). The tail splits in two (`EdgeCut.cut_tail`), the copy $(d,\mathrm{true})$ of the edge
  starts at the vertex of $k_1$ (`EdgeCut.cut_rot_k1`), the other boundaries and vertices stay
  (`EdgeCut.boundary_of_boundary`, `EdgeCut.fconnect_cut_iff`), and the corners stay connected
  (`EdgeCut.skeletonConnected`).
- `lean/SsspFlow/WalkCut.lean`: the cut along a walk. A `WalkCut` is a walk of the split from the
  vertex of $k_a$ to the vertex of $k_b$ for a boundary $k_a,a_1,\dots,a_p,k_b,b_1,\dots,b_q$, with distinct vertices
  and distinct edges, whose vertices after the first carry no corner of $k_a,a_1,\dots,a_p$. Unlike a `DiskChord` it
  may pass through corners of $b_1,\dots,b_q$ and run along edges cut at both digon corners, the first of them through
  its copy $(d,\mathrm{true})$. Cutting it adds the digon corners of all its edges to $\Gamma$, one edge at a time
  (`WalkCut.state`). If the map is planar and connected and $\Gamma$ is connected, the side of $k_a$ has the boundary
  $k_a,a_1,\dots,a_p,r_n,\dots,r_1$, with $r_j$ the digon corner of the $j$-th edge at its head
  (`WalkCut.boundary_hi`), and its corners are the corners in the component of $k_a$ (`WalkCut.gcomp_hi_iff`). The
  copies $(d,\mathrm{true})$ of the edges form a walk on this side (`WalkCut.isWalk_hi`), every vertex of the walk has
  exactly one part on this side (`WalkCut.part_hi`, `WalkCut.part_hi_last`), and the other vertices stay
  (`WalkCut.fconnect_cut_iff`). If moreover the vertices after the first carry no corner of $k_b,b_1,\dots,b_q$
  and the last edge, if it is cut at both digon corners, is used through its copy $(d,\mathrm{false})$, the walk
  read backwards is a `WalkCut` that cuts the same edges (`WalkCut.reverse`, `WalkCut.reverse_Γ'`). Then the side
  of $k_b$ has the boundary $k_b,b_1,\dots,b_q,m_1,\dots,m_n$, with $m_j$ the digon corner of the $j$-th edge at
  its tail (`WalkCut.boundary_lo`, `WalkCut.gcomp_lo_iff`), the copies $(d,\mathrm{false})$ of the edges form a
  walk on it (`WalkCut.isWalk_lo`), every vertex of the walk has exactly one part on it (`WalkCut.part_lo`,
  `WalkCut.part_lo_last`), and the two sides are different components (`WalkCut.not_gcomp`).
- `lean/SsspFlow/Overlap.lean`: (C23) of `notes/LEMMA_O.md` for a planar map with a face whose corners read
  $\kappa_0(x_a),\dots,\kappa_0(x_b),L_b,\kappa_1(y_b),\dots,\kappa_1(y_a),L_a$ in this cyclic order, the form of the
  boundary of a live annulus with its pieces of $p_t^0$ and $p_t^1$ and its bounding paths $P_a$ and $P_b$
  (`cornerSeg`), for dart weights that agree on the two darts of each edge. If a shortest walk from the tail of
  $\kappa_0(i)$ to the tail of $\kappa_1(i)$ passes through the tail of $\kappa_0(x_a)$, of a corner of $L_a$ or of
  $\kappa_1(y_a)$, then for $\max(x_a,y_a)\le\mu\le i$ the distance from $\kappa_0(\mu)$ to $\kappa_1(\mu)$ is the
  distance from $\kappa_0(\mu)$ to that vertex plus the distance from it to $\kappa_1(\mu)$ (`FaceDrawn.overlap_a`). The
  same holds with $\kappa_0(x_b)$, $L_b$ and $\kappa_1(y_b)$ for $i\le\mu\le\min(x_b,y_b)$ (`FaceDrawn.overlap_b`). Both
  follow from `FaceDrawn.exchange`, a face read from another corner (`FaceDrawn.rotate`) and the symmetry of the
  distance (`walkDist_comm`).
- `lean/SsspFlow/Reroute.lean`: (INV) of `notes/LEMMA_O.md` on the side of $k_a$ of the cut along a walk. A walk of
  the cut is a walk of the split (`isWalk_of_split_subset`), so distances do not shrink
  (`walkDist_le_of_split_subset`). Let the walk of the cut be a shortest walk between its ends, of finite length, for
  dart weights that agree on the two darts of each edge. Then a walk of the split between two darts of the side of
  $k_a$ gives a walk of the cut between them that is no longer (`WalkCut.reroute`). It follows the first walk up to
  its first vertex on the walk of the cut, runs along the copies $(d,\mathrm{true})$ to its last vertex there and
  follows the first walk from there (`IsWalk.split_first`, `IsWalk.split_last`, `WalkCut.lift_first`,
  `WalkCut.lift_last`). So on the side of $k_a$ the distances after the cut are the distances before it
  (`WalkCut.walkDist_hi`).
- `lean/SsspFlow/Live.lean`: the invariant (I) of `notes/LEMMA_O.md` in the split model. A live annulus
  (`CutPath.Live`) is the component of a corner of $\Gamma$ in the split of the doubled map whose boundary reads
  $\kappa_0(x_a),\dots,\kappa_0(x_b),L_b,\kappa_1(y_b),\dots,\kappa_1(y_a),L_a$ (`liveBoundary`). Its corner
  $\kappa_0(t)$ lies at the copy $p_t^0$ of the cut and $\kappa_1(t)$ at $p_t^1$, the corners of $L_a$ and $L_b$
  lie off the path, no cut edge off the path has both digon corners on the boundary, and the distance between
  $\kappa_0(t)$ and $\kappa_1(t)$ is $\lambda_t$ for $\max(x_a,y_a)\le t\le\min(x_b,y_b)$. The cut of the doubled
  map along the path is one (`CutPath.liveOne`, Claim 2). A step (`CutPath.Live.Step`) is a simple walk $Q$ from
  the vertex of $\kappa_0(x)$ to the vertex of $\kappa_1(y)$, shortest between its ends and of finite length, with
  its inner vertices off the path and through no edge of the path. It uses each cut edge through one of its two
  copies only (`CutPath.Live.hold_of_walk`, `edges_of_copies`). If the side of $\kappa_0(x)$ holds another corner,
  or $Q$ has more than one edge, or its first edge is not cut, then $Q$ starts on a cut edge through its copy
  $(d,\mathrm{true})$ (`first_of_boundary`, from the head of a cut edge, `head_eq_psi`). Then the cut along $Q$ is a
  `WalkCut`, read from $\kappa_0(x)$ (`CutPath.Live.hiCut`) or backwards from $\kappa_1(y)$
  (`CutPath.Live.loCut`). If $Q$ avoids the corners of $L_b$, the side of $\kappa_0(x)$ is a live annulus with
  $x_a=x$ and $y_a=y$ (`CutPath.Live.hi`). If $Q$ avoids the corners of $L_a$, the side of $\kappa_1(y)$ is a live
  annulus with $x_b=x$ and $y_b=y$ (`CutPath.Live.lo`). The distances on the side come from
  `WalkCut.walkDist_hi` (Claim 13), and the rest of the invariant passes to the side (Claim 14, `WalkCut.old_hi`).
- `lean/SsspFlow/Pieces.lean`: (I3) of `notes/LEMMA_O.md`. A dart of the doubled map at $p_t$ lies in the cut at
  exactly one of the copies $p_t^0$, $p_t^1$ (`CutPath.sector`, `CutPath.not_sector_both`), and a dart of an edge of
  the path joins two copies of one side (`CutPath.side_eq`, `CutPath.not_mem_Γ_of_sides`). A dart of a live annulus
  at the copy $p_t^0$ lies at the vertex of $\kappa_0(t)$, and then $x_a\le t\le x_b$; at the copy $p_t^1$ it lies at
  the vertex of $\kappa_1(t)$, and then $y_a\le t\le y_b$ (`CutPath.Live.piece`). A simple shortest walk of finite
  length from the vertex of $\kappa_0(i)$ to the vertex of $\kappa_1(i)$ contains a step: its part from its last
  vertex at a copy $p_x^0$ to the first vertex at a copy $p_y^1$ after it (`CutPath.Live.exists_step`).
- `lean/SsspFlow/Run.lean`: the recursion [18, Alg. 3] with the repair, on the live annuli of the split model. A run
  on a live annulus with the index range $[j,k]$ (`CutPath.Run`) is a leaf if $k\le j+1$, with the lengths at $j$ and
  $k$. Otherwise it takes a shortest walk $P_i$ from $\kappa_0(i)$ to $\kappa_1(i)$ for $i=\lfloor(j+k)/2\rfloor$,
  the least and the greatest index $i_1$, $i_2$ of a copy of the path at a vertex of $P_i$ (`CutPath.idx`) and a step
  of $P_i$, and it computes the lengths at $i$, $\max(i_1,j)$ and $\min(i_2,k)$. Each side has an overlap, if $P_i$
  passes through a corner of its bound, and then the length through that corner is computed for every index between
  the end of the range and $i$; or its child is the live annulus on its side of the step (`CutPath.Live.lo`,
  `CutPath.Live.hi`); or its range is empty. The bound of the side of $j$ is $\kappa_0(x_a)$, $L_a$, $\kappa_1(y_a)$
  and that of the side of $k$ is $\kappa_0(x_b)$, $L_b$, $\kappa_1(y_b)$; the two end corners belong to the bound
  also where no bounding path exists, which (C23) allows. Every computed length is $\lambda_t$ of its index $t$
  (`CutPath.Run.vals_eq`), in the annulus by (INV) and through the corner of an overlap by (C23). A walk of the cut
  gives a walk of the annulus of `CutAnnulus.lean` that is no longer (`IsWalk.exists_adjWalk`,
  `CutPath.exists_walk`, `CutPath.lamD_eq`). So Lemma S1 holds for the image of $P_i$ in the cut
  (`CutPath.Live.dom`), a run is a tree of the index model of `Recursion.lean` with the same computed indices
  (`CutPath.Run.toRec`, `CutPath.Run.computed_eq`), and by Lemma S2 the least computed length of a run on the cut is
  the least $\lambda_t$ (`CutPath.Run.isLeast`). A run on the cut exists (`CutPath.exists_run`,
  `CutPath.nonempty_run`), since shortest walks exist (`CutPath.Live.exists_shortest`) and a side without overlap
  avoids its bound, so that its child is a live annulus. `CutPath.recursion_cut` collects these facts for a planar
  connected map, natural dart weights that agree on the two darts of each edge, and a shortest path with positive
  weights between corners of two different faces.
- `lean/SsspFlow/GHat.lean`: Definition R of `notes/GHAT_REPAIR.md`, for a graph with a rotation system, a set of
  incised edges, a set of cut corners with their modes and a host for the pair of each unincised edge (`RData`): the
  tokens (`RData.IsTok`) and their pairs (`partner`), the face walk of the tokens (`RData.succ`), the links between
  consecutive tokens without a cut between them (`RData.Link`), the pieces (`RData.Piece`), the copies (`Copy`,
  `RData.Valid`), the E_R edges after repair (a) (`RData.alpha`, `RData.beta`), the E_S edges (`RData.ES`) and the
  ends of the E_C edges after repair (b) (`RData.att`). Claims 1 and 2 of the note: the ends of an E_R edge are valid
  copies other than star centres (`RData.valid_alpha`, `RData.valid_beta`, `RData.alpha_ne_star`,
  `RData.beta_ne_star`), distinct if the graph has no loops (`RData.alpha_ne_beta`); $\alpha$ and $\beta$ are
  injective on tokens (`RData.alpha_inj`, `RData.beta_inj`); $\beta(y)=\alpha(z)$ exactly when $z$ follows $y$ in a
  piece (`RData.beta_eq_alpha_iff`); and every valid copy other than a star centre is an end of an E_R edge
  (`RData.exists_end`). So the E_R edges, directed from $\alpha$ to $\beta$, have in- and out-degree at most one.
  A copy belongs to the piece of its tokens (`RData.pieceOf_eq`), an E_R edge joins two copies of one piece
  (`RData.pieceOf_er`), and the copies of one piece are joined by E_R edges (`RData.ring_conn`). Hence the E_R edges
  of each piece form a path or a cycle, and those of distinct pieces are disjoint: property (1) of Lemma R. Property
  (2): the E_C edge of a pair joins the paths of the pieces of its two tokens (`RData.pieceOf_att`), at two copies of
  its host (`RData.owner_att_partner`).
- `lean/SsspFlow/GHatDist.lean`: the repaired graph as a multigraph on the copies (`RData.Arc`), with weight $0$ on
  E_R edges, a weight $\lambda(x)\ge0$ on the E_C edge of each token $x$ and $M\ge0$ on E_S edges, and the token
  graph on the pieces with the same weights. A walk of the token graph lifts to a walk of the repaired graph of the
  same weight between any copies of its end pieces (`RData.lift`). A walk of the repaired graph of weight below $M$
  between copies on E_R edges projects to a walk of the token graph between their pieces of the same weight
  (`RData.project`). So the distance of two copies is the distance of their pieces if that is below $M$, and at
  least $M$ otherwise (`RData.gdist_eq`), and a walk from a set of pieces closed under pairs stays in it
  (`RData.mem_of_walk`): the distance bullet of Theorem D. For the weights $K\cdot c+1$ with natural costs $c$ and
  $K$ at least the number of nodes, a walk of least weight has fewer than $K$ edges and least cost, and its weight
  divided by $K$ is that cost (`FaceDisjoint.Walk.wt_scaled`, `FaceDisjoint.Walk.decode`).
- `lean/SsspFlow/GHatProps.lean`: properties (4) to (6) of Lemma R, as far as they are combinatorics. E_S edges join
  copies of one vertex (`RData.owner_es`), and a valid copy other than a star centre is joined to the star centre of
  its vertex by one E_S edge, or by two for the copies L, R and X (`RData.star_walk`). If at most three corners are
  cut, the star centres of the two ends of an edge are joined by a walk of at most four edges (`RData.hop_dart`). So a
  walk of length $k$ in the graph gives walks of at most $4k$ edges between star centres and of at most $4k+4$ edges
  between other copies (`RData.hop_walk`, `RData.hop_copies`): the hop bound of property (4). Property (5): if the
  graph has no loops, every corner in the first face of a path through distinct faces has a flank that is not an
  edge of the path (`RotSystem.legal_flank`). Property (6): for a level before with fewer incised edges and the same
  cut corners, the parents of linked tokens are linked (`RData.link_parent`). So every piece refines a piece of the
  level before (`RData.parentPiece`, `RData.piece_parent`), and the end at the host of the parent of a token lies on
  the path of that piece (`RData.pieceOf_att_parent`): the refinement of Lemma N and the first part of Claim 3.
- `lean/SsspFlow/ListRot.lean`: a rotation system given by a list of darts at each vertex (`ListData.toRot`). Two
  darts lie at one vertex exactly when they lie in one list (`ListData.tail_eq_iff`), and a label of the darts that
  agrees on each dart and the reverse of the next dart in its list is invariant along faces
  (`ListData.lab_rev_rot_of_mem`).
- `lean/SsspFlow/GHatRot.lean`: the full repaired graph, Definition R with a rim edge at both ends of every edge, the
  copies $X(c)$ of the cut corners and the rerouted rims, with the lists of Table R at all copies (`RData.lst`).
  Every dart lies in the list of its tail (`RData.mem_lst_tl`, `RData.tl_of_mem`) and no list repeats a dart
  (`RData.lst_nodup`), so the lists define a rotation system (`RData.hRot`).
- `lean/SsspFlow/GHatPlanar.lean`: property (3) of Lemma R. The faces of the full repaired graph carry labels: a wheel
  at each dart of the graph, a quad at each edge, a face of the graph, and a lens at each incised dart
  (`RData.lab`). The label is invariant along faces (`RData.lab_face`) and takes every value (`RData.lab_surj`). With
  the counts of edges, vertices and faces (`RData.numEdges_hRot`, `RData.numVertices_hRot`, `RData.numFaces_hRot`),
  Euler's formula for the graph and connectivity (`RData.hRot_connected`), the full repaired graph is planar
  (`RData.hRot_planar`). The repaired graph $\hat G_\ell$ keeps all edges except the rims that are no E_C edges. Its
  rotation is the restriction, so it is planar (`RData.gRot_planar`), every kept dart is an arc of $\hat G_\ell$
  between the same copies and every arc is a kept dart (`RData.arc_of_keep`, `RData.keep_of_arc`). The face
  invariance needs that no incised dart has its tail corner cut in mode R and its head corner cut in mode L
  (`RData.NoConflict`). Any number of cut corners is allowed, at any vertices.
- `lean/SsspFlow/GHatRun.lean`: the levels of a run have no conflict. The two corners of a conflict are consecutive
  at one vertex of the dual, so a conflict needs two distinct cut corners there (`RData.noConflict_of_cut`). The cut
  corners of every level of a run are the corners of the cut at $s$ and $t$ (`CutPath.Run.cut_data`), at the vertices
  $p_0$ and $p_m$ of the dual path, and for $m = 0$ nothing is incised. So every level has no conflict, for any modes
  and hosts (`CutPath.Run.noConflict`), and its repaired graph is planar (`CutPath.Run.planar_data`). The count of
  copies of property (4): every copy of a level is a copy of its vertex (`RData.mem_copiesAt`), a vertex of degree
  $\deg$ has at most $3\deg + 1$ copies plus one for each cut corner at it (`RData.card_copiesAt`), and on a level of
  a run $s$ and $t$ have at most $3\deg + 2$ copies and every other vertex at most $3\deg + 1$
  (`CutPath.Run.card_copiesAt`).
- `lean/SsspFlow/GHatSim.lean`: the simulation of (4). The repaired graph as a simple graph on the copies
  (`RData.hatGraph`). An edge between copies at two different nodes is an E_R edge and follows an edge of the network
  (`RData.hatHost_of_adj`), and at most four such edges go from one node to another (`RData.card_cross_le`). So if
  each node knows the edges of the repaired graph at its own copies, the nodes run any algorithm on the repaired graph
  round for round, with messages of four times the width (`RData.run_hatSim`).
- `lean/SsspFlow/SubNet.lean`: each edge of a rotation system becomes a path of three edges (`RotSystem.subNet`).
  The result is a simple network for every rotation system, planar if the rotation system is connected and planar
  (`RotSystem.subNet_planar`), and of diameter at most $3k + 2$ if any two vertices are joined by a walk of at most $k$
  darts (`RotSystem.subNet_diam`). Renaming the nodes keeps planarity and diameter (`Net.relabel_planar`,
  `Net.relabel_diam`).
- `lean/SsspFlow/GHatNet.lean`: the repaired graph as a network. Every dart of the full repaired graph starts at a
  valid copy (`RData.valid_tl`), and a walk of $\hat G_\ell$ is a walk of the full repaired graph
  (`RData.isWalk_of_arcs`). Two valid copies whose vertices are at distance at most $D$ in $G$ are joined by at most
  $4D + 4$ arcs (`RData.arc_hop`). So the subdivided full repaired graph of every level of a run is a planar network
  on $\{0, \dots, n - 1\}$ of diameter at most $12D + 14$ (`CutPath.Run.hatNet`). The edges that $\hat G_\ell$
  drops can get the length $\infty$.
- `lean/SsspFlow/GHatLevel.lean`: the network of a level on fixed identifiers. For a plane network on $n$ nodes,
  the nodes of the subdivided repaired graph are named by a node, a neighbour and one of 21 kinds (`Net.nameC`,
  `RData.nameD`, `RData.name_injective`), so the names do not depend on the level. All other names hang as pendant
  nodes at the star centre of their node, in increasing order. The lists at the copies are those of Table R, with the
  star centre of a node in the order of its rotation list (`RData.hatNet`). They are rotations of the lists of the
  subdivided repaired graph (`RData.hatList_rot`, `RData.vList_rot`), and lists that are rotations of the lists of a
  network give the same graph and the same rotation (`Congest.Net.relist_planar`, `Congest.Net.relist_connected`,
  `Congest.Net.relist_diam`). The network of a level is planar (`RData.levelNet_planar`) and has diameter at most
  $12D + 16$ (`RData.levelNet_diam`).
- `lean/SsspFlow/GHatLevelSim.lean`: the nodes simulate the network of a level. The host of an identifier is the node
  that names it. An edge between two hosts is the middle edge of a token dart (`RData.levelNet_cross`), so it follows
  an edge of the network (`RData.levelNet_host`), and at most four go from one node to another
  (`RData.levelNet_card_cross`). If each node knows the edges at its own identifiers, the nodes run any algorithm on
  the network of a level round for round, with messages of four times the width (`RData.run_levelSim`).
- `lean/SsspFlow/GHatLevelDist.lean`: distances in the network of a level. The arcs of $\hat G_\ell$ get length $0$
  on E_R arcs, $\lambda$ of the token on E_C arcs and $M$ on E_S arcs (`RData.arcW`), and every kept dart of the full
  repaired graph is an arc of the same length between the same copies, and conversely (`RData.arc_of_keep_w`,
  `RData.keep_of_arc_w`). With these lengths on the middle edges of kept darts, $0$ between a copy and a dart and
  $\infty$ elsewhere (`RData.levelLen`), the distance between two copies in the network of a level is their distance
  in $\hat G_\ell$ (`RData.levelNet_dist`).
- `lean/SsspFlow/GHatLevelSssp.lean`: distances of a level in $O(\log^c n \cdot D)$ rounds, assuming the Exact SSSP
  bound (`ExactSsspBound`). With offset $0$ at one source copy and $\infty$ elsewhere (`RData.levelOff`), the distance
  from the virtual source is the distance in $\hat G_\ell$ from the source copy (`RData.dsrcTop_levelOff`). One
  algorithm, fixed for $n$ and $D$, computes at every copy its distance from the source copy in
  $C \log^c n' \cdot (12D + 16)$ rounds on the network of the level, with $n' = 21 n^2$ (`RData.levelSssp`), and the
  nodes of the network compute the same distances in the same number of rounds, with messages of four times the width,
  if each node knows the edges and inputs at its own identifiers (`RData.levelSssp_sim`).
- `lean/SsspFlow/GHatLevelConn.lean`: the components of a level from one more shortest-path computation. If every
  token length is $0$ or at least $M$, every walk of $\hat G_\ell$ has length $0$ or at least $M$, and the walks of
  length $0$ are the walks along E_R edges and E_C edges of tokens of length $0$ (`RData.awt_zero_or`,
  `RData.arcDist_eq_zero_iff_rtg`); with token lengths $0$ these are the E_R and E_C edges (`RData.zr_zero`), with
  token lengths $M$ the E_R edges (`RData.zr_const`). With an offset below $M$ at every copy, distinct for distinct
  copies, the distance from the virtual source at a copy is the least offset of the copies joined to it by such walks
  (`RData.zlab_spec`), so two copies get the same value exactly when they are joined (`RData.zlab_eq_iff`). Assuming
  the Exact SSSP bound, the nodes compute these labels in $C \log^c n' \cdot (12D + 16)$ rounds, with messages of four
  times the width, if each node knows the edges and inputs at its own identifiers (`RData.levelConn_sim`). With
  `RData.erc_comp_iff` and `RData.er_comp_iff`, the labels identify the annuli and the paths of the pieces.
- `lean/SsspFlow/RunDepth.lean`: the depth of a run. The sides of an annulus with the range $[j, k]$ get the ranges
  $[j, i_1]$ and $[i_2, k]$ with $i_1 \le \lfloor (j+k)/2 \rfloor \le i_2$, so a run on $[j, k]$ has an annulus at depth
  $\ell + 1$ only if $2^\ell < k - j$ (`CutPath.Run.nodes_width`), and none below depth $\log_2 (k - j) + 1$
  (`CutPath.Run.nodes_eq_nil`).
- `lean/SsspFlow/TheoremDCost.lean`: the rounds of Theorem D in a cost model. A level makes a constant number of
  calls on the network of the level: shortest paths from a virtual source (`RData.levelSssp_sim`), labels of
  components (`RData.levelConn_sim`) and part-wise aggregations, assuming part-wise aggregation on planar networks in
  $\tilde O(D)$ rounds ([9, Cor. 4.6]), stated as the proposition `PartAggBox`, plus a constant number of rounds.
  With $\log n' \le 7 \log n$ (`logN_level`) and at most $4 \log n$ levels for a cut path of length $m \le n^2$
  (`log_levels`, `CutPath.Run.nodes_eq_nil`), all levels take $O(\log^{c+1} n \cdot D)$ rounds (`theoremD_cost`).
  This is a count of rounds over the levels, not one algorithm of the message model for the whole recursion.
- `lean/SsspFlow/GHatLevelLocal.lean`: the rotation lists of the network of a level, by names. At the name of a dart
  they hold the name of the copy at which it starts and the name of the reverse dart (`RData.levelNet_rotList_dart`),
  at the name of a copy the names of its darts in the order of Table R and the identifiers that hang at it
  (`RData.levelNet_rotList_copy`), and at an identifier that names nothing the star centre $(u, u, 0)$ of its node $u$
  (`RData.levelNet_rotList_pend`). A node that knows its own name and these lists at its own identifiers knows the edges
  at them (`Congest.view_of_lists`).
- `lean/SsspFlow/GHatTableRaw.lean`: the lists of Table R from local data. Every dart carries a record of five bits that
  its tail computes (`RData.dinfo`): incised, cut corner, mode, host bit, and whether its tail corner is cut in mode R.
  Read as names, the lists at the copies $D(c)$, $L(c)$, $R(c)$ and $X(c)$ of a corner $c = (w, u)$ are functions of the
  records of the darts at $w$, the records of the darts into $w$ and the successor of $u$ in the rotation list of $w$
  (`RData.dList_raw`, `RData.lList_raw`, `RData.rList_raw`, `RData.xList_raw`), and the list at the star centre of $w$
  is a rotation of the rotation list of $w$ (`RData.starList_raw`). So a node knows these lists after one round in
  which every node sends each neighbour the record of the dart to it.
- `lean/SsspFlow/GHatLevelRaw.lean`: the rotation lists of the network of a level from local data. The node $w$ computes
  the list at each identifier $(w, u, k)$ from its rotation list, the records of the darts at $w$ and the records of
  the darts into $w$ (`rawAt`): it decides which identifiers name a node (`RData.rawReal_iff`), reads the lists of
  Table R at its copies (`RData.rCopy_name`), finds the copy at which a dart starts (`RData.rTail_nameD`) and the name
  of the reverse dart (`RData.nameD_hrev`), and lists the identifiers that name nothing at its star centre
  (`RData.extras_inl`). These are the rotation lists of the network of a level at every identifier
  (`RData.levelNet_rotList_raw`).
- `lean/SsspFlow/GHatLevelLen.lean`: the inputs of the shortest paths of a level from local data. One round in which
  every node sends each neighbour a number of its own for it (`Algorithm.run_exchTo`) carries the record of a dart and
  the three values $\lambda$ of its tokens in $3b + 5$ bits (`DInfo.unpack_pack`, `DInfo.pack_lt`). From the rotation
  list of $w$, the records and the values $\lambda$ of the darts at $w$ and into $w$, the bound $M$ and the identifier
  of the source, the node $w$ computes the length of each dart and whether $\hat G_\ell$ keeps it
  (`RData.rawW_nameD`, `RData.rawW_rev`, `RData.rawKeep_nameD`), and so the input of each of its identifiers, with its
  neighbours, the lengths to and from them and its offset (`RData.levelNet_oracleIn_raw`).
- `lean/SsspFlow/GHatLevelSsspLocal.lean`: the distances of a level from local inputs. Every node starts with its
  name, its rotation list, the records and the values $\lambda$ of the darts at it, the bound $M$ and the identifier
  of the source copy (`RData.levelIn`). Assuming the Exact SSSP bound, one algorithm of the message model, fixed before
  the network, runs the exchange round and then the simulation of the shortest paths of the level, and after
  $C \log^c n' \cdot (12D + 16) + 1$ rounds holds at every copy its distance in $\hat G_\ell$ from the source copy,
  with messages of $4C\log^c n' + 3(K \log n' + 1) + 5$ bits for lengths up to $(n' + 2)^K$ and $n' = 21n^2$
  (`RData.levelSssp_local`).
- `lean/SsspFlow/GHatLevelConnLocal.lean`: the components of a level from the same local inputs. The host of a copy
  computes its start offset from the name of the copy (`RData.labOff_raw`). Assuming the Exact SSSP bound, one
  algorithm of the message model, fixed before the network, holds after $C \log^c n' \cdot (12D + 16) + 1$ rounds a
  label at every copy, and two copies have the same label exactly when they are joined by arcs of length 0
  (`RData.levelConn_local`).
- `lean/SsspFlow/GHatRuleM.lean`: Rule M as a local rule. A node holds a token at the end of its pair on its own side
  of the dart, and Rule M reads the end of the parent token on the same side of the same dart (`RData.ruleEnd`), which
  is a copy of the same node (`RData.owner_ruleEnd`). Tokens of one component of the token graph of a level are matched
  with copies of one component of $\hat G_{\ell-1}[E_R \cup E_C]$ (`RData.ruleM_comp`), so they read the same label of
  the level before (`RData.ruleM_lab`).
- `lean/SsspFlow/GHatPhase.lean`: the combinatorics of property (6). Two copies on E_R edges are joined by E_R edges
  exactly when they lie on the path of one piece (`RData.er_comp_iff`), and by E_R and E_C edges exactly when their
  pieces are joined in the token graph (`RData.erc_comp_iff`), whose components are those of the split
  (`RData.tg_comp_iff`). So the global phase finds the paths of the pieces and, with Lemma N, the annuli. Every copy on
  the path of a piece is a copy of an end of a dart of the piece (`RData.owner_end`), so the leader copy belongs to a
  vertex of the piece. For Rule M, the parent of the other token of a pair is the other token of the parent pair
  (`RData.parent_partner`), so arcs of the token graph map to arcs of the level before (`RData.parent_tg`) and a
  component of a level lies in one component of the level before (`RData.parent_comp`): the second part of Claim 3. On
  a run the incisions grow with the level and the cut corners stay fixed (`CutPath.Run.inc_mono`,
  `CutPath.Run.cut_eq`), so this holds for every two consecutive levels (`CutPath.Run.parent_comp`).
- `lean/SsspFlow/GHatSplit.lean`: Lemma N in the split model, which cuts the doubled dual at the digon corners of the
  incised darts and at the cut corners (`RData.dualSplit`). Two tokens lie in one piece exactly when their darts lie
  at one vertex of the split (`RData.piece_eq_iff`), so the pieces are the vertices of the split
  (`RData.vertexEquiv`). The token at the reverse of a dart is the partner of the token at the dart
  (`RData.tokOf_rev`), so the pairs are the edges of the split (`RData.head_tokDart`), and for weights that agree on
  the two darts of an edge the distances of the token graph are those of the split (`RData.ddist_eq`). Every set of
  corners that holds both digon corners of each of its edges is the set of corners of some data
  (`RData.Γ_ofCorners`), and further corners out of the reach of a vertex do not change the distances from it
  (`RotSystem.walkDist_split_split`). Hence the length $\lambda_t$ of a live annulus is the distance between the
  pieces at its corners $\kappa_0(t)$ and $\kappa_1(t)$ in the token graph of its own corners
  (`RData.ddist_live_ofCorners`). For any data whose further corners lie out of the reach of the annulus, it is that
  distance in the token graph and, below $M$, the distance in the repaired graph between copies on the paths of the
  two pieces (`RData.ddist_live`, `RData.gdist_live`).
- `lean/SsspFlow/Annuli.lean`: Lemma N for a whole level. The root of a run of the recursion is the annulus of level
  1, and the annuli at depth $\ell$ are those of level $\ell + 1$ (`CutPath.Run.nodes`). The digon corners of the
  steps of all annuli above them, also of the annuli whose sides are not called, are the incisions of the levels
  before (`CutPath.Run.steps`). Every annulus and every incision below a side of a step lie in the component of that
  side in the cut along the step (`CutPath.Run.inv`), and the two sides lie in different components
  (`Live.not_gcomp_sides`). So the corners of an annulus of a level are corners of the level
  (`CutPath.Run.subset_level`), the other corners of the level lie out of its reach (`CutPath.Run.unreach_level`),
  and from the annulus the walks in the split at all the corners of the level are those in the split at its own
  corners (`CutPath.Run.isWalk_level_iff`): every annulus of a level is a component of the token graph of the level.
  Hence $\lambda_t$ of an annulus of a level is the distance between its two pieces in the token graph of the whole
  level and, below $M$, in its repaired graph (`CutPath.Run.ddist_level`, `CutPath.Run.gdist_level`).
- `lean/SsspFlow/TheoremD.lean`: correctness of Theorem D, assuming the classical duality of planar minimum cuts and
  shortest paths in the cut along a shortest dual path ([21], [22]), stated as the
  proposition `CutDuality`. The capacity of a cut and the minimum st-cut are defined on the network itself
  (`cutVal`, `cutVals`), and a minimum st-cut exists for $s \neq t$ (`exists_isLeast_cutVals`). For $K$ larger than
  the number of darts, a minimum cut $v$ for the lengths $K\cdot c+1$ gives the minimum cut $\lfloor v/K \rfloor$ for
  the capacities $c$ (`isLeast_scale`). `theoremD_correct`: if the dual map is planar and connected, the capacities
  agree on the two darts of an edge and the path is shortest for $K\cdot c+1$, a run of the recursion on the cut
  exists, and for every run the least computed length $v$ gives the minimum st-cut $\lfloor v/K \rfloor$ for $c$.
- `lean/SsspFlow/Arborescence.lean`: the arithmetic of the contraction and the halving count of `notes/DMST.md`.
- `lean/SsspFlow/NegScaling.lean`: the arithmetic of the scaling, the alternation, the short paths in a cluster and the arc inequality of `notes/NEGATIVE.md`.
  - `Setup.negCycle_iff`, `Setup.walks` and `Setup.lemmaD` prove it for any graph with the
    face-cycle, dual-dart and star structure of $\hat G$; parallel arcs and loops are allowed.
  - `rotSetup` builds $\hat G$ from a combinatorial map, `rot_pair` shows that both arcs of an
    edge join the same two corners, and `rot_lemmaD` is Lemma D for that graph.
  - Planarity is never used, so the weighting works on any surface.
- `lean/SsspFlow/Tools.lean`: tools of the repair of [1], with walks in multidigraphs and
  "for every walk on one side there is a walk on the other side at most $\lambda$ times as
  long" as the form of $\mathrm{dist}\le\lambda\cdot\mathrm{dist}$.
  - `glue`: the combinatorial core of Lemma R1 (gluing keeps terminal approximation). A walk
    between terminal images cuts into segments of one piece with no terminal image inside
    (`decomp`). The quotient construction is not formalized; its properties are hypotheses.
  - `rounding`: Lemma R6 (capping and rounding up to multiples of $\eta$ costs at most a factor
    $1+\varepsilon$ when $\eta\cdot|V|\le\varepsilon$ and distances are at least 1), with
    `rnd_bounds` for the new weights.
  - `level_step`: the factor $(1+\varepsilon')^3$ per level of Lemma 15′.
  - `params`: $(1+\varepsilon/(2(3H+1)))^{3H+1}\le 1+\varepsilon$ for $\varepsilon\in[0,1]$.
- `lean/SsspFlow/Labels.lean`, theorems `SsspFlow.labelOut` and `SsspFlow.labelIn`: one level
  of Lemma 16′ in both directions, for induced bags (distances inside vertex sets). The
  separation property of the child bags enters as a closure hypothesis on arcs. The region
  form of Lemma 16′ is not formalized.
- `lean/SsspFlow/Boost.lean`, theorem `SsspFlow.Boost.Run.exact`: the discretized boosting of
  [3] with base $\ell_i+\eta$, for a run of $J$ iterations. Lengths stay nonnegative
  (`Run.len_nonneg`), every vertex contracts by a factor $1-1/\alpha$ up to an additive
  $(n-1)\eta$, and the final rounding is exact once the stated bounds hold. `c1_negative` is the
  one-arc instance where base $\ell_i$ gives $-\eta$.

- `lean/SsspFlow/LemmaVRegion.lean`, theorem `SsspFlow.RHierarchy.lemmaV`: Lemma V for region
  bags. Bags carry arc sets, and an arc of a bag between two non-hubs lies in a common child.
- `lean/SsspFlow/LemmaVChain.lean`, theorem `SsspFlow.RHierarchy.lemmaV_chain`: Lemma V in the
  form that fits the labels of [1, Def. 4]. A vertex has estimates only along its chain of bags,
  which stops at the first bag where it is a hub, and each estimate need only lie between the
  distance in G and (1+ε) times the distance in the bag.

- `lean/FourColor/`: the hypermap theory behind the Four Colour Theorem, in the Lean 4 port
  [FourColorTheorem-Lean4](https://github.com/RBarish-UTokyo/FourColorTheorem-Lean4) of the Coq
  development, vendored under its Apache-2.0 licence with its notices; the upstream commit is
  recorded in `lean/FourColor/PORTING.md`, and no file was changed. It provides combinatorial
  maps with their genus, planarity as genus zero, the equivalence of planarity with a contour
  property (`planar_iff_jordan`), cutting a planar map along a ring into two planar maps
  (`Snip`), gluing two maps along a border with additive genus (`Sew`, `Patch`), and dart
  deletion (`Walkup`). It builds unchanged on the pinned toolchain, and
  `lean/FourColor/axioms.txt` lists the axioms of its main results. It is the foundation for
  the planarity statements.
- `lean/SsspFlow/PlanarMap.lean`: the bridge from graphs with a rotation system to those maps.
  `RotSystem` has darts, a reversal and a rotation, `toHypermap` is its plain hypermap, and
  `Planar` means genus zero. `euler` is $V+F=E+2$ for connected planar systems and
  `planar_iff_euler` is the converse. `ofMap` and `toSetup` relate this to the map of
  `LemmaD.lean`.
  - For a simple cycle, `inside` and `outside` are the two sides, read off the cut of the dual
    map. Every dart off the cycle lies on exactly one side (`exactly_one_side`), and both darts
    of an edge off the cycle lie on the same side (`edge_exactly_one_side`).
  - On a planar system, a walk from one side to the other passes through a vertex of the cycle
    (`isWalk_meets_cycle`). Each side is a planar map (`insideMap_planar`, `outsideMap_planar`),
    and reversing the cycle swaps the sides (`mem_outside_reverseCycle_iff`).
  - `triangle` is an instance with a dart on each side, so these statements are not vacuous.
  - Not here: that a side is connected, which side is bounded, and any embedding in the plane.
- `lean/SsspFlow/Splice.lean`: splitting a rotation system at a set of corners, with no drawing.
  `firstReturn f S` is the first return of a permutation to a set. `split` closes the rotation
  at the corners of $\Gamma$, and `skeleton` is the hypermap on $\Gamma$ of the first returns of
  rotation and face. $\psi$ (`psi`) is their product.
  - `genus_split` is the identity
    $g(G)+C(P)+C(\mathrm{skeleton})=g(P)+g(\mathrm{skeleton})+C(G)+\mathrm{orb}(\psi)$, with $P$ the
    split system, $g$ the genus and $C$ the number of components.
  - The components of $P$ are the tiles of Lemma 14′ (`gcomp_split_iff`). For a planar connected
    system and a nonempty connected $\Gamma$, $P$ is planar with exactly one $\psi$-orbit per tile
    (`split_planar`). This is (T3) in combinatorial form.
  - `glue_planar` and `replace_planar` replace the tiles by planar maps with the same ports in the
    same cyclic order and keep planarity. This is Lemma R3 in combinatorial form.
  - `triangle_split_two_tiles` and `triangle_replace` are instances. The instance of the
    replacement has a map replacing itself.
- `lean/SsspFlow/Chord.lean`: adding and removing edges of a rotation system, with no drawing.
  - The transposition lemma: multiplying a permutation by a transposition splits an orbit or
    merges two (`orb_mul_swap_of_fconnect`, `orb_mul_swap_of_not_fconnect`).
  - A chord between two corners of one face keeps the genus and splits the face
    (`genus_chord_of_fconnect`, `fconnect_chord_cases`). A chord between two faces of one
    component raises the genus by one (`genus_chord_of_not_fconnect`).
  - A restriction to a set of darts does not raise the genus (`genus_restrict_le`). Two corners of
    one face of a planar map lie in one face of every connected restriction
    (`fconnect_predIn_of_fconnect`). Two chords between the same two corners in the same order at
    both ends raise the genus (`genus_twisted`).
- `lean/SsspFlow/Crossing.lean`: (G4) for rotation systems. `DiskDrawn` says that darts name corners
  of one face of a connected planar map, in a given cyclic order. Walks between crossing pairs of
  corners share a vertex (`DiskDrawn.crossing`), so distances over walks with dart lengths in
  $[0,\infty]$ satisfy the Monge condition (`DiskDrawn.monge`). `triangle_diskDrawn` is an instance.
- `lean/Cslib/`: the CONGEST model of a fork of CSLib, vendored unchanged under its Apache-2.0
  licence with its notices. The source and the commit are in `lean/Cslib/PORTING.md`.
- `lean/SsspFlow/Congest.lean`: algorithms in this model, with exactly $B$ bits per edge, direction
  and round, and fixed before the network.
  - `run_widen`, `run_seq_lt` and `run_seq` give the semantics of wider messages and of sequential
    composition. `run_keep`, `run_stopAt` and `run_iter` do the same for keeping an input, for
    stopping after a number of rounds and for repeating an algorithm on data that change between
    the repetitions. `run_exch` is one round in which every node tells its neighbours a number of
    at most $B$ bits. `run_congr` says that after $t$ rounds a node depends only on the inputs
    within $t$ hops.
  - `Net` is a graph with rotation lists, and `toRot` is its rotation system on the darts of the
    graph (`tail_eq_iff`, `toRot_connected`). `triNet_planar` is an instance.
- `lean/SsspFlow/LabelHypothesis.lean`: statements in this model.
  - `LabelHypothesis`, for one algorithm per $n,e,D$ on all planar networks with these parameters and
    with arc lengths at most $(n+2)^K$, with the word sizes and the rounds as part of the statement.
    `labelHypothesis_of_boxes` in `lean/SsspFlow/LabelFinal.lean` proves it from the propositions below, and
    `labelHypothesis_of_cited` in `lean/SsspFlow/AggFinal.lean` without `AggBox`.
  - `lemmaV_chain₂` and `LabelWitness.query_bound` prove Lemma V for the values that the labels
    hold. `labelsOK_oneBag` and `labelsOK_triNet` show that correct labels exist on small networks.
  - The results of the literature that are used are stated as propositions (`RealizationBox`,
    `DistanceLabelBox`, `FaceIdBox`, `EmbeddingBox`, `AggBox`, `SmoothingBox`). `aggBox` in
    `lean/SsspFlow/AggProof.lean` proves `AggBox`, and `smoothingBox` in `lean/SsspFlow/SmoothRun.lean` proves
    `SmoothingBox`; the others are not proved.
    `NegReduction` is a reduction for negative weights, and `negReduction_of_ldd` in
    `lean/SsspFlow/NegFinal.lean` proves it from the decomposition `LDDBox` of
    `lean/SsspFlow/NegBox.lean`. `ExactSsspBound`, `NegSsspBound` and `MaxFlowBound` are the round bounds of
    Theorems A, B and C as definitions, and this file asserts none of them.
    `not_negSsspBound_zero` and `not_maxFlowBound_zero` show that the two randomized definitions
    fail with no rounds.
- `lean/SsspFlow/LabelOracle.lean`, theorem `approxOracle`: `LabelHypothesis` and `AggBox` give a
  $(1+1/e)$-approximate oracle for shortest paths from a virtual source, with polynomial lengths and
  offsets, in $\tilde O(De)$ rounds and with words of polylogarithmically many bits. One aggregation
  over the subgraphs of all bags computes the query of Lemma V (`labelAnswer_eq`). Unreachable nodes
  are found by replacing $\infty$ with a large number (`capped_bounds`).
- `lean/SsspFlow/ExactSssp.lean`, theorem `exactSsspBound`: `LabelHypothesis`, `AggBox` and
  `SmoothingBox` give `ExactSsspBound`, that is exact distances and the parents of a shortest-path
  forest in $\tilde O(D)$ rounds, with words of polylogarithmically many bits, by one fixed algorithm
  per $n$ and $D$ on all planar networks of diameter at most $D$. Lengths and offsets are in
  $\{0,\dots,(n+2)^K,\infty\}$.
  - Lengths are scaled to $(n+1)\ell+1$ (`walk_scale`, `scale_top`, `scale_finite`). This gives a
    strict decrease along parents (`exactSpec_of_ndsrc`).
  - The iterations stay in natural numbers (`itSeq`). `it_main` applies `Boost.Run.exact` to them,
    and `it_bounds` shows that their lengths stay polynomial.
  - `exactAlg` is the algorithm. `itRel_iter` shows that the nodes hold these iterations, and
    `exactAlg_ok` is its correctness.
- `lean/SsspFlow/PlanarDual.lean`, theorem `RotSystem.exists_face_potential`: an integer circulation
  on a connected planar rotation system is the difference of an integer potential on the faces. The
  proof is a count of dimensions from the formula $V+F=E+2$.
- `lean/SsspFlow/NetPad.lean`: `planar_of_count` says that a connected rotation system with enough
  vertices and faces is planar, because the genus is not negative. `padNet` hangs identifiers as
  pendant nodes at chosen nodes, in an order given with the identifiers (`PadMap.order`). It stays planar
  (`padNet_planar`), and its diameter grows by at most two (`padNet_diam`).
- `lean/SsspFlow/DualNet.lean`, `Net.xNet`: a version of $\hat G$ in which all edges of crowns and
  rings are subdivided, so that it is a simple graph for every network. It is planar (`xNet_planar`)
  and has diameter at most $5D+4$ (`xNet_diam`).
- `lean/SsspFlow/DualFlow.lean`: `dualNet` is this network with all remaining identifiers as pendant
  nodes, so that a network with $n$ nodes always has a dual network on $5n^2$ identifiers. Its diameter
  is at most $5D+6$.
  - `no_negCycle_of_flow`: for a unit flow $\sigma$, a flow of value $\beta$ rules out negative cycles
    for the costs $c-\beta\sigma$. `isFlow_of_spec`: distances for these costs give a flow of value
    $\beta$. `hasNegCycle_mono`: a negative cycle stays negative for all larger values.
  - `negIn_eq`, `dual_adj_cross`: a node computes the inputs of the identifiers that it hosts, and the
    edges between different hosts follow the edges of the network, at most two per edge and direction.
- `lean/SsspFlow/Flood.lean`, theorem `unitFlow_of_floods`: two floods of $D$ rounds with messages of
  one bit give a unit of flow from $s$ to $t$.
- `lean/SsspFlow/HostSim.lean`, theorem `Algorithm.run_simulate`: under these conditions the hosts run
  an algorithm on identifiers in the same number of rounds, with messages of twice the width.
- `lean/SsspFlow/HostSimK.lean`, theorem `Algorithm.run_simulateView`: the same with at most $k$ edges between two
  hosts in each direction and messages of $k$ times the width. The slots need not be fixed in advance: each host
  knows the edges at its own identifiers, and both ends of an edge list the pairs between them in the same order.
- `lean/SsspFlow/MaxFlow.lean`: the algorithm and the round count of Theorem C.
  - `negSsspBound_of_reduction`: `ExactSsspBound` and `NegReduction τ` give `NegSsspBound τ`. So,
    given `ExactSsspBound`, `NegReduction` fails with the factor $0$ (`not_negReduction_zero`).
  - `maxFlowBound_of_neg`: `NegSsspBound τ` gives `MaxFlowBound τ'` if $\tau(5n^2+2)$ is at most a
    constant times $\tau'(n+2)$. The nodes find a unit of flow, then run a binary search on the value,
    and each test simulates the algorithm for negative weights on the dual network. `search_inv` is
    the invariant of the search and `whole_correct` its correctness. `maxFlow_count` bounds the
    fraction of bad strings, with the same strings in all tests and a union bound over the values.
  - `negFlow_subpoly`, `negFlow_polylog`: `LabelHypothesis`, `AggBox`, `SmoothingBox` and
    `NegReduction τ` give `NegSsspBound τ` and the matching `MaxFlowBound`. With `tauSubpoly C` these
    are $D\cdot n^{o(1)}$ rounds, and with `tauPolylog c` they are $\tilde O(D)$ rounds.
- `lean/SsspFlow/Tour.lean`: tours of a spanning forest in a planar map, by the formula $V+F=E+2$ alone.
  `fconnect_tour_iff`: the cycles of the tour are the components. `walk_strict`: the corners of a face
  appear on the tour in the order of the face. `exists_balanced`: a cycle with at least four forest darts
  has two corners of one face, such that each arc between them holds about three quarters of these darts
  or less.
- `lean/SsspFlow/Disks.lean`: disks cut along walks up a spanning tree of the map with doubled edges.
  `IsLevel.spanForest`: the marked tree edges at the vertices without a corner in a level are a spanning
  forest of the cone over the level. `side_gcomp`: a larger level with two corners of one face of the
  cone keeps each of its disks on one side of the tour. `npOf_balance`: so a balanced cut leaves about
  three quarters of the forest darts or less in each disk. `IsLevel.next`: corners with their walks up
  the tree form a level again.
- `lean/SsspFlow/Bags.lean`: the bags of a sequence of levels: corners, diameter, the logarithmic depth and the hierarchy they form, with short chains, few hubs and low congestion.
- `lean/SsspFlow/Glue.lean`: distances after gluing the corners of a split. `walkDist_glue`: they are the least
  total weights of walks over the distances before gluing, with free moves on the glued corners.
  `split_faceDrawn`: a cycle of corners lies on one face of the split, in its order.
- `lean/SsspFlow/Compose.lean`: disks composed along their corners. `hubDist_monge`: the composed distances
  satisfy the crossing inequalities on each cycle of a smaller set of corners.
- `lean/SsspFlow/Emulator.lean`: `exists_bagOK`: a metric with the crossing inequalities gives short labels
  with precise values, from `RealizationBox` and `DistanceLabelBox`, with no growth of numbers.
- `lean/SsspFlow/Levels.lean`: values along a sequence of levels. `levelMetric_step`: values at a larger set of
  corners give values at a smaller one by one call per bag, with the factor `((U + 4) / U) ^ 2`.
  `levelMetric_seq`: so errors add up over all levels instead of multiplying large factors.
- `lean/SsspFlow/Hubs.lean`: `est_bounds`: values between the hubs of each bag give estimates from all
  vertices of a bag to its hubs, with no growth over the levels. `bagDist_lo`, `bagDist_hi`: the values
  between hubs from values on the corners, against walks in the graph and along the arcs of a bag.
- `lean/SsspFlow/Witness.lean`: `bagVal_lo`, `bagVal_hi`: these bounds for every bag of a decomposition, with
  values along its levels from the top.
- `lean/SsspFlow/Tau.lean`: `fconnect_tau`: one tour through all darts of the doubled map. `pos_psi_le`: the
  next corner of a bag on its boundary is the next one on this tour. `fconnect_cone_face`: two darts of a bag
  on one face of the map lie on one face of the bag.
- `lean/SsspFlow/Potential.lean`: `pot_spec`, `cyc_spec`: masses on the tour of a bag are differences of
  numbers of the global tour, plus an offset per corner.
- `lean/SsspFlow/Select.lean`: a rule for the cut of each bag in terms of these masses, and
  `decomp_levelSeq`: the levels of this rule form a decomposition.
- `lean/SsspFlow/Sector.lean`: `Decomp.dart_span`: any two darts of a bag are joined by a short walk of darts
  inside the bag.
- `lean/SsspFlow/TourNums.lean`: `phi_eq`, `pos_tau_eq`: the numbers on the first tour and on the tour through
  all darts as sums over the blocks of the tree.
- `lean/SsspFlow/Tables.lean`: `massT_eq`, `cycT_eq`: masses on the tour of a bag from a table of its corners.
- `lean/SsspFlow/LevelT.lean`: `candA_eq`, `candY_eq`, `mem_next_iff`: the cut rule and the next level from this
  table and the numbers of a dart.
- `lean/SsspFlow/Machine.lean`: a machine with phases on top of the message model. `mem_relax`, `mem_agg`,
  `run_mach`: each phase leaves its result in a memory that later phases keep.
- `lean/SsspFlow/NetTree.lean`: `treeN`: the tree of shortest walks of a network. `fid_iff`, `sec_iff`: faces and
  sectors in terms of what a node sees.
- `lean/SsspFlow/NetPasses.lean`: `dep_spec`, `up_spec`, `down_spec`: relaxations for the depth and the sums over
  the tree. `constAt_of_run`: after these phases a node knows the numbers of its darts and of their reverses.
- `lean/SsspFlow/NetAgg.lean`: `valid_of`, `AggDone.tab`: calls of the aggregation primitive in which each dart
  of a node holds a name and pairs. The hypotheses of the primitive follow from the shape of the bags, and the
  answers form a table.
- `lean/SsspFlow/NetFlood.lean`: `flood_spec`: after a number of rounds given by the diameter of the bags, each
  dart holds the least code of a corner of its bag.
- `lean/SsspFlow/LevelTab.lean`: the answers of the calls of one level. `isA_iff`, `isY_iff`, `mem_next`: a dart
  reads from them whether it lies on the cut of its bag and whether it belongs to the next level.
- `lean/SsspFlow/NetLevels.lean`: `corL_eq`, `levels_of_run`: what a node reads from its memory, and that a run of
  the phases of the levels gives each node its corners at all levels.
- `lean/SsspFlow/EdgeBound.lean`: `card_le_of_planar`: a set of darts closed under reversal in a simple planar map
  has at most eight darts per vertex it touches.
- `lean/SsspFlow/ValueTab.lean`: `vT_ok`, `label_read`, `bagVal_read`: one aggregation call per bag gathers the
  records of its corners in a table. The labels of the ports and the values between the hubs of the bag are
  functions of this table alone, and `vals_metric`, `label_bounds`, `vItems_lt` give their accuracy and their size.
- `lean/SsspFlow/NetValues.lean`: `vItsL_eq`, `values_of_run`, `leaf_card`: what a node submits in the value calls,
  and that a run of these calls gives each node the tables of its bags.
- `lean/SsspFlow/Output.lean`: `labelsOK_of_mem`: correct tables in the memory of the nodes give correct labels, with the
  hierarchy of the bags as the witness.
- `lean/SsspFlow/LabelProof.lean`: `labels_memL`: the memory of a node after all phases is correct, so it gives correct
  labels. `finalAlg`, `run_finalAlg`: the algorithm of the nodes and what it holds after its rounds.
- `lean/SsspFlow/LabelFinal.lean`: the end of the proof.
  - `labelHypothesis_of_boxes`: `RealizationBox`, `DistanceLabelBox`, `FaceIdBox` and `AggBox` give `LabelHypothesis`.
  - `exp_bounds`, `bits_le`: all numbers of a run are polynomial in $n$, so they fit into polylogarithmically many bits,
    independently of $D$. `labelRounds_le`: the number of rounds. `labelsOK_tiny`: networks with at most one node.
  - `exactSssp_of_boxes`: with `SmoothingBox`, this gives `ExactSsspBound`. `negFlow_polylog_of_boxes`,
    `negFlow_subpoly_of_boxes`: with `NegReduction τ`, this gives `NegSsspBound τ` and the matching `MaxFlowBound`.
- `lean/SsspFlow/NegWalk.lean`: walks with integer weights. `Walk.exists_nodup_le`: if closed walks have nonnegative
  weight, a walk can be replaced by one without repeated vertices that is not heavier and not longer.
- `lean/SsspFlow/NegBox.lean`: `LDDBox`, the low-diameter decomposition of [6, Lemma 4, Cor. 27] with the order of its
  clusters of [6, Lemma 5, Prop. 32, Cor. 33], in the form of Lemma 2 of `notes/NEGATIVE.md` with the repairs of its
  Section 8.
- `lean/SsspFlow/NegAlt.lean`: Lemma 1 of `notes/NEGATIVE.md`. `altD_walk`, `altD_le`: after $t$ steps of oracle calls
  and relaxations over the negative arcs, each value is the weight of a walk and at most the weight of every walk with
  at most $t$ negative arcs.
- `lean/SsspFlow/NegLevels.lean`: the restricted problem of Proposition 4. `short_walk` is Lemma 3. `Good.levPhi_last`:
  if the decompositions behave, the potential of the last level makes all kept arcs nonnegative.
- `lean/SsspFlow/NegScale.lean`: Lemma 5 and Section 5. `scale_all`, `Bseq_nPhase`: the reduced weights stay at least
  $-B$, and the bound reaches $0$ after $O(\log nW)$ phases. `exists_bad_arc`, `negSpec_of`: a negative closed walk
  leaves an arc of negative reduced weight for every potential, and without one the least reduced walks give the
  distances.
- `lean/SsspFlow/NegProb.lean`: the failure probability of Proposition 4. `phaseBad_count`, `anyBad_count`: bad phases
  are rare, also when each phase depends on the strings of the phases before it.
- `lean/SsspFlow/NegCode.lean`, `lean/SsspFlow/NegNet.lean`, `lean/SsspFlow/NegRun.lean`: the program of a node and its
  run on the machine of `Machine.lean`. `negSpec_run`: if no phase is bad, the outputs of the nodes are correct.
- `lean/SsspFlow/NegFinal.lean`: `negReduction_of_ldd`: `LDDBox` gives `NegReduction (tauPolylog c)` for some $c$.
  `negP_nums`, `negP_kp`: all numbers are polynomial in $n$, and the number of steps is $O(\log^{11} n)$.
  `negFlow_of_ldd`: with the propositions of `LabelFinal.lean`, this gives `NegSsspBound` and `MaxFlowBound` with a
  polylogarithmic factor.
- `lean/SsspFlow/AggMux.lean`: `TAlg.run_bits`: an algorithm with typed messages runs with messages of $B$ bits when
  the codes of its messages stay below $2^B$. `run_mux`: blocks of $c$ rounds, in which round $r$ of a block serves the
  $r$-th subgraph of each edge in sorted order, so after $ct$ rounds a node holds the state after $t$ rounds of the run
  on each subgraph.
- `lean/SsspFlow/AggMerge.lean`: a pipelined convergecast of minima per key. A node sends the least key above those it
  has sent once all its children have passed it, with the least value seen, and an end mark when no key is left.
  `streamInv`: each key is sent with its least value over the subtree. `timing`, `stream_full`: a node of height $h$
  has sent the key of rank $r$ by round $h+r+1$, and all keys and the end mark by round $h+k+1$ for $k$ keys in its
  subtree. `ans_eq` reads the minima from a full stream, and `mergeT_rec`, `mergeT_code` give the algorithm and the size
  of its messages.
- `lean/SsspFlow/AggProof.lean`: one subgraph in five phases of $5(s+k+1)$ rounds in all: a leader by flooding the
  least identifier (`ldr_spec`), a breadth-first tree, an exchange of parents, the convergecast to the leader and a
  broadcast of its answer (`perName_run`, `perName_ans`). `aggBox` proves `AggBox` with the constant $5$.
- `lean/SsspFlow/AggFinal.lean`: `labelHypothesis_of_cited` is the Label Hypothesis of `LabelFinal.lean` without
  `AggBox`.
- `lean/SsspFlow/SmoothStep.lean`: the smoothing of [3] in natural numbers. `Smooth` bounds the estimates along walks,
  with a slope and a slack. `step_smooth`: one step with two calls on level graphs, with shifts $0$ and $h$, raises the
  slope by one and halves the slack. `iter_inv`: after $t$ steps the estimates have slope $5t$ and slack $t$, and they
  stay at least $4t$ times the distance. `out_lo`, `out_arc`, `out_off`: the rounded estimates satisfy the three bounds
  of `SmoothingBox`.
- `lean/SsspFlow/SmoothRun.lean`: the smoothing on the machine of `Machine.lean`. `dsrc_eq_ndsrc`: the distance from
  the virtual source in natural numbers. `dG_inv`: the estimates from the answers of the oracle. `dM_eq`: the memory
  of each node holds them. `smoothingBox` proves `SmoothingBox` with $C = 30K + 104$ and $c = 1$.
  `exactSssp_of_cited`, `negFlow_polylog_of_cited`, `negFlow_subpoly_of_cited` and `negFlow_of_cited` are the end
  results of `LabelFinal.lean` and `NegFinal.lean` without `AggBox` and `SmoothingBox`.

Not formalized: the proofs of the cited propositions other than `AggBox` and `SmoothingBox`, among them `LDDBox`, the minimum cut of
Theorem C, Theorem C′, the construction of the tiles and the rest of Lemma 14′, and Lemmas R5 and R7. Of Theorem D,
Lemmas S1 and S2 and the facts of Lemma O that the recursion uses are formalized, in a split model of the incisions on
the cut of a planar map along a shortest path between corners of two different faces: a run of the recursion on the
cut exists, every length it computes is a length $\lambda_t$, and the least of them is the least $\lambda_t$.
Of Lemma R, Definition R, its properties (1), (2) and (5), the hop bound of (4), the refinement in (6) and the
distances on the repaired graph are formalized, for any set of cut corners with modes and any host of the unincised
pairs. Lemma N is formalized in the split model: the pieces and pairs are the vertices and edges of the split, every
annulus of a level is a component of the token graph of the level, and its lengths $\lambda_t$ are distances in that
token graph and, below $M$, in the repaired graph. The planarity (3) is formalized for every level of a run, for any modes
and hosts, and so is the count of copies in (4). The combinatorics of (6) is formalized, and so is the simulation in (4) for nodes that know the edges of the repaired graph at their own copies, and the repaired graph of every level as a planar network of diameter $O(D)$ whose distances between copies are the distances in $\hat G_\ell$, and, assuming the Exact SSSP bound, the computation of these distances and of the components of $\hat G_\ell[E_R]$ and $\hat G_\ell[E_R \cup E_C]$ by the nodes in $O(\log^c n \cdot D)$ rounds. The round count of the whole recursion is formalized as a cost model over the levels, assuming part-wise aggregation (`PartAggBox`). The rotation lists and the inputs of the shortest paths of the network of a level at every identifier are formalized as functions of the data of its host and the records and values $\lambda$ of the darts into it. The distances of a level are formalized as one algorithm of the message model from these local inputs, assuming the Exact SSSP bound (`RData.levelSssp_local`), and so are the components (`RData.levelConn_local`). Rule M is formalized as a local rule: the copy it reads is a copy of the node itself, and tokens of one component read one label of the level before (`RData.ruleM_lab`). The other distributed steps of a level and one algorithm of the message model for the whole recursion are not formalized. The reduction of the minimum st-cut to the least computed length is
formalized, assuming the classical cut duality (`CutDuality`).

## Numerical checks (`sim/`)

Requires Python 3 with `numpy`, `scipy` and `networkx`. Run each script from its own directory.
The arXiv version of the paper (2611.02256v1) refers to the tree at the tag `arxiv-v1`, where some
of these directories have older names.
These scripts test finite families and the sequential meaning of the statements. They do not
test round counts.

- `sim/check.py`: Lemma V, Lemma D, Theorem C and Theorem C′ on random planar instances, in exact
  arithmetic. `python3 check.py 40 1` runs 40 instances with seed 1.
- `sim/tiles/tiles2.py`: the tile construction of Lemma 14′ as written, with child bags shaped
  as in [8]. It checks every claim of §3 per level, the Monge condition on every tile, and the
  planarity of every gluing. Run as `python3 tiles2.py <seeds> [virtual|neg|pend3|pend6]`.
  `tiles.py` is the first version. The `run*.txt` files hold the outputs listed in
  `notes/LEMMA15.md` §3.7: about 2.7 million Monge checks and no failure, while the negative
  controls fail as they should.
- `sim/tiles_check/`: a second check of §3. `walk_check.py` rebuilds the boundary
  order of every tile from port records alone, as the distributed algorithm would, and
  `pendant.py` builds graphs with pendant leaves in every corner, on which the reading with one
  child per outside component fails.
- `sim/tiles_early/`: tests of an earlier form of §3. `run.py` is the driver, `engine.py` the
  construction and its checks, and `s7_rebuild.py` rebuilds the three configurations above. `g1_inconsistency.py` shows that
  one child per outside component is incompatible with the decomposition's properties on
  stars. `g1_grouped.py` repeats that search with the grouping of [8] and finds balanced
  children.
- `sim/lemma14prime/`: tests of Lemma 14′ and of the parts of Lemmas 15′ and 16′ that use it, with
  negative controls. `p6.py` builds the family on which Property 6 fails
  (`python3 -I p6.py 100 u 8 nopost`), and `lp46_demo.py` a step of [8] that adds more than
  one tree component. `sweep.py` and `run.py` drive the sweeps; `logs/` holds their output.
- `sim/s9/`: the region bags of §9. `engine_r.py` is the region form of the engine,
  `post_r.py` its Lemma 15′ and 16′ checks, `rsweep.py` the driver, `big.py` larger
  instances, and `neg.py` the negative controls. 2,450 correctness instances had no failure,
  and every edge lay in at most two region graphs per depth. With `NOSPLIT=1` the engine never
  splits a separator vertex; 1,400 instances of that form also had no failure. Another
  1,750 instances checked Lemmas B2 to B4 with exact hole counts at 86,905
  children without a violation (`logs/e_*.txt`); `logs/` holds all output. `b5.py` runs
  Lemma B5 and checks each separator against an independent side count (4,000 instances, n
  up to 1,842, no failure; `python3 -I b5.py START END`).
- `sim/lemmaB5/`: further tests of Lemma B5. `mine.py` is an independent
  implementation with its own side count, and `harness.py` compares it with `b5.py`.
  `exh.py` and `exh_trees.py` enumerate all instances for small n, `rand.py`, `fams.py` and
  `geo_cmp.py` run larger ones, `hill.py` climbs towards the step bounds, and `negctl.py`
  runs the negative controls.
- `sim/thmD/`: simulation of Theorem D. `thmD.py` runs the recursion of [18, Alg. 3],
  driven only by the exact trees of Theorem D, on the literal and the repaired $\hat G_\ell$,
  and checks every distance, tree and final cut against networkx. `minimize.py` shrinks
  failures, `planar_check.py` tests planarity and diameter, `endpoints.py` reruns the three
  endpoint cases of Remark 3.3 on their smallest graphs and counts how often the mirrored copy is
  needed, and `lane1.sh`/`lane2.sh` give the runs. `logs/summary.txt` sums them up. `repair/` checks Lemma R: `formal_ghat.py` builds
  the repaired graph from its written definition, and `test_repair.py` and `witness.py`
  compare it with `thmD.py` and check its properties; `test_mono.py`, `witness_mono.py` and
  `run_mono.sh` rerun them with the monotone I_ℓ and also check Lemma N.
  `testR/` tests Lemma R and Lemma N with code written independently of
  `thmD.py`: `emb.py` enumerates maps, `defr.py` builds Definition R, `abstract18.py` models
  the incisions of [18], `level1.py`, `planar_sweep.py`, `deep.py` and `deep2.py` run the
  checks, `search_e2e.py` and `minimize_e2e.py` find the recursion defect, and
  `confirm_author.py` reruns it on `thmD.py`. `thmD.py --ends 1` adds the repair of Lemma S and
  checks its interval claim (`c24_interval`), the hull of part (b) (`hull_i12`) and the
  separation fact (`sep_fail`). `fix/` checks the smallest instance and reruns the 25 failing
  instances with and without the repair; `lane_ends.sh`, `lane_c24.sh` and `lane_sep.sh` give
  the sweeps. `lemmaO/` checks every part of Lemma O and of its
  invariant at every incision (`patchO.py` turns `thmD.py` into `thmD_O.py`; `lanes*.sh`):
  342,000 instances, 232,868 incisions, no failed check. `testSO/` tests Lemmas S and O:
  every run on all connected loopless maps with at most 8 edges (with a cap of runs per instance),
  hill-climbing and the saved hits (`logs/summary.txt`). `checkND/` is the script test of the naming of
  sides, the cut read from a path, the reading direction and the number of levels: 12,441,126 runs
  with no failure, every negative control fired (`REPORT.md`).
- `sim/s9_stress/`: stress tests of §9. `engine_r9.py` adds exact hole counts,
  closings through holes, greedy separators that aim at the slack of Lemmas B2 to B4, and
  other global trees; `engine_c9.py` draws closings combinatorially; `fams9.py` adds nine
  families (Delaunay with holes, sparse Delaunay, cacti, wheels of wheels and others). Run
  `python3 -I adv.py CONF A:B fam1,fam2 SCALE`. `tight.py` finds the equality cases.
- `sim/counterexamples/`: the counterexamples to [1, Lemma 14], and checks of the analytic layer:
  gluing (`r1_glue.py`), rounding (`r6_round.py`), the error recursion (`l16.py`), the squaring
  in [1, Thm 2] (`s1_square.py`), and tests of Lemma V and Lemma D
  (`lemmaV.py`, `lemmaD_flow.py`). `rot.py` is a small rotation-system library used by the
  others.
- `sim/monge/monge.py`: an instance that satisfies the Monge constraints of [1] for one linear
  reading of the order but not for the circular one, which is why the notes impose them in all
  rotations.

## Notes (`notes/`)

- `notes/NOTES.md`: the state of the art, Theorems A, B, C, C′ and D, Lemmas V and D, and the
  ratings.
- `notes/GHAT_REPAIR.md`: Lemma R, the repaired auxiliary graph of [18] that Theorem D runs on.
- `notes/RECURSION.md`: Lemma S, the repaired recursion of [18, Alg. 3].
- `notes/LEMMA_O.md`: Lemma O, the sides of one incision, which Lemma S and the exact exchange
  use.
- `notes/LEMMA15.md`: the gaps in [1, Lemmas 14 to 16] and their repair, with Lemma 14′ (§3),
  the analytic layer (§4 to §7), what is settled (§8), and the region bags that repair the
  round count (§9).
- `notes/DISKS.md`: the construction of the labels that is proved in Lean, with disks cut along walks up a
  tree of shortest walks: the cut of a bag, the shape of the bags, the values and the algorithm.

These are working notes. References such as "lty 1762", "adpw 2166" or "adw26 1673" point to
line numbers in plain-text extractions of [1] (arXiv v2), [9] and [18].

## Open questions

- Directed planar global minimum cut is at $\tilde O(D^2)$ [9, Thm 1.5]. It needs the shortest
  cycle of simple darts in the dual. $\hat G$ has cycles of weight 0, so the girth of
  $\hat G$ does not give it.
- Weighted girth of planar digraphs, also at $\tilde O(D^2)$ [19]. If its algorithm uses
  polylogarithmically many exact SSSP calls, Theorem A may improve it; we have not checked.
- Is the component bound of Lemma B1(e) really $\Theta(\log^2 n)$? All runs stayed at
  depth + 1.
- Theorems A, C′ and D are deterministic given an embedding. Are Theorems B and C? That
  needs a deterministic version of [6].
- Can the realization step run in polynomial local time, with a prescribed cyclic order of the
  terminals? [1, Thm 1] claims a polynomial-time construction but promises no order.
- A deterministic maximum st-flow assignment in undirected planar networks in $\tilde O(D)$ from the
  Label Hypothesis alone. Theorem D gives the value and a minimum cut. An undirected network is a
  directed one with two opposite arcs per edge, so `notes/NEGATIVE.md` gives the flow on every edge
  with high probability, and `notes/MAXFLOW.md` gives it deterministically with one extension of the
  labels; [18] asks for the assignment as well.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to search the literature, to
develop and check the proofs, to write the scripts and the Lean formalization, and to draft
the text.

## References

The numbers match those in `notes/`.

1. H. Le, H. Tierno, S. Yang. Planar Embedding of Okamura-Seymour Quasimetrics in Polynomial
   Time with an Application to Distributed SSSP. arXiv:2606.31192 (v2, 2026).
2. N. Cao, J. T. Fineman. Parallel Exact Shortest Paths in Almost Linear Work and Square Root
   Depth. SODA 2023.
3. V. Rozhoň, B. Haeupler, A. Martinsson, C. Grunau, G. Zuzic. Parallel Breadth-First Search
   and Exact Shortest Paths and Stronger Notions for Approximate Distances. STOC 2023,
   arXiv:2210.16351.
4. S. Chechik, D. Mukhtar. Single-source shortest paths in the CONGEST model with improved
   bounds. PODC 2020.
5. N. Cao, J. T. Fineman, K. Russell. Brief announcement: an improved distributed approximate
   SSSP algorithm. PODC 2021.
6. V. Ashvinkumar et al. Parallel, Distributed, and Quantum Exact SSSP with Negative Edge
   Weights. ESA 2024, arXiv:2303.00811.
7. T. de Vos. Minimum Cost Flow in the CONGEST Model. arXiv:2304.01600.
8. J. Li, M. Parter. Planar Diameter via Metric Compression. STOC 2019, arXiv:1912.11491.
9. Y. Abd-Elhaleem, M. Dory, M. Parter, O. Weimann. Distributed Maximum Flow in Planar Graphs.
   PODC 2025, arXiv:2411.11718.
10. Y. Chen, Z. Tan. Paths and Intersections: Characterization of Quasi-metrics in Directed
    Okamura-Seymour Instances. SODA 2025, arXiv:2410.19246.
11. G. L. Miller, J. Naor. Flow in planar graphs with multiple sources and sinks. SIAM J.
    Comput. 24(5), 1995.
12. R. Hassin. Maximum flow in (s,t) planar networks. Inform. Process. Lett. 13(3), 1981.
13. M. Thorup. Compact oracles for reachability and approximate distances in planar digraphs.
    J. ACM 51(6), 2004.
14. M. Ghaffari, M. Parter. Near-Optimal Distributed DFS in Planar Graphs. DISC 2017.
15. M. Ghaffari, B. Haeupler. Distributed Algorithms for Planar Networks I: Planar Embedding.
    PODC 2016.
16. B. Jauregui, P. Montealegre, I. Rapaport. Deterministic Distributed DFS and Other Problems
    via Cycle Separators in Planar Graphs. PODC 2025, arXiv:2504.21620.
17. Y. Abd-Elhaleem, M. Dory, O. Weimann. A Simple Distributed Deterministic Planar Separator.
    SIROCCO 2026, arXiv:2602.22916.
18. Y. Abd-Elhaleem, M. Dory, O. Weimann. Õptimal Distributed Maximum Flow Approximation in
    Undirected Planar Graphs. arXiv:2608.09500, to appear in DISC 2026.
19. M. Parter. Distributed Planar Reachability in Nearly Optimal Time. DISC 2020.
20. M. Ghaffari, B. Haeupler. Low-Congestion Shortcuts for Graphs Excluding Dense Minors.
    arXiv:2008.03091.
21. J. H. Reif. Minimum s-t cut of a planar undirected network in O(n log² n) time. SIAM J.
    Comput. 12(1), 1983.
22. A. Itai, Y. Shiloach. Maximum flow in planar networks. SIAM J. Comput. 8(2), 1979.

## License

Copyright 2026 Sebastian Senge. The code and the documentation in this repository are licensed
under the Apache License 2.0; see `LICENSE`.
