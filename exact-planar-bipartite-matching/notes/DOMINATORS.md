# Dominator trees of planar digraphs in Õ(D) rounds

**Status.** Claim, written 3 Nov 2026. Proofs below, simulation in `sim/dom.py`. Combinatorial core in Lean. No human has checked it. It uses the General Search Theorem of `notes/GENERAL_DFS.md`, itself a claim, through its paths and classes. Importance: solid if it survives. The dominator tree is a basic tool, and we found no bound for it in CONGEST. The proof is elementary, and its step along one path has sequential relatives, see Context.

The model is CONGEST on a connected planar network G with n vertices and hop diameter D, with a known embedding. Õ hides factors polylogarithmic in n. A *digraph on G* has its arcs on edges of G. D is the diameter of the undirected G. Identifiers are distinct.

## 1. Results

Let H be a digraph on G and r a vertex. A vertex v *dominates* y if v ≠ y and every path from r to y passes through v. Two dominators of y appear in the same order on all simple paths from r to y: otherwise a prefix of one path and a suffix of the other avoid one of them. The *immediate dominator* idom(y) of a vertex y ≠ r reached from r is the last dominator of y on such a path. These pointers form the dominator tree.

**Dominator Theorem.** In Õ(D) rounds every vertex y ≠ r reached from r learns the identifier of idom(y).

**Corollary 1 (cut vertices).** Given also a vertex t reached from r, every vertex learns in Õ(D) rounds whether it dominates t, that is, whether it lies on all paths from r to t.

**Corollary 2 (single failures).** In Õ(D) rounds every vertex learns whether it is a strong articulation point of H, and every arc whether it is a strong bridge of H. A *strong articulation point* is a vertex whose removal increases the number of strong components, and a *strong bridge* is such an arc.

**Corollary 3 (no general search).** On a planar DAG the Dominator Theorem and Corollary 1 hold on the passes of `notes/DAG_DFS.md`, with no use of the General Search Theorem and of the identifiers of strong components. If all strong components have at most s vertices, the same passes give Õ(D·s) rounds.

The algorithms are deterministic relative to the tree of bags and the identifiers of strong components of [1, Lemma 3], as in `notes/GENERAL_DFS.md`.

**Context.** The classical sequential algorithm [2] starts from a depth-first search and computes semi-dominators by a bottom-up sweep with path compression, and later algorithms reach linear time or simplify the machinery [3, 8]. We did not see a way to run such a sweep in Õ(D) rounds. On parallel machines [4] computes the dominators of a DAG with the processors of one transitive closure, where the method before it took n times as many. To our knowledge there is no earlier algorithm for dominators, strong articulation points or strong bridges in CONGEST, on planar networks or otherwise. Ω(D) holds: take two directed paths from r to y of length about D, and let the first arc of one be present or absent, which changes idom(y).

Three parts are older in spirit:

- Sequential planar oracles for one failure [5] take a separator path P, the earliest and the latest vertex of P with a given reach, and detours, which are paths from before a failed vertex of P to after it. Our a(y), b(y) and jumps below are close relatives. The layers L_i of [5, Section 6.1] are exactly our sets B_i without p_i, and [5] computes one dominator tree per layer. Its Lemma 6.5, that a failure in another layer changes nothing, is Lemma 4(a) in spirit, and its rescuers do the work of our entries. There the dominator trees are an input, computed by a sequential algorithm.
- A sweep along one path from s to t finds all s-t bridges and articulation points [6].
- The reduction of Corollary 2 is [7].

What is new here, if it survives, is the bound, the computation of Section 5 with aggregates only, and the recursion of Lemma 4: the flow graph with ρ and the entries E_K, and one class per head, which keeps the problems vertex-disjoint and rooted. The path step needs no planarity. Planarity enters through the General Search Theorem and the tools below it.

## 2. Tools and problems

As in `notes/GENERAL_DFS.md`, Section 2: the Multi-Source Lemma, part-wise aggregates (P), (T2), the Split Lemma and its rounds, Lemma 4 of `notes/DAG_DFS.md`. All run at once on vertex-disjoint sets. We take from `notes/GENERAL_DFS.md` the sequence of *passes*: each pass takes a class (z, Q), picks a path R in D[Q] from z, and replaces Q by its classes for R. There are O(log² n) passes in series, problems at each pass are vertex-disjoint, and a problem below 12 vertices is solved locally.

A *problem* here is (Q, E), with E ⊆ Q the *entries*, and a *root* z in E such that every vertex of Q is reached from z in D[Q]. Its *flow graph* is D[Q] with an extra vertex ρ and an arc from ρ to each entry. A vertex w of Q *dominates* y in Q if w ≠ y and every path from ρ to y in the flow graph passes through w.

## 3. One path

Fix a problem (Q, E) with root z, and a simple path R = (p_1, ..., p_k) of D[Q] with p_1 = z. Put p_0 = ρ and O = Q ∖ V(R).

An index i in 0, ..., k *feeds* y in O if the flow graph has a path from p_i to y with all vertices after p_i in O. Let a(y) and b(y) be the least and the greatest index that feeds y. Every y is fed: take the last vertex of R or ρ on a path from ρ to y.

For 2 ≤ t ≤ k, an index i *jumps to* t if (p_i, p_t) is an arc of the flow graph, or if (u, p_t) is an arc for some u in O fed by i. Let A(t) and B(t) be the least and the greatest index that jumps to t. Since R is a path, t − 1 jumps to t, so A(t) ≤ t − 1 ≤ B(t).

For 1 ≤ j ≤ k let R_j be the set reached from ρ in the flow graph without p_j, and m(j) the least t > j with p_t in R_j, or k + 1 if there is none.

**Lemma 1 (intervals).** (a) For i ≠ j, p_i is in R_j if and only if i < j or i ≥ m(j). (b) For y in O, y is in R_j if and only if a(y) < j or b(y) ≥ m(j).

So p_j dominates p_i if and only if j < i < m(j), and p_j dominates y in O if and only if j ≤ a(y) and b(y) < m(j).

*Proof.* (a) R gives p_i for i < j, and from p_{m(j)} it gives all later vertices. No index strictly between j and m(j) is reached, by the definition of m(j).

(b) If i feeds y and p_i is in R_j, with i ≠ j, then y is in R_j, since the feeding path avoids p_j. Apply this to i = a(y) if a(y) < j, and to i = b(y) if b(y) ≥ m(j). Conversely let y be in R_j, and let p_i be the last vertex of R or ρ on a path from ρ to y without p_j. Then i feeds y, so a(y) ≤ i ≤ b(y), and p_i is in R_j, so by (a) i < j or i ≥ m(j). ∎

Call (j, x), for j < x ≤ k + 1, *closed* if A(t) ≥ j and B(t) < x for all t with j < t < x.

**Lemma 2 (closed intervals).** (a) m(j) is the largest x such that (j, x) is closed. (b) If j < j′ < m(j), then m(j′) ≤ m(j). So the sets {j, ..., m(j) − 1} are laminar.

*Proof.* (a) Let j < t < m(j), and let i jump to t. If i < j or i ≥ m(j), then p_i is in R_j and the jump avoids p_j, so p_t is in R_j, against Lemma 1(a). So i lies in j, ..., m(j) − 1, and (j, m(j)) is closed.

Let (j, x) be closed, and suppose that a path from ρ without p_j meets some p_t with j < t < x. Take the first such vertex on the path, and let p_i be the last vertex of R or ρ before it. Then i ≠ j, and i is not strictly between j and x, so i < j or i ≥ x. So i jumps to t, and A(t) < j or B(t) ≥ x, against closedness. Hence m(j) ≥ x.

(b) Suppose m(j′) > m(j), and let t = m(j). A path from ρ to p_t without p_j exists. It passes through p_j′, since j′ < t < m(j′). Its prefix puts p_j′ in R_j, against j < j′ < m(j). ∎

**Lemma 3 (deepest).** (a) All dominators of p_t in Q lie on R. The last one is p_j for the largest j < t with m(j) > t, if there is such a j. (b) For y in O the dominators of y on R are the p_j with 1 ≤ j ≤ a(y) and m(j) > b(y). They come before all other dominators of y, in the order of their indices.

*Proof.* (a) (ρ, p_1, ..., p_t) is a path, and Lemma 1 applies. (b) The set is Lemma 1. The path that follows R to p_{a(y)} and then feeds y holds all dominators of y, and after p_{a(y)} it stays in O. ∎

## 4. Classes

Apply the Split Lemma to Q and R. For a class K with head h and tail p(h) on R, let E_K be the set of vertices of K that are in E or have an arc from Q ∖ K. So h is in E_K, and (K, E_K) is a problem with root h.

**Lemma 4 (classes).** Let y be in K. (a) All dominators of y in Q that are off R lie in K. (b) A vertex w of K dominates y in Q if and only if it dominates y in K.

*Proof.* Every vertex v of a class K′ with head h′ is reached from ρ inside R ∪ K′: follow R to p(h′), then h′, and then a path in D[K′]. This gives (a) with K′ = K.

(b) Let P be a path from ρ to y in the flow graph of K without w. Its first vertex e after ρ is in E_K. If e is in E, then P is a path in the flow graph of Q. Otherwise e has an arc from some v in Q ∖ K. Then v is on R or in another class, and by the first remark v is reached from ρ with no vertex of K on the way. So in both cases y is reached in the flow graph of Q without w.

Conversely let P be a path from ρ to y in the flow graph of Q without w. Let e be the first vertex of P after its last vertex outside K, where ρ counts as outside. Then e is in E_K, and the rest of P lies in K. So y is reached in the flow graph of K without w. ∎

*The algorithm.* The first problem is the set reached from r, with E = {r}. At each pass on a class Q with path R, all vertices of Q compute their last dominator on R by Section 5, and a vertex that has one records it, overwriting any earlier record. Then every vertex of a new class marks itself as an entry if it has an arc from a vertex of Q outside its class, in one round. The vertices of the first problem know that they are reached from r, and they tell their neighbours, so an arc from an unreached vertex never counts. This is needed. Take r = 0 and, for i = 0, ..., 6, the arcs 0 → 1 + 3i, 1 + 3i → 2 + 3i, 3 + 3i → 2 + 3i. If the arc from the unreached 3 + 3i counted, a vertex 2 + 3i off the first path would be an entry of its class and keep the record 0, while its immediate dominator is 1 + 3i. A problem below 12 vertices collects its flow graph and solves it, and its vertices record their immediate dominators if these are not ρ.

**Proposition.** At the end y records idom(y).

*Proof.* Paths from r to y stay in the set reached from r, so dominators of y in the first problem are its dominators in H. For a problem Q holding y and a pass with path R, Lemmas 3 and 4 say: if y is on R, its dominators in Q are those on R; otherwise they are those on R, followed by its dominators in its class. So the last dominator of y comes from the last problem on its chain where y has a dominator, which is the last record. ∎

## 5. One path in Õ(D) rounds

Vertex-disjoint problems run at once throughout. The vertices of R know their positions by (T2).

*Step 1: a and b.* b(y) is the first coordinate read from the key e(y) of the Split Lemma. a(y) comes in the same way, with keys (i, id(z)) for a head z with tail p_i, where entries off R count with i = 0. The bit search of Lemma 4 of `notes/DAG_DFS.md` needs only that keys do not increase along arcs and that a path from the best head stays in its class, and both hold here by the same proof. Let A_a = {p_a} ∪ {y : a(y) = a} for a ≥ 1, and B_b = {p_b} ∪ {y : b(y) = b}. A feeding path from p_{a(y)} stays in A_{a(y)}: its vertices are fed by a(y), and if one were fed by a smaller index, y would be too. So the sets A_a are connected and vertex-disjoint, and so are the sets B_b, and (P) applies to each family.

In one round p_t learns A(t) and B(t), the least and the greatest of: a(u) and b(u) for arcs (u, p_t) with u in O, i for arcs (p_i, p_t), and 0 if p_t is an entry. If A(t) = a ≥ 1, then p_t has a neighbour in A_a, so it can send to A_a and hear from it. We call p_t a *leaf* of p_a.

*Segments.* For a level ℓ, a *segment* is a set of positions whose codes t − 1 agree above bit ℓ. It is S = [l, r], cut by bit ℓ into Z = [l, c] and Y = [c + 1, r], and we skip it if Y is empty. Segments of one level are vertex-disjoint subpaths. For positions i < i′, there is exactly one segment with i in Z and i′ in Y. A *sweep* gives each vertex of a subpath the minimum of some values before it or after it on the subpath. It takes O(log n) applications of (P), over the dyadic pieces of the subpath.

*Step 2: m.* Fix a segment. For j in Z let X(j) be the first t in Y with A(t) < j, or r + 1 if there is none. For x in c + 2, ..., r + 1 call x *good* if B(t) < x for all t in [c + 1, x). For x in c + 1, ..., r + 1 let g(x) be the largest good value at most x, if there is one. The following are computed:

1. g(t) for t in Y by sweeps in Y, and g(r + 1), the first t° in Y with A(t) < l, and g(t°), by aggregates over S.
2. For a in Z, the first leaf t_a of p_a in Y, with g(t_a), by one aggregate over A_a.
3. X(j) = min(r + 1, t°, min {t_a : a in Z, a < j}), with its value of g, by a sweep in Z.
4. For j in Z, the minimum of A and the maximum of B over (j, c], by sweeps in Z.

The vertex p_j takes x = g(X(j)) as a *candidate* if it exists, if A(t) ≥ j on (j, c], and if B(t) < x on (j, c]. Finally m(j) is j + 1 or the largest candidate of j over all levels.

**Lemma 5.** If a candidate exists for j in Z, it is the largest x with (j, x) closed and c + 2 ≤ x ≤ r + 1, and otherwise there is no such x. So m(j) is as stated.

*Proof.* For such x, (j, x) is closed if and only if (1) A ≥ j on (j, c], (2) B < x on (j, c], (3) A ≥ j on [c + 1, x), and (4) B < x on [c + 1, x). Here (3) says x ≤ X(j), and (4) says that x is good. Condition (2) is monotone in x. So if some x works, then g(X(j)) works and is the largest. By Lemma 2(a), m(j) is the largest x with (j, x) closed, and if m(j) > j + 1, then j and m(j) − 1 lie in Z and Y of one segment. ∎

*Step 3: labels.* Fix a segment. Its *chain* is the set of j in Z with m(j) > c + 1. By Lemma 2(b) it is j_1 < ... < j_s with m_1 ≥ ... ≥ m_s, where m_i = m(j_i). For a in Z let λ(a) be the last member at or before a. For t in Y let δ(t) be the last member with m(j) > t. Either may not exist. λ comes by a sweep in Z.

**Lemma 6 (rings).** Let i ≥ 1 with m_{i+1} < m_i ≤ r + 1. Then X(j_{i+1}) lies in [m_{i+1}, m_i), and A(X(j_{i+1})) lies in [j_i, j_{i+1}).

*Proof.* Write j = j_{i+1}, j′ = j_i, m = m_{i+1}, m′ = m_i. Since m < m′, the interval (j, m′) is not closed by Lemma 2(a), so some t with j < t < m′ has A(t) < j or B(t) ≥ m′. Since (j′, m′) is closed and j′ < t < m′, we have B(t) < m′ and A(t) ≥ j′. So j′ ≤ A(t) < j. Since (j, m) is closed, t is not below m. So t is in [m, m′), and it lies in Y, since m ≥ c + 2 and m′ ≤ r + 1. The first such t is X(j), since all t in Y below m have A(t) ≥ j. ∎

To compute δ we place *marks* in Y.

- *Rings.* A vertex a of Z with λ(a) = j_i and next member j_{i+1}, with m_{i+1} < m_i ≤ r and t_a = X(j_{i+1}), sends j_i to the leaf p_{t_a}. By Lemma 5, since c + 2 ≤ m_{i+1} ≤ r, we have g(t_a) = m_{i+1}, and the leaf places at this position a mark with value j_i. Each member j_{i+1} gives its m and X to p_{j_{i+1} − 1} in one exchange along R. They then travel back over the half-open subpath [j_i, j_{i+1}), and j_i sends its own m forward over it. These subpaths are vertex-disjoint. By Lemma 6 exactly one a sends for each such i. The subpaths from m_{i+1} to t_a lie in the disjoint sets [m_{i+1}, m_i), so at most one of them crosses the middle of any dyadic piece of Y, and all marks arrive by O(log n) applications of (P).
- *The rest.* Let J be the last member with m(j) > r, if any, and let j⁺ be the member after J, or j_1 if there is no J. By aggregates over S, if m(j⁺) ≤ r, a mark goes to position m(j⁺), with value J, or with the value "none" if there is no J.

Then δ(t) is the value of the last mark at or before t, or j_s if there is none, by a sweep in Y. This is right: if m_{i+1} ≤ t < m_i, with m_{i+1} < m_i, the last member with m > t is j_i. The last mark at or before t is at m_{i+1}, with value j_i. If t < m_s, it is j_s. If m_1 ≤ t, there is no member, and the value is "none".

Each vertex of R now has a *label*: λ for segments where it lies in Z, and δ for segments where it lies in Y. A label has O(log n) entries. Each entry is a position with the identifier of its vertex, which travels with the position on the same routes, and each vertex of R adds its own identifier to its label.

*Step 4: reading off.* p_t takes δ(t) from its lowest level where it exists, which is its last dominator on R by Lemma 3(a), since j < t and m(j) > t puts j in Z of the segment with t in Y. A vertex y in O gets the labels of p_{a(y)} and p_{b(y)}, by O(log n) broadcasts over A_a and B_b.

**Lemma 7.** Let a = a(y) and b = b(y). If a = 0, y has no dominator on R. If a = b, its last dominator on R is p_a. If a < b, let S be the segment with a in Z and b in Y. If λ_S(a) and δ_S(b) both exist, the last dominator on R is the earlier of the two. Otherwise it is δ_{S′}(b) for the lowest higher segment S′ with b in its Y where this value exists, if any.

*Proof.* By Lemma 3(b) we want the largest j with 1 ≤ j ≤ a and m(j) > b. If a = b, this is j = a, since m(a) > a. Let a < b. If j is in Z, then m(j) > b ≥ c + 1, so j is in the chain. The members at or before a are a prefix of the chain, and the members with m > b are a prefix too, by Lemma 2(b). So the last common member is the earlier of λ(a) and δ(b). If there is none, j lies before S, so j ≤ a holds, and j lies in Z′ of a higher segment with b in Y′. The sets Z′ of lower segments hold larger positions, so the lowest such segment gives the largest j. ∎

*Rounds.* Step 1 takes two bit searches, each O(log n) runs of the Multi-Source Lemma. Each of O(log n) levels takes O(log n) applications of (P). So one pass takes Õ(D) rounds, and with O(log² n) passes the theorem follows. A problem below 12 vertices takes O(1) rounds. The labels and the marks are the only part that uses more than aggregates over R. They use the sets A_a, and the reading off uses the sets A_a and B_b.

## 6. Corollaries

*Corollary 1.* On each pass on the problem that holds t, broadcast t's position on R, or a(t) and b(t), over Q. Each p_j decides by Lemma 1 after Step 2. There is one such problem per pass. The small problem at the end of the chain is solved locally.

*Corollary 3.* Sections 3 to 5 and the Proposition use a pass only through two facts: its path starts at the root of the problem, and its new problems are the classes of the Split Lemma. The passes of `notes/DAG_DFS.md` have both: the path of step 4 and the paths π′ of step 5 start at the root of their problem, and each of them goes through Lemma 1 there. Each level has at most s + 1 such passes, and there are O(log n) levels. So the rounds are Õ(D·s), and s = 1 on a DAG. No identifier of a strong component is used, and the arguments use no General Search. ∎

*Corollary 2.* Find the strong components with the identifiers, and in each component C a root s, say with the least identifier. Vertex-disjoint components run at once. For v ≠ s in C, the digraph D[C] − v is strongly connected if and only if every other vertex reaches s and is reached from s in it. That is, if and only if v dominates no vertex in D[C] from s and none in the reversal of D[C] from s. This is the reduction of [7]. The reversal is a digraph on G as well. A vertex v that dominates some y has an out-neighbour y′ with idom(y′) = v: on a simple path from s to y, let y′ be the vertex after v. Then v dominates y′, or y could be reached without v, and the path up to y′ has no vertex between v and y′. So v learns this in one round. The roots s are tested by one run of the identifiers on the components without s, with one aggregate per component.

For strong bridges, subdivide each arc (u, v) by a vertex x_{uv}. The new network is planar, has diameter at most 2D + 2, which K₄ with one arc per edge attains with 4, and each round of it takes O(1) rounds on G, with x_{uv} simulated by u. An arc between two components is no strong bridge. An arc inside C is one exactly if x_{uv} dominates some vertex from s in the subdivided D[C] or in its reversal, and by the remark above the one out-neighbour of x_{uv} then has it as immediate dominator.

## 7. Checks

`sim/dom.py` runs Section 5 on the paths of `sim/gdfs.py`, with reachability computed directly. Instances: all families of `sim/gdfs.py`, and two new ones, `jumps` and `nest`, a directed path with non-crossing chords on both sides, in both directions, through vertices off the path. It also runs the path step alone on arbitrary digraphs, not necessarily planar, with random paths and entries, and on whole paths of `jumps` and `nest`. `dom.py dag` runs Corollary 3 on the passes of `sim/dagdfs.py`.

Two lanes of 600 seconds on the current code, `dom.py 981 600` and `dom.py 982 600 big`, no FAIL in any counter. Every full run passed the planarity check.

| Lane | Runs | Path step, random paths | Path step, whole paths | Trees compared | m checked | Deepest checked | Star marks | Past marks | Max n | Max k | Longest chain | Max levels |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `981` | 30,252 | 90,807 | 90,807 | 30,252 | 2,812,852 | 6,185,354 | 79,756 | 246,786 | 203 | 89 | 32 | 12 |
| `982 big` | 17,804 | 53,433 | 53,433 | 17,804 | 1,975,866 | 5,997,383 | 47,470 | 160,359 | 675 | 170 | 128 | 20 |

Corollary 3, on the passes of `sim/dagdfs.py`, compared with `networkx`, no FAIL. `dom.py dag 983 300` had 212,791 runs, 186,585 of them on DAGs, up to n = 211, and `dom.py dag 984 300 big` had 87,533 runs, 76,034 of them on DAGs, up to n = 349. The others have cycles, with strong components up to 347 vertices and up to 55 passes in a level. Every instance passed the planarity check.

Negative controls, `dom.py ctl 985 40`, 40 seconds each. Each changes one rule, and only a wrong tree or a failed internal check counts.

| Control | What it changes | Runs | Wrong trees |
|---|---|---|---|
| `noentry` | the root of the path is the only entry | 9,768 | 5,346 |
| `noback` | B(t) is capped at t - 1, so jumps from behind t do not count | 9,970 | 1,845 |
| `onea` | b is replaced by a | 10,175 | 1,711 |
| `nosuf` | Step 2 drops the test A >= j on (j, c] | 10,334 | 2,497 |
| `noM` | Step 2 drops the test B < x on (j, c] | 10,357 | 682 |
| `nogood` | every x counts as good | 10,132 | 1,868 |
| `firstonly` | only the first level that raises m(j) counts | 10,240 | 2,391 |
| `nopast` | the mark of the ring running past r is left out | 10,254 | 1,881 |
| `maxld` | the larger of the two values is taken in Lemma 7 | 10,181 | 2,071 |

Three further controls change rules of the rings, in the path step alone, `dom.py ringctl 986 60`. The final tree does not see them in most runs, so here the checks on δ and on deepest values count.

| Control | What it changes | Runs | Counters that fire |
|---|---|---|---|
| none | | 13,844 | none |
| `markj1` | a mark takes the next member, not j_i | 14,342 | δ 33,195, deepest 17,140 |
| `ringr` | a ring needs m_i < r instead of m_i ≤ r | 14,586 | δ 4,508, deepest 2,303 |
| `nota` | the test t_a = X(j_{i+1}) is dropped | 14,457 | δ 7, deepest 3, mark_twice 6, mark_pos 7, routes_meet 2 |

The last one is a weak control here: it fires rarely.

Scale, `dom.py scale`, one run per size, no failure. These runs do not check planarity.

| Family | n | Reached | Nontrivial dominators | Max k | Longest chain | Levels |
|---|---|---|---|---|---|---|
| jumps | 510 | 510 | 508 | 64 | 28 | 16 |
| jumps | 2030 | 2030 | 2028 | 224 | 128 | 15 |
| jumps | 7207 | 7207 | 7205 | 787 | 505 | 31 |
| bigrid | 400 | 400 | 8 | 69 | 1 | 6 |
| bigrid | 1600 | 1597 | 39 | 278 | 2 | 12 |
| bigrid | 6400 | 6393 | 6391 | 1332 | 2 | 9 |
| ladder | 400 | 400 | 397 | 94 | 64 | 14 |
| ladder | 1600 | 1600 | 1597 | 340 | 256 | 23 |
| ladder | 6400 | 6400 | 6397 | 1347 | 1024 | 34 |

The final tree is compared with `networkx.immediate_dominators`, and on instances up to 60 vertices that function is compared with vertex removal. On small sets every path step is compared by vertex removal on m(j), so Lemma 2(a) only through the output of Step 2, on the formula of Lemma 1(b), on laminarity, and on the last dominator on R, so only that part of Lemma 3. The marks are compared with the definition of δ. `FAIL.not_reached`, `FAIL.prefix` and `FAIL.root_not_entry` cannot fire on correct bookkeeping, and `FAIL.not_planar` and `FAIL.networkx` guard the generator and the library. Lemma 4, the connectivity of A_a and B_b, and the leaf neighbours have no direct check here.

## 8. Not covered by the checks

- Rounds, messages and who knows what: no CONGEST simulation. The sim computes values in the order of Section 5, and it checks that rings are disjoint, but it does not route anything.
- The tools and the General Search Theorem, with their caveats in `notes/GENERAL_DFS.md`. If that theorem falls, the path step, Lemma 4 and Corollary 3 still stand, and the bound for all digraphs becomes the number of passes of whatever search replaces it, times Õ(D). The Dominator Theorem inherits the weak part of the General Search, which is (S).
- Corollaries 1 and 2 are not simulated in `sim/dom.py`.
- The marks of Step 3 are rare on the paths of the General Search: 24 ring marks in 10,837 full runs with `nest` included. They are exercised by the runs of the path step alone, which do not use these paths. The path step does not depend on where the path comes from, so this is a gap in coverage only.
- The final tree is blind to some errors in the marks. The controls `markj1`, `ringr` and `nota` above therefore count the internal checks on δ and on deepest values.
- Lean: `lean/PlanarMatching/Dominators.lean` proves Lemma 1, the part of Lemma 2 on closed intervals and laminarity, the class statement of Lemma 4, the candidate and ring statements of Lemmas 5 and 6, and the case of Lemma 7 with a and b in one segment, from given values, with standard axioms and no `sorry`. It does not cover that the aggregates compute these values, the rounds, the disjointness of routes, Lemma 3, Lemma 4(a), the tie of the class statement to E_K and to the Split of Q, the other cases of Lemma 7, the marks and their single sender, the chain composition in the Proposition, or the corollaries.

## 9. Open

- Low-high orders and two independent spanning trees of a flow graph, which would give certificates for the tree.
- 2-vertex-connected blocks of a digraph, and small vertex cuts in digraphs.
- The size of the set that each vertex dominates. The dominator tree is not a subgraph of G, so (T2) does not apply directly.

## 10. Remarks

*Jumps.* The definition of a jump has no exception for i = t − 1, and this is what puts A(t) and B(t) within one round in Section 5. On the path p_1, ..., p_6 with a vertex u off it and arcs p_2 → u, p_5 → u, u → p_3, such an exception would give A(3) = 5, while p_3 sees only a(u) = 2.

*Hubs.* A hub off R contributes one pair (a, b), each p_t is a leaf of one A_a, and each a in Z sends at most one mark per level. We know of no instance that pushes too much through a hub.

*Measured costs.* In a local simulation of Section 5 and the chain, each value moves only by one-round exchanges, by (P) on explicit parts, or by the Multi-Source Lemma as a black box. Every part is connected, each vertex lies in one part, values stay within 6 words, and at most one mark crosses any dyadic middle. A pass takes about 10 log² k applications of (P) for k up to 4096, and 26 to 50 Multi-Source runs.

## References

1. M. Parter. Distributed Planar Reachability in Nearly Optimal Time. DISC 2020. The identifiers of strong components.
2. T. Lengauer, R. E. Tarjan. A fast algorithm for finding dominators in a flowgraph. ACM TOPLAS 1(1), 121-141, 1979.
3. S. Alstrup, D. Harel, P. W. Lauridsen, M. Thorup. Dominators in linear time. SIAM J. Comput. 28(6), 2117-2132, 1999.
4. S. R. Pawagi, P. S. Gopalakrishnan, I. V. Ramakrishnan. Computing dominators in parallel. Information Processing Letters 24(4), 217-221, 1987. An earlier version: Parallel algorithm for dominators, ICPP 1986, 877-879.
5. G. F. Italiano, A. Karczmarz, N. Parotsidis. Planar Reachability Under Single Vertex or Edge Failures. arXiv:2101.02574.
6. M. Cairo, S. Khan, R. Rizzi, S. Schmidt, A. I. Tomescu, E. Zirondelli. Computing all s-t bridges and articulation points simplified. arXiv:2006.15024.
7. G. F. Italiano, L. Laura, F. Santaroni. Finding strong bridges and strong articulation points in linear time. Theoretical Computer Science 447, 74-84, 2012.
8. W. Fraczak, L. Georgiadis, A. Miller, R. E. Tarjan. Finding dominators via disjoint set union. Journal of Discrete Algorithms 23, 2-20, 2013. Corrections in Journal of Discrete Algorithms 26, 106-110, 2014.
