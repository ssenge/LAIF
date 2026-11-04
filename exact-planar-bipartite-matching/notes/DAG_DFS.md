# Depth-first search and topological order of planar DAGs

**Status.** Claim, written 3 Nov 2026. Proofs below, simulations in `sim/dagdfs.py` and `sim/sec5.py`. No human has checked it. Importance: solid if it survives for the DAG Search Theorem, since the bound is optimal up to polylogarithmic factors for a basic problem, and we found no earlier bound polynomial in D for it. Modest for the Topological Order Theorem, where earlier work suggests randomized ranks, see Context.

The model is CONGEST on a connected planar network G with n vertices and hop diameter D, with a known embedding. Õ hides factors polylogarithmic in n. A *digraph on G* has its arcs on edges of G, an edge may carry no arc, one arc, or one arc in each direction. In round bounds D is the diameter of the undirected G, and in D[K] it is the digraph of Sections 3 and 4. Identifiers are distinct. This note builds on `notes/DIRECTED.md`.

## 1. Results

**DAG Search Theorem.** Let H be a DAG on G. In Õ(D) rounds every vertex learns its parent, the order of its children, and its pre-order and post-order numbers in a depth-first search forest of H. The same holds for a depth-first search tree from a given vertex r, for the vertices reached from r.

**Topological Order Theorem.** Let H be a digraph on G. In Õ(D) rounds every vertex learns an integer in 1..c, where c is the number of strong components, such that the integers are equal exactly on strong components and increase along each arc between two strong components. On a DAG this is a topological numbering of the vertices by 1..n.

**Small Components Theorem.** Let H be a digraph on G whose strong components have at most s vertices. A depth-first search forest of H, and a tree from a given vertex, take Õ(D·s) rounds. With the Directed DFS Theorem of `notes/DIRECTED.md` this gives Õ(D·min(s,D)). `notes/GENERAL_DFS.md` claims Õ(D) for all planar digraphs, written later, which would supersede this bound.

All three are deterministic relative to the tree of bags, as in `notes/DIRECTED.md`. On digraphs with cycles this also rests on the identifiers of [1, Lemma 3], stated as randomized and only outlined, or on the rule `selfcomp` in Section 9 of `notes/DIRECTED.md`. On DAGs it does not.

**Context.** Depth-first search of an undirected planar network takes Õ(D) rounds [3], deterministically by [4]. For digraphs, [1] gives reachability and identifiers of strong components in Õ(D), and [5] states that these are the only known nontrivial problems on planar digraphs with an Õ(D) bound, to the best of its authors' knowledge, before it adds approximate shortest paths. To our knowledge no earlier depth-first search for planar digraphs or DAGs in CONGEST has a bound polynomial in D.

For the order, [8, Corollary 33, Remark 34], adapting [9], computes with high probability polynomially bounded ranks that are equal exactly on strong components and monotone on the arcs between them, with Õ(1) Minor-Aggregation rounds and Õ(1) calls to a reachability oracle. With the Multi-Source Lemma as the oracle this suggests randomized ranks in Õ(D) on planar digraphs, with the caveat of `notes/DIRECTED.md`. We did not prove this. What stays new here is the exact range 1..c, which is no immediate corollary, since sorting polynomial labels across a bridge costs far more than Õ(D), and determinism.

Ω(D) holds for depth-first search, since a directed path with one arc reversed at the far end changes the numbers at the other end. That argument fails for topological numbers, since the first vertices of the path can keep their numbers. For them take the chain a_m → ... → a_1 → v_0 → b_1 → ... → b_m and a vertex f adjacent to a_m and b_m. With both arcs into f the chain followed by f is a Hamiltonian path, which forces m + 1 at v_0. With both arcs out of f, f followed by the chain is one, which forces m + 2. The diameter is m + 1, and f is at distance m + 1 from v_0.

The classes of Section 3 are the dangling subgraphs of [11, Definition 7, Lemma 8]. On DAGs they refine the sets R′(v_i) of [6, Section 7]. With cycles they do not quite: on 0→1, 0→3, 1→2, 2→0 with π = (0,1), R′(v_1) holds 3, while Lemma 1 gives the head 3 the tail v_0. [6, Lemma 2], whose proof it takes from [10, Theorem 11], reduces the lexicographically least depth-first search of a DAG to reachability in logspace. That reduction asks many adaptive queries, and we did not see a form of it in Õ(D) rounds. This note gives some real search, not the lexicographic one. The new parts are that one class per head gives vertex-disjoint connected problems with real roots, so a separator of [2] applies with no virtual root, that a whole path can be added to a DAG in one pass, and the CONGEST bounds. The bounds are the main novelty, and the combinatorics is modest, since the deep-first order is already in [6]. We did not trace that order further back: [6] cites [7] only in its introduction, and we did not check the text of [7].

## 2. Tools

From `notes/DIRECTED.md`: labels on any digraph (T1), trees (T2), the Out-Forest Theorem, and from `notes/MATCHING.md` the Multi-Source Lemma. Each takes Õ(D) rounds on any digraph on G. A union of digraphs on vertex-disjoint sets is again a digraph on G, so all problems below run them at once.

**(S)** [2, Theorem 3]. Let G_1, ..., G_t be vertex-disjoint connected subgraphs of G with at least 12 vertices each, and T_i a spanning tree of G_i. In Õ(D) rounds each G_i learns the ends of a path of T_i whose removal leaves connected components of at most 3/4 of the vertices of G_i. Other vertices of G count as parts of their own, with weight 0, since [2, Theorem 3] asks for a partition with 1/12-proper weights. We apply it to induced subgraphs G[Q]: a spanning tree of a connected subgraph on Q spans G[Q], and a connected component of the subgraph minus a path lies in one of G[Q] minus the path, so the bound of 3/4 carries over. One (P) gives the ends to all of G_i. [2, Theorem 3] says connected, its Lemma 5 assumes biconnected, and its Appendix A.2 for many parts is a brief overview, so this rests on a part of [2] that we did not check.

**(P)** [2, Lemma 7]. An aggregate over each of a family of vertex-disjoint connected subgraphs takes Õ(D) rounds.

An *ordered tree* has an order on the children of each vertex. A vertex b is *right of* a if pre(b) > pre(a) and post(b) > post(a). A *search tree* of D[K] from x is an ordered tree on K with root x and with arcs of D such that no arc of D[K] goes from a vertex to a vertex right of it.

**Fact 1.** A search tree of D[K] is the result of a real depth-first search of D[K] that at each vertex visits its children in order and then scans its other arcs. At the top level K is closed under arcs of H, so this is a search of H. This is Lemma 9 of `notes/DIRECTED.md`: when the search scans the other arcs of a, it has visited the subtree of a and everything before a in pre-order, so an unvisited head would be right of a.

## 3. The Split Lemma

Let D be a digraph, x a vertex and K a set in which every vertex is reached from x in D[K]. Let π = (v_0, ..., v_k) be a path in D[K] with v_0 = x, and R = K ∖ V(π). Give the arc (v_i, z) with z in R the key (k − i, id(z)). So deeper vertices of π come first. A *head* is a vertex z of R that receives such an arc, and its key is the least key among these arcs. For y in R let e(y) be the least key of a head that reaches y in D[R]. The *class* of a head z is K_z = {y : e(y) = key(z)}, and it counts only if z is in it. One that does not is empty, by the proof of (a), so this only drops empty sets. Let p(z) be the tail of the arc that gives z its key.

**Lemma 1 (split).** (a) The classes partition R, and every vertex of K_z is reached from z in D[K_z]. (b) If (y, y′) is an arc of D[R], then e(y′) ≤ e(y). (c) Let T_z be a search tree of D[K_z] from z for each class. Let T consist of π, the arc (p(z), z) and T_z for each class, where the children of v_i are v_{i+1} first and then the heads z with p(z) = v_i whose class counts, in the order of their keys. Then T is a search tree of D[K] from x.

*Proof.* (b) A head that reaches y reaches y′.

(a) Let y be in R. A path from x to y has a last vertex v_i on π, and its next vertex is a head that reaches y in D[R]. So e(y) exists. Let e(y) = key(z), and let w be on a path from z to y in D[R]. Then e(w) ≤ key(z) since z reaches w, and e(y) ≤ e(w) by (b), so e(w) = key(z). So the path stays in K_z. With w = z, z is in its own class.

(c) By (a) each vertex of R lies in one class that counts, and each head of such a class has one parent p(z), so T is an ordered tree on K with arcs of D. Let (a, b) be an arc of D[K]. We show that b is not right of a.

- a = v_i and b on π: b is an ancestor or a descendant of a.
- a = v_i and b in R: (v_i, b) has key (k − i, id(b)), so b lies in a class of key at most this. Its head z has p(z) = v_j with j ≥ i. If j > i, then b is below v_{i+1}. If j = i, then b is below v_i. Either way b is a descendant of a.
- a in the class of z with p(z) = v_i, and b = v_j on π: if j ≤ i then b is an ancestor of a. If j > i then b is below v_{i+1}, the first child of v_i, so b comes before a in pre-order and is not right of it.
- a and b in R, in one class: T_z is a search tree, and "right of" is the same in T_z and T.
- a in the class of z and b in the class of z′ ≠ z: by (b) key(z′) < key(z). If p(z′) = v_j and p(z) = v_i, then j ≥ i, and j > i puts z′ below v_{i+1}, the first child of v_i, while j = i puts z′ before z among the children of v_i. Either way the subtree of z′ comes wholly before the subtree of z, so b is not right of a. ∎

A forest is the same lemma with π a single virtual vertex that has an arc to each root, where the identifier of a root fixes the order of the roots.

**Lemma 2 (blocks).** Let τ = (s_1, ..., s_m) be a path in D[R]. (a) Each class holds a contiguous part of τ. (b) Let τ be simple, and (z, K_z) a class with nonempty part β = (s_a, ..., s_b). If z is in β, let s_c = z. Otherwise let Z be the set reached from z in D[K_z ∖ β], and s_c the vertex of β of least index with an arc from Z. Then s_c exists, and there is a path π′ from z that goes through Z to s_c, or starts at s_c = z, and goes on along β to s_b. For a ≤ ℓ < c, the vertices s_ℓ and s_c lie in one strong component of D[K_z]. On a DAG therefore c = a.

*Proof.* (a) By Lemma 1(b), keys do not increase along τ. (b) z reaches β in D[K_z], and the first vertex of β on such a path has an arc from Z, or is z. π′ is a path: take a simple path through Z, which avoids β, and τ is simple. For the rest, take ℓ < c. A path from z to s_ℓ first meets β at some s_{c′}, and c′ ≥ c by the choice of c, or s_{c′} = z = s_c. So s_{c′} reaches s_ℓ, s_ℓ reaches s_c along β, and s_c reaches s_{c′} along β. ∎

So if π′ goes into Lemma 1 for the class K_z, what is left of τ in K_z is the path (s_a, ..., s_{c−1}), and part (a) applies again. Each round shortens each part by at least one, and after the first round what is left of a part has at most s − 1 vertices, if strong components have at most s. So at most s rounds absorb all of τ, and on a DAG one round does.

## 4. The algorithm

A *problem* is (x, K) with every vertex of K reached from x in D[K]. Problems are vertex disjoint, and D holds only arcs inside problems. At the start, for a tree from r the single problem is r with the set it reaches. For a forest, take as roots the sources of H, or on a general digraph one vertex of each source component, found with the identifiers of [1] and one aggregate per component. The identifier of a root is its pre-order number in a BFS tree of G. Lemma 1 gives the first problems.

One *level*, for all problems (x, K) at once:

1. If |K| < 12: D[K] is connected, so x collects it in O(1) rounds and solves it. Otherwise:
2. Compute a spanning out-tree F of K from x by the Out-Forest Theorem, with the roots of all problems as the sources.
3. Apply (S) to the underlying graph of D[K], with the tree F. This gives u and v, and P is the tree path between them.
4. Let π be the path of F from x to u, and τ the part of the path of F from x to v that is not on π. So P ⊆ V(π) ∪ V(τ). Apply Lemma 1 with π.
5. While τ has vertices left: in each class that holds a part of τ, take π′ of Lemma 2 and apply Lemma 1 to the class with π′. Drop the vertices of π′ from τ.

The classes at the end are the problems of the next level. Solving them gives the search tree of (x, K) by Lemma 1(c), applied backwards.

**Lemma 3.** A problem of the next level has at most 3/4 of the vertices of (x, K).

*Proof.* Its digraph is connected, with no vertex of π or τ, so no vertex of P, and its arcs are arcs of D[K]. So it lies in one component of the underlying graph of D[K] minus P. ∎

So there are O(log n) levels. By Fact 1 the final tree is a real depth-first search of H. Steps 2 to 5 use at most s + 1 applications of Lemma 1, and 2 on a DAG.

**Lemma 4 (rounds).** One application of Lemma 1, to any vertex-disjoint set of problems at once, takes Õ(D) rounds. Steps 1 to 3, and one round of step 5 without its application of Lemma 1, take Õ(D) rounds.

*Proof.* The vertices of π are marked by (T2): v is on the path to u exactly if its subtree in F holds u. Their position on π is an ancestor sum by (T2). One exchange gives each z in R its key, its tail p(z) and the arcs of D[R].

The classes come by binary search over the bits of e(y), from the top, as in Lemma 7 of `notes/DIRECTED.md`. Suppose all y know the first i bits of e(y). Keep the arcs between vertices with the same first i bits. Run the Multi-Source Lemma from the heads whose key agrees with their own first i bits of e and has next bit 0. Then the next bit of e(y) is 0 exactly if y is reached. Indeed a path from the best head stays in the class by the proof of Lemma 1(a), and so is kept, and if y is reached from a head with next bit 0, then e(y) is at most this key. There are O(log n) bits, and each run takes (T1) and the Multi-Source Lemma.

A head z sees that it is in its own class if e(z) = key(z). Then it tells p(z), which so learns its children in order. Arcs between classes are dropped after one exchange. Sizes of problems come by (P). Step 1 is O(1) rounds, step 2 is the Out-Forest Theorem and step 3 is (S).

In step 5, each vertex of τ knows its position, and (P) over the class gives its part of τ. The set Z comes from the Multi-Source Lemma on the digraphs D[K_z ∖ β], the arc into s_c of least index by (P), and the path through Z from the Out-Forest Theorem on the same digraphs, with (T2) to mark it. Its length comes from (T2), and with the position on β this gives positions on π′. One exchange tells a vertex of β its next vertex in β, which may have left the class. ∎

*Proof of the DAG Search and Small Components Theorems.* There are O(log n) levels, each with at most s + 1 applications of Lemma 1 and at most s rounds of step 5. The numbers come from (T2) at the end. In a forest, each root also adds the total size of the earlier trees, and these are prefix sums along the BFS tree by pre-order, in O(D) rounds. On a DAG s = 1. ∎

## 5. Topological order

On a DAG take the search forest and n − post(v), with post(v) counted from 0. Let (u, v) be an arc. Then v is not right of u, and v is no ancestor of u, since H has no cycle. So post(v) < post(u).

For any digraph, run the algorithm on the condensation, which is a planar DAG, as follows. Compute identifiers of strong components by [1], and treat a component as one *point* of the problems. A problem is a union of components, and its root is a vertex of its root component. All reachability runs on H itself, since for a union R of components, reachability in H[R] agrees with reachability between components. The out-tree F of step 2 is a tree of H from the root, and (S) is applied with F to the underlying graph of D[K]. A directed path of H cannot return to a component that it has left, so the path of F to u gives a path of points π.

*Keys.* In each component C fix a spanning tree T_C with a pre-order pre_C, by (T2), once at the start. An arc (a, b) from a in the point v_i of π to a point Z of R has the key (k − i, pre_C(a), id(Z)). A head is a point, its key is the least key among its arcs, and the end b of that arc, found by one (P) over Z, is the root of its class. Lemma 1 uses only the first coordinate and that keys of heads are distinct, so Lemmas 1 and 2 hold on points. The order by pre_C is what makes the numbers below computable.

*Pieces.* The path of F to v can re-enter components of π. So what is left of τ after these components go is a sequence of *pieces*, each a path of points in D[R].

**Lemma 5.** Each class holds a contiguous part of one piece.

*Proof.* Let y be on a piece A and y′ on a later piece B. Let v_j be the last point of π on τ before B. The next point w on τ is a head that reaches y′ in D[R], so the first coordinate of e(y′) is at most k − j. Let e(y) = key(z) with p(z) = v_i. Then v_i reaches z, z reaches y, and y reaches v_j along τ. If i ≥ j, then v_j reaches v_i along π, and this closes a cycle in the condensation through z, which is not on π. So i < j, the first coordinate of e(y) is k − i > k − j, and e(y′) < e(y). So y and y′ lie in different classes. Within one piece use Lemma 2(a). ∎

So Lemma 2(b) applies to each class with its part of its piece, with c = a, and step 5 takes one round. Whole components go, and removing more than P keeps Lemma 3. The result is a search forest of the condensation.

*Numbers.* In (T2) a point counts 1, and contracting components is one more Minor-Aggregation contraction, so subtree and ancestor sums on the tree of points take Õ(D) rounds. The sizes of earlier siblings are not an aggregate in general: heads ordered by id(Z) can hang on far vertices of one component, and Section 9 shows that this order takes far more than Õ(D). With the keys above, let w(a) be the total size of the heads with tail a in the point C, and let W(a) be the sum of w(b) over b before a in pre_C. By (T2) on T_C this is a weighted pre-order, a sum of ancestor and subtree sums. A head with tail a then has as earlier siblings the next point of π, of a size known by (P), everything counted in W(a), and the earlier heads at a, which a knows. In a forest the roots are ordered by pre-order in a BFS tree of G, as in Section 4. The number is c − post(v), counted from 0. ∎

## 6. Checks

`sim/dagdfs.py` runs the algorithm on DAGs made by orienting planar graphs along random, breadth-first and depth-first vertex orders, reversed or not, on grid DAGs, and on digraphs with cycles from `sim/dirs.py`, each checked for planarity. Out-trees are chosen with varying shape, since the algorithm must work with any of them, and the shape `any` can give every spanning out-tree. Each result is checked by the replay of a real search, with the coverage of all reached vertices, and reversed post-order against every arc. Every separator is checked against 3/4 by its actual components, every class against Lemma 3, every part of τ for being contiguous, every level against the count of passes, and a sample of classes by the binary search of Lemma 4 against a direct computation. The condensations of digraphs with cycles are checked for planarity and run as DAGs. `sim/sec5.py` runs Section 5 as written, with F and the separator on the graph of H.

Two long lanes, no failure:

| | `sim/dagdfs.py 9011 700` | `sim/dagdfs.py 9012 700 big` |
|---|---|---|
| Runs | 571,865 | 256,454 |
| DAGs | 501,497 | 223,109 |
| Replays of a real search | 607,034 | 273,010 |
| Condensations run as DAGs | 35,169 | 16,556 |
| Separators against 3/4 | 388,539 | 314,527 |
| Classes against Lemma 3 | 2,309,409 | 2,077,025 |
| Parts of τ for being contiguous | 360,313 | 310,768 |
| Binary searches against a direct computation | 77,654 | 62,843 |
| Largest n | 219 | 349 |
| Largest number of levels | 5 | 6 |
| Largest number of passes per level, digraphs with cycles | 39 | 69 |
| Largest component after a separator | 75% | 75% |

All DAG runs stayed within two passes per level. The passes on digraphs with cycles stayed below the bound of the Small Components Theorem.

Negative controls, `sim/dagdfs.py ctl 9013 60`. Each breaks one rule, and each is detected:

| Control | Rule broken | Runs | What fired |
|---|---|---|---|
| `shallow` | shallow vertices of π come first | 20,622 | replay 9,324 |
| `headfirst` | heads before the next vertex of π | 21,639 | replay 9,617 |
| `revhead` | heads in the wrong order | 21,612 | replay 3,946 |
| `onepath` | no step 5 | 19,339 | class too big 6,013, levels 48, replay 28 |
| `firsthit` | the entry of greatest index in place of least | 24,837 | more than 2 passes on a DAG 1,108 |

`sim/sec5.py` on points, no failure:

| | `sim/sec5.py 9021 700` | `sim/sec5.py 9022 700 big` |
|---|---|---|
| Runs | 359,307 | 176,412 |
| Runs with cycles | 199,926 | 102,203 |
| Checks of Lemma 5 | 1,415,828 | 1,181,470 |
| Checks of Lemma 3 | 1,394,101 | 1,191,430 |
| Step 5 in one round | 310,498 | 267,837 |
| Numbers against the formula | 7,747,375 | 7,382,278 |
| Arcs against the order | 21,521,536 | 21,402,571 |
| Runs where τ re-enters a component | 6,062 | 3,053 |
| Largest number of pieces | 10 | 10 |
| Largest n | 212 | 352 |

Negative controls, `sim/sec5.py ctl 9023 60`:

| Control | Rule broken | Runs | What fired |
|---|---|---|---|
| `shallow` | shallow points of π come first | 30,196 | numbers 138,291, order 44,207, replay 40,492, Lemma 5 2 |
| `idorder` | heads of a component ordered by identifier | 29,477 | numbers 13,111, order 340 |
| `noround` | no step 5 | 28,103 | Lemma 3 3,040 |

`sim/dagdfs.py scale`, on instances up to n = 6,400, gives at most 5 levels and 9 passes on grid DAGs, and at most 2 levels and 3 passes on stacked triangulations.

## 7. Not covered by the checks

- Rounds, messages and who knows what: no CONGEST simulation. Reachability is computed directly.
- The separator of the lanes is a fundamental cycle of a triangulation found by a central computation, not the protocol of [2]. (S), (P), (T1) and (T2) are read from [1] and [2] and from the earlier notes. Appendix B of [3] and the proof of [1, Lemma 3] are not checked.
- In `sim/dagdfs.py` the condensation runs as a DAG on the contracted graph, so it does not test the numbers or the pieces of Section 5. `sim/sec5.py` runs the form of Section 5 and its numbers, with reachability computed directly.
- The separator of the lanes takes the best fundamental cycle of a triangulation. It reaches the 75% allowed.
- Some counters of `sim/dagdfs.py` cannot detect a fault of the algorithm: `class_not_reached` and `block_not_reached`, since the group is defined as a reach, `block_no_progress`, `split_not_cover`, and `block_not_contiguous`, which holds for greedy classes under any key order. `topological` runs only after the replay passed, so it is then a theorem. No control exists for `bits`, `unbalanced`, `not_planar` or contiguity. About 12% of its runs have cycles.
- [2] asks in Theorem 3 for vertex-disjoint connected subgraphs, but its multi-part proof is at sketch level, and we read it as stated. The weakest spot is parallel biconnectivity, since [2] does not spell out augmentation across many parts at once. The graph Ĝ of [3], which [2] uses, can be read as non-planar when written literally for C the rim of a wheel, and as planar when the edge is attached to the copy in its corner. We did not check this.
- `lean/PlanarMatching/DagSearch.lean` proves Lemmas 1 and 2 in full and Fact 1, with no `sorry` and the three standard axioms, listed in `lean/axioms.txt`. Fact 1 is proved for a search defined as an inductive relation, with the numbers it assigns, and "right of" is shown to agree with these numbers. Every finite problem has a search tree, by recursion on classes (`exists_searchTree`), so the definition is not vacuous. Not in Lean: the separator (S), Lemmas 3 and 4, the forest with a virtual vertex, the count of rounds, Section 5 and all round bounds.

## 8. Open

- `notes/GENERAL_DFS.md` claims Õ(D) for depth-first search of all planar digraphs. What follows is the state before it. A bidirected path entered at its end shows that step 5 can take s rounds: each round adds one vertex. The undirected algorithm goes on along the longer side of the path, and a directed path has only one side. Aiming at the middle of τ keeps each piece of τ at half its length, but several pieces can then lie in one class, and one class takes one path per pass. A separator that bounds strong components only is enough: [11, Algorithm 10] extends a partial search tree by one path and one cycle per class, with one root per class and O(log n) passes per level, for all digraphs. So the problem reduces to a directed cycle or path through a strong component that leaves no heavy strong component. [11] and [6] find these on planar digraphs in parallel. `notes/GENERAL_DFS.md` finds them in Õ(D): two root paths of a spanning out-tree come from the separator, and a binary search on them picks the component.
- Dominators of a planar DAG: Corollary 3 of `notes/DOMINATORS.md` claims Õ(D) on the passes of this note.

## 9. Instances for Section 5

*Numbers under identifier order.* Let B(m) have a bidirected path c_0, ..., c_{2m−1} as one component, pendant arcs c_i → w_i, and a binary tree over the c_i on edges with no arcs, so D = O(log m), with 2 edges between the left and right halves. With identifier order, the numbers of the right pendants reveal the histogram of the left identifiers, which has binom(2m,m) values. This gives Ω(m/log n) rounds against D = O(log m), for this output and not for the theorem. The instance B(2) has 6 of 6 histograms, B(3) is the smallest with |K| ≥ 12, with 10 of 20, and B(4) has 70 of 70. Gathering the siblings over (P) on B(64) needs 5,859 bits against a limit of 72. With the key of Section 5, B(m) for m = 4 to 512 takes 2 levels and at most 106 runs of the Multi-Source Lemma.

*The same at constant diameter.* Take hubs A⇄B, leaves a_j⇄A and b_j⇄B, and pendant sinks p_j from a_j and q_j from b_j, for j = 1, ..., t, with id(p_j) = 4j and id(q_j) = 4j ± 1 by a bit x_j. The diameter is 5 and n = 4t + 2. The number of p_j reveals x_j across the single edge A−B, so that order needs Ω(t/log n) rounds.

*Pieces.* The smallest instance with more than one piece has 5 vertices and arcs (0,1), (1,2), (2,1), (0,3), (3,2), (2,4), with π = (0,1) and τ = (3,2,4). The pieces are [3] and [4], and no such instance exists on n ≤ 4. The ladder of `sim/sec5.py` has strong components {p_j, q_j} for j = 0, ..., m − 1, and arcs p_j → p_{j+1} and q_j → w_j → q_{j+1}. With π through the p_j and τ through the q_j and w_j it has the m − 1 pieces [w_j], and each class holds one.

## 10. Remarks

- Planarity is needed in (S). The graph K₁₂,₁₂ with a spanning tree of depth 2 has no tree path that meets the bound of 3/4: a tree path has at most 5 vertices, and what is left is connected, with at least 19 of the 24 vertices.
- The bound of 3/4 is reached by the separator of [2] itself: Algorithm 1 of [2], run centrally, has largest component exactly 75%.
- Numerically, levels stay within log_{4/3}|K|. The largest values seen are 6 at |K| = 96 with the threshold of step 1 at 12, and 13 at n ≤ 345 with that threshold at 2. Rounds of step 5 reach s for s = 1 to 7 and do not exceed it, and on DAGs there is always 1. Word counts stay at most 7.5 log₂ n, and calls to the primitives on DAGs up to n = 400 stay at most 8.6 log² n. Computing (T2) from (P) alone takes at most 146 aggregations on trees up to n = 16,384.

## References

1. M. Parter. Distributed Planar Reachability in Nearly Optimal Time. DISC 2020.
2. Y. Abd-Elhaleem, M. Dory, O. Weimann. A Simple Distributed Deterministic Planar Separator. arXiv:2602.22916.
3. M. Ghaffari, M. Parter. Near-Optimal Distributed DFS in Planar Graphs. DISC 2017.
4. B. Jauregui, P. Montealegre, I. Rapaport. Deterministic Distributed DFS and Other Problems via Cycle Separators in Planar Graphs. arXiv:2504.21620.
5. H. Le, H. Tierno, S. Yang. Planar Embedding of Okamura-Seymour Quasimetrics in Polynomial Time with an Application to Distributed SSSP. arXiv:2606.31192.
6. E. Allender, A. Chauhan, S. Datta. Depth-First Search in Directed Planar Graphs, Revisited. MFCS 2021; Acta Informatica 2022, doi:10.1007/s00236-022-00425-1. ECCC TR20-074, revision 3, states that an earlier version claimed a stronger bound with an error in a lemma.
7. A. Aggarwal, R. J. Anderson, M.-Y. Kao. Parallel depth-first search in general directed graphs. SIAM J. Comput. 19(2), 1990.
8. V. Ashvinkumar, A. Bernstein, N. Cao, C. Grunau, B. Haeupler, Y. Jiang, D. Nanongkai, H.-H. Su. Parallel, Distributed, and Quantum Exact Single-Source Shortest Paths with Negative Edge Weights. arXiv:2303.00811.
9. W. Schudy. Finding strongly connected components in parallel using O(log² n) reachability queries. SPAA 2008, 146-151.
10. P. de la Torre, C. P. Kruskal. Fast parallel algorithms for all-sources lexicographic search and path-algebra problems. J. Algorithms 19(1), 1-24, 1995.
11. M.-Y. Kao. All Graphs Have Cycle Separators and Depth-First Search on Planar Digraphs is in DNC. Technical Report 244, Indiana University, 1988; AWOC 1988, LNCS 319, 53-63.
