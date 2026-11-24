# Quantum algorithms for parameterized graph problems from classical search trees

Written 22 Nov 2026.

For a graph G and a budget k, Vertex Cover above LP asks for a vertex cover of size at most k, with the parameter μ = k − vc*(G), where vc*(G) is the optimum of the linear programming relaxation. Several problems reduce to it with μ bounded by their own parameter, and a quantum walk over its search tree then gives the bounds below.

**Theorem 1.** Odd Cycle Transversal, Above Guarantee Vertex Cover and Almost 2-SAT (clause and variable deletion) have quantum algorithms with bounded error, polynomial space and no quantum random access memory, in time O(1.5214^k) · poly(n). For Above Guarantee Vertex Cover, k is the excess of the minimum vertex cover over a maximum matching.

**Theorem 2.** Deletion to a graph whose vertex cover number equals its matching number (KVD), and Vertex Cover parameterized by the size k of a KVD set or of an odd cycle transversal, have quantum algorithms of the same kind in time O(1.2335^k) · poly(n).

**Theorem 3.** With k the solution size, quantum algorithms of the same kind solve Cluster Vertex Deletion in time O(1.3458^k) · poly(n), Edge Dominating Set in O(1.4951^k) · poly(n), and d-Path Vertex Cover (deletion of at most k vertices so that no path on d vertices remains) for d = 3, 4, 5, 6, 7 in O(1.3071^k), O(1.4624^k), O(1.6238^k), O(1.8261^k) and O(1.9899^k), times poly(n).

**Theorem 4.** Cluster Editing (at most k edge insertions and deletions that turn G into a disjoint union of cliques) has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, in time O(1.2721^k) · poly(n).

**Theorem 5.** Mixed Dominating Set (at most k vertices and edges that together dominate all vertices and edges) has quantum algorithms of the same kind in time O(1.8734^k) · poly(n) and in time O(1.3825^n).

**Theorem 6.** Feedback Vertex Set in Tournaments (delete at most k vertices so that a tournament on n vertices becomes acyclic) has quantum algorithms of the same kind in time φ^{k/2} · 2^{O(k/log k)} + poly(n) and in time ρ^{n/2} · 2^{O(n/log n)}, where φ = 1.61803… is the golden ratio, ρ = 1.46557… is the root of x³ = x² + 1, √φ = 1.27202… and √ρ = 1.21061…. Asymptotically this is O(1.2721^k + poly(n)) and O(1.2107^n).

Status: Claim. For Odd Cycle Transversal the matching bound on the relaxation and the bound on μ are in Lean (`lean/FptBranching.lean`), and so are the bases; for the problems of Theorem 2 only the arithmetic of the budget step is. The search tree of [1] and the reductions of [1] and [4] are used as stated there (Assuming), and the walk is the direct application of [2] and [3]. For Theorem 3 the search trees of [5], [7] and [9] are used as stated there, with the changes of Section 3; the bounds of [9] are computer-assisted and are used as stated (Assuming). For Theorem 4 the search tree of [15] and Theorem 1 of [2] are used as stated, with the split step of Section 4. For Theorem 5 the search trees of [18] are used as stated, with the tree of the first step given in Section 5. The bases and the split step are checked by script. For Theorem 6 the family of [19, Lemma 5], the reduction of [19, Lemma 6], the branching of [19, Lemma 9] and the minimization of [19, Lemma 7] with its partition [19, Lemma 10] are used as stated (Assuming), with quantum minimum finding [20] and reversible simulation [21]; the exponents are checked by script.

## Before and after

| Problem | Previous best bound | After |
|---|---|---|
| Odd Cycle Transversal | 2.3146^k classically [1]; 1.6181^k quantum, implied by [1, Theorem 1] with [3] | **1.5214^k** |
| Above Guarantee Vertex Cover | 2.3146^k classically [1]; 1.6181^k quantum, implied as above | **1.5214^k** |
| Almost 2-SAT | 2.3146^k classically [1]; 1.6181^k quantum, implied as above | **1.5214^k** |
| KVD | 1.5214^k classically [1]; 1.2721^k quantum, implied by [1, Theorem 1] with [3] | **1.2335^k** |
| Vertex Cover parameterized by a KVD set | 1.5214^k classically [1]; 1.2721^k quantum, implied as above | **1.2335^k** |
| Vertex Cover parameterized by an odd cycle transversal | 1.5214^k classically [1]; 1.2721^k quantum, implied as above | **1.2335^k** |
| Cluster Editing | 1.6181^k classically [15]; 1.7321^k quantum [17]; 1.3267^k quantum, the square root of the tree of [16] | **1.2721^k** |
| Cluster Vertex Deletion | 1.811^k classically [5]; 1.7321^k quantum [17]; 1.3821^k quantum, implied by [6] with [3] | **1.3458^k** |
| Edge Dominating Set | 2.2351^k classically [7]; 1.5215^k quantum, implied by [8] with [3] | **1.4951^k** |
| Mixed Dominating Set, parameter k | 3.510^k classically, polynomial space [18] | **1.8734^k** |
| Mixed Dominating Set, n vertices | 1.912^n classically, polynomial space [18] | **1.3825^n** |
| Feedback Vertex Set in Tournaments, parameter k | 1.6181^k classically [19]; 1.4143^k quantum, implied by the iterative compression of [23] with quantum search [22] | **1.2721^k** |
| Feedback Vertex Set in Tournaments, n vertices | 1.4656^n classically [19]; 1.2939^n quantum, implied by the polynomial-delay enumeration of the at most 1.6740^n minimal feedback vertex sets of [24] with [3] | **1.2107^n** |
| 3-Path Vertex Cover | 1.708^k classically [9]; 1.3089^k quantum, implied by [10] with [3] | **1.3071^k** |
| 4-Path Vertex Cover | 2.138^k classically [9]; 1.6184^k quantum, implied by [11] with [3] | **1.4624^k** |
| 5-, 6-, 7-Path Vertex Cover | 2.636^k, 3.334^k, 3.959^k classically [9]; 1.9863^k, 2.2242^k, 2.4395^k quantum, implied by [12] with [3] | **1.6238^k, 1.8261^k, 1.9899^k** |

All bounds hide polynomial factors in n. The new bases are √2.3146 and 2.3146^{1/4}, rounded up. The implied quantum bases come from a walk on the simpler search tree of [1, Theorem 1], of size 2.6181^μ, through the same reductions. Each bound of Theorem 3 is a direct application of [3] to the newest search tree, and the implied bases apply [3] in the same way to the earlier trees named in the table. For d-Path Vertex Cover the bases of [9], printed with three decimals, are raised by 0.0005 before the square root. The walk on the tree of [5] also serves as the oracle of the quantum monotone local search of [14], with bounds in n. To our knowledge, the only quantum bounds for these problems parameterized by k stated before are O(1.7321^k · √k · n³) for Cluster Vertex Deletion and Cluster Editing [17].

## 1. The tool

The algorithm of [1, Theorem 2] decides Vertex Cover above LP with a search tree of size 2.3146^μ · poly(n). Its rules apply polynomial-time preprocessing at a node and then branch. The worst branching vectors are (1, 3/2, 3/2) for rule B5 and (3/2, 3/2, 5/2, 5/2, 2) for rule B6, both with root 2.31460 in μ. The algorithm of [1] treats connected components separately and solves components of at most 10 vertices exactly. Here the budget stays global, as in [2, Section 5]: μ is additive over components, so branching inside one component gives the same drops of μ, and solving a small component exactly at a node and removing it lowers the budget by its vertex cover number and the relaxation by at most that, so μ does not grow. Rule B6 applies only when every component is 3-regular with surplus 2, so the whole graph being irreducible gives the same for the component of the branching vertex, which is what Lemmas 16 and 17 of [1] use. Every node therefore does polynomial work and branches, and the tree is plain. The walk on backtracking trees of [3] then decides it in time √(2.3146^μ) · poly(n) = O(1.5214^μ) · poly(n), with bounded error and polynomial space. A solution comes by self-reduction.

## 2. The reductions

- **Odd Cycle Transversal.** The construction of [1, Section 5.2] takes two copies of the vertex set, puts a copy of G on each, and joins the copies of each vertex by an edge. G has an odd cycle transversal of size at most k exactly when this graph H has a vertex cover of size at most n + k [1, Lemma 20]. The n joining edges form a perfect matching of H, so every fractional vertex cover of H has weight at least n (`matching_le_fractional`), and the excess at budget n + k is at most k (`transversal_excess`).
- **Above Guarantee Vertex Cover.** The relaxation is at least the size of a maximum matching, so μ is at most the excess over the matching [1, Theorem 3].
- **Almost 2-SAT.** Both versions reduce to Above Guarantee Vertex Cover [1, Corollary 2]. As instances of BIP2 they also reduce in linear time to Vertex Cover above LP with the same gap above the relaxation, which is at most k [4, Theorem 1 and Example 3].
- **Vertex Cover parameterized by a KVD set.** The preprocessing in the proof of [1, Theorem 5] (Lemma 1 there) leaves a graph G′ and a budget ℓ′, and G′ has a KVD set O of size at most k [1, Lemma 22]. Then vc(G′) − vc*(G′) ≤ |O|/2 ≤ k/2 (`kvd_excess`, from the two inequalities in the proof there). If ℓ′ ≥ vc*(G′) + k/2 the answer is yes at once, and otherwise the excess ℓ′ − vc*(G′) is below k/2 (`kvd_budget`). The walk then costs O(1.5214^{k/2}) = O(1.2335^k), times poly(n) (`half_cost`).
- **Vertex Cover parameterized by an odd cycle transversal.** An odd cycle transversal is a KVD set [1, Corollary 5].
- **KVD.** If G has a KVD set of size at most k, then vc(G) − vc*(G) = vc(G′) − vc*(G′) ≤ k/2 on the preprocessed graph G′ [1, Lemmas 2 and 22]. The walk tries the budgets from ⌈vc*(G′)⌉ up to vc*(G′) + k/2 on G′, and if none of them succeeds the answer is no. Otherwise a minimum vertex cover comes by self-reduction, which does not raise the excess, at a polynomial factor, and it gives a minimum KVD set in polynomial time [1, Corollary 4].

## 3. Search trees for Theorem 3

Each algorithm below is a search tree whose nodes do polynomial work and then stop or branch with a smaller budget, so the walk of [3] gives the square root of its size, and a solution comes by self-reduction.

- **Cluster Vertex Deletion [5].** The reduction rules are polynomial, the components of maximum degree 2 are solved in closed form, and the families of hitting sets that the algorithm branches over are themselves produced by a branching procedure. The analysis of [5] bounds the leaves of the combined tree, with every dead end of the inner procedure counted, so the inner steps are nodes of one tree. The same argument is given in [14] for this tree. The tree of [6] is plain as well.
- **Edge Dominating Set [7, Theorem 1].** The tree branches on vertices, 4-cycles and bad components, and a leaf with only clique components is solved in polynomial time [7, Lemma 2]. The analysis bounds the number of leaves. Its third stage is written as an enumeration of assignments of the bad components subject to two counting conditions. As a tree that assigns one component per level and prunes a node when the conditions fail even with the cheapest branch for every remaining component, it has the same leaves and at most polynomially more nodes, since the cheapest branch of each component type minimizes both counted quantities. The tree of [8] has the same final stage, over its 2-path components, and is restated in the same way.
- **d-Path Vertex Cover [9].** The generated algorithm (Algorithm 1 and Theorem 1 of [9]) applies two polynomial reduction rules, each followed by one call, solves the instance by brute force when every component has fewer than a constant number of vertices, and otherwise branches on a rule applied to one component with the global budget. Its bounds are those of Table 1 of [9]. The earlier trees of [10] and [12] are plain in the same sense, and the algorithm of [11] uses iterative compression, where each round is one plain tree.

## 4. Cluster Editing: Theorem 4

The algorithm of [15, Theorem 2] works on integer-weighted instances, with s(uv) > 0 for an edge, s(uv) < 0 for a non-edge and s(uv) = 0 for a zero-edge; the type graph has the edges as its edges. An unweighted input has weights ±1 and no zero-edges. The algorithm branches on an edge by forbidding or merging it, with branching number φ = 1.6180… in the budget, where creating and destroying a zero-edge count 1/2 each. A node (G, k) answers yes if and only if V(G) ≤ k, with V(G) = opt(G) + z(G)/2, the optimum cost plus half the number of zero-edges: every step lowers k by exactly the drop of V, where joining two zero-edges into one releases 1/2, and the cash-in leaf tests z ≤ 2k. The leaves of [15] that compare a transformation cost with k compare that cost plus z/2 with k. Some of its steps [15, Lemmas 3 and 5] compare the cost of a solution of a connected component with k, so they are exact when that component is the whole instance. Here a node whose type graph is connected applies the step of [15] unchanged, and a node whose type graph is disconnected applies a split step.

**The split step.** It is the level scan of [2, Lemma 2] for two parts. A component C whose pairs are all edges is removed, and k is lowered by z_C/2 for the z_C zero-edges between C and the rest. Let H be another component, z_H the number of zero-edges between H and G − H, k̃ = k − z_H/2, and K the largest multiple of 1/2 with K ≤ k̃/2. Some optimal solution puts no two components into one cluster, since every pair between them is a non-edge or a zero-edge, so V(G) = V(H) + V(G − H) + z_H/2, and V(H) ≥ 1/2, since H has a zero-edge or a conflict triple with integer weights. For k ≥ 16, make value calls (H, i) for i = 1/2, 1, … , K. If one succeeds at i = k′, make the tail call (G − H, k̃ − k′). Otherwise make value calls (G − H, i) for the same i, and if one succeeds at i = k″, make the tail call (H, k̃ − k″). If neither succeeds, V(H) + V(G − H) > k̃ and the answer is no. For k < 16, make value calls (H, i) for i = 1/2, 1, … up to k̃ and then the tail call on G − H.

**Measure.** Let B(G, k) = 2φ^{max(k, 0)} at a node that branches or splits, and B = 2 at a leaf.

- **(M1) and (M3).** On a connected node the steps of [15] are macro steps with branching number φ in the sense of Lemma 0 of [2], including the steps of several levels in [15, Lemmas 2 and 5]; a macro step has at most n + O(1) nodes, which Lemma 0 allows as a factor poly(n), and the comparisons of a solution with k are their leaves. Branching on an edge and the reductions of [15] are valid on any instance, so a node inside a macro step continues it even when its type graph is disconnected, and the split step is applied only at the roots of macro steps. The tail of the split step has budget at most k − 1/2, and its call tree has at most n^C (2 Σ_{i ≤ K} φ^i + φ^{k−1/2}) leaves, which is at most n^C φ^k for k ≥ 16, and the number of nodes is at most the depth plus one times the number of leaves. Every step lowers k by at least 1/2 or removes a vertex, so the depth is at most n + 2k. For k < 16 the budget stays below 16 in the whole call tree. A value call on H may keep the budget, but H is connected and every step on a connected node lowers k by at least 1/2, and a tail call lowers it by at least 1/2, so every path has at most 33 split steps, each with at most 33 calls, and the tree has n^{O(1)} nodes.
- **(M2).** For k ≥ 16 a value call has budget at most k/2, so log B(y) ≤ (1/2) log B(v). For k < 16 a value call has constant measure, which the term C log n covers.

Theorem 1 of [2] then gives √(φ^k) · poly(n) = O(1.2721^k) · poly(n). A solution comes by self-reduction.

## 5. Mixed Dominating Set: Theorem 5

Both algorithms of [18] are search trees whose nodes do polynomial work, with polynomial leaves. Isolated vertices are put into the solution first, which lowers k, so the graph has none.

- **Parameter k [18, Theorem 8].** Reduction and branching rules build the sets D_f and P_f of a nice solution with a measure l ≤ 2k, and when no rule applies the solution is completed optimally in polynomial time [18, Lemma 10]. The tree has at most 1.8734^l · poly(n) nodes, so the walk of [3] runs in time 1.8734^{l/2} · poly(n) ≤ 1.8734^k · poly(n). A leaf is marked if its completion has size at most k.
- **Parameter n [18, Theorem 7].** The first step lists all minimal vertex covers. As a tree, it takes a vertex v of minimum degree in the remaining graph and has one child for each u ∈ N[v], with u put into an independent set and N[u] removed. Every child removes at least deg(v) + 1 vertices, so the tree has O*(3^{n/3}) nodes, and every maximal independent set is a leaf, so every minimal vertex cover is the complement of a leaf. Each leaf is the root of the tree of the second step, with at most 1.3252^n · poly(n) nodes [18, Section 4], whose leaves are completed as follows, with repairs to [18, Lemma 8]. Let S = P_f ∪ P′_f. The leaf takes D_f and |S| − ν(G[S]) edges of G that cover S, a maximum matching of G[S] and one edge of G at each remaining vertex of S, where ν is the matching number. Since C ⊆ D_f ∪ P_f and V \ C ⊆ P′_f ∪ N(D_f) at a leaf, this is a mixed dominating set, and at a leaf consistent with an optimal nice solution D ∪ M its size is at most |D| + |M|, since M covers P ⊇ S. Every leaf therefore yields a mixed dominating set, so a leaf is marked if its solution has size at most k. The combined tree has O*(3^{n/3} · 1.3252^n) nodes, and the walk of [3] gives time √(3^{n/3} · 1.3252^n) · poly(n) = O(1.3825^n), with a factor log n for the search over k.

The completion of [18, Lemma 8] uses a minimum edge cover of G[S], which need not exist at a leaf consistent with an optimal solution: for the complete bipartite graph K_{2,4} with parts {u, w} and {z₁, … , z₄}, the leaf D_f = {u}, P_f = {w} has S = {w}, while the optimum {u} with the edge wz₁ has size 2. This hints at a possible gap in the proof of Lemma 8 of [18]; the completion above keeps its bound 1.912^n. The vector of rule B6 of [18, Section 4] has root 1.3006, a little above the printed 1.3001; the largest root, 1.3252 of rule B5, is unchanged.

## 6. Feedback Vertex Set in Tournaments: Theorem 6

**The classical algorithm** [19]. A kernel leaves O(k³) vertices. A family X of 2^{O(k/log k)} pairs (M, P), listed in polynomial space, contains for every solution H a pair with M ∩ H = ∅ and P ⊆ H [19, Lemma 5]. For each pair, a polynomial reduction gives an instance of d-Feedback Vertex Cover on a mixed multigraph with blocks of at most d = 2 log⁴ k vertices [19, Lemma 6]. Its search tree branches on a vertex v with at least two undirected neighbours: v is deleted (k drops by 1, n by 1), or all its undirected neighbours are deleted and v is contracted (k drops by at least 2, n by at least 3) [19, Lemma 9]. A node where no such vertex is left has s ≤ k disjoint undirected edges, and the minimization of [19, Lemma 7] decides it: it splits the vertices by the partition of [19, Lemma 10], with at most s/2 + d crossing edges, and takes the minimum over all subsets C of the crossing edges of the number of crossing edges plus the optima of two independent instances with at most s/4 + d² edges each; components are solved separately and instances with at most d edges by brute force in time 2^{O(d²)}. The directed arcs that cross the partition all go forward between blocks, so they lie on no cycle and the two sides are independent. Classically this takes 2^{2s/3} · 2^{O(d² + d log s)} · poly(n).

**Quantum leaf.** The minimization is run as nested quantum minimum finding [20] over C, with the two optima computed by recursive calls, for D = 3 levels; below them the classical minimization runs reversibly [21] in time T^{1+ε}, with ε = 1/10. Each recursive value is computed by O(k) parallel copies and their minimum, which brings the error of a comparison below the inverse of the number of comparisons, and the copies are uncomputed, so the workspace stays polynomial at constant depth. The time is Q(s) ≤ 2^{s(1/3 + η)} · 2^{O(d²)} · poly(n) with η = (1 + 2ε)/(3 · 4^D) = 1/160, since the square roots 2^{(s_l/2 + d)/2} of the search spaces multiply along a path and the leaf costs 2^{(1+ε) 2 s_D/3} with s_D ≤ s/4^D + 2d².

**The walk.** For each s₀ = 0, …, k, the walk of [3] runs on the tree of [19, Lemma 9] cut off at budget s₀: a node with budget below s₀ is an unmarked leaf, and a node where the branching stops with s₀ undirected edges is marked if the quantum leaf finds a solution within its budget. Every stopping node with s₀ edges has budget at least s₀, so it lies in the cut tree, which has O(φ^{k − s₀}) nodes. Each step of the walk evaluates the marking with error below the inverse square of the number of steps, since errors in amplitude add up, so the run takes φ^{(k − s₀)/2} · Q(s₀) · poly(k). Since 2^{1/3 + η} = 1.2654 < √φ, the largest term is the one with s₀ = 0, and the sum over s₀ and over the pairs of X is φ^{k/2} · 2^{O(k/log k)} · poly(k), after the kernel in time poly(n). In terms of n the tree has the vector (1, 3), so its cut at n₀ vertices has O(ρ^{n − n₀}) nodes, and a stopping node with n₀ vertices has at most n₀/2 undirected edges; with 2^{(1/3 + η)/2} = 1.1249 < √ρ, the time is ρ^{n/2} · 2^{O(n/log n)}; the kernel only lowers n.

## 7. Lean

`lean/FptBranching.lean` proves, with only the standard axioms (`lean/axioms.txt`):

- `matching_le_fractional`: a matching of size m, given by 2m distinct endpoints, forces every nonnegative fractional vertex cover to have weight at least m.
- `transversal_excess`, `transversal_cost`: the excess of the transversal reduction is at most k, and a cost C · 1.5214^μ is then at most C · 1.5214^k.
- `kvd_excess`, `kvd_budget`, `half_excess_base`, `half_cost`: the arithmetic of the budget step, and an excess of at most k/2 gives C · 1.2335^k.
- `walk_base_k`, `walk_base_half`, `base_half_sq`: 2.3146 < 1.5214², 2.3146 < 1.2335⁴ and 1.5214 ≤ 1.2335².

Lean 4 v4.36.0-rc1 with Mathlib at revision d875a8de5222f62cf1c2fafc7984588adadc990a. Run `lake exe cache get` and then `lake build` in `lean/`.

Not formalized: the search trees of [1] and [15], the split step of Section 4, the walk of [3], the reductions of [1] and [4], and for the problems of Theorem 2 the two inequalities vc(G′) ≤ |M| + |O| and vc*(G′) ≥ |M| + |O|/2 and Lemma 22 of [1].

## 8. Measurements

`sim/bases.py` recomputes the root 2.314596 of the vectors of rules B5 and B6 of [1], checks the printed bases in exact arithmetic on the recurrence of the walk, and recomputes the implied bases from the root φ² of the tree of [1, Theorem 1]. Run it with `python bases.py` in `sim/`. It exits nonzero on a failed check. `sim/bases2.py` checks the bases of Theorem 3 and of the implied baselines in exact arithmetic, each the square root of the classical base rounded up at the fourth decimal, and checks that the bases for d = 3 to 6 lie below the quantum bounds for d-Hitting Set of [13]. `sim/cluster.py` checks by brute force over all partitions, on 321 random disconnected weighted graphs with up to 7 vertices, that V is additive over the components of the type graph as in Section 4, that V(H) ≥ 1/2 for a component that is not a clique of edges, and that both forms of the split step, with the removal of clique components, decide V(G) ≤ k; it checks the leaf bound of the split step for k ≥ 16 and the bases √φ ≤ 1.2721 and √1.76 ≤ 1.3267 in exact arithmetic. `sim/mds.py` recomputes the roots of all branching vectors of [18, Sections 4 and 5] in exact arithmetic, checks on 300 random graphs that the tree of the first step of Section 5 reaches every maximal independent set with at most (n + 1) · 3^{n/3} nodes, checks by brute force that the completion of Section 5 gives a mixed dominating set at every leaf with U empty and that the best such leaf over all minimal vertex covers is optimal, on 73 random graphs without isolated vertices with up to 6 vertices and on K_{2,4}, and checks 1.3825^6 ≥ 3 · 1.3252³. `sim/bookkeeping.py` checks the bookkeeping by brute force over all partitions on random weighted instances with zero-edges and forbidden pairs, up to 6 vertices: for every edge, V equals the minimum over forbidding and merging of the parameter decrease plus V of the child, with the join rules of [15]; removing a clique component lowers V by half its zero-edges to the rest; and V = z/2 when the type graph is a union of cliques. It also checks the polynomial cases of [15, Lemma 5] with zero-edges: a clique minus one pair, by a minimum cut, and Kq * H for H a 5-cycle, three isolated vertices or two disjoint edges, by the best partition of H with Kq joined to a largest cluster.

`sim/tfvs.py` checks the exponents of Theorem 6 in exact rational arithmetic: the roots φ and ρ, 2^{1/3 + η} < √φ and 2^{(1/3 + η)/2} < √ρ for D = 3 and ε = 1/10, the exponent of the nested minimization on the integer recursion s_{l+1} = s_l/4 + d² for s up to 2 · 10⁵ and d up to 64, that the maximum over s₀ and n₀ of the combined exponent is at 0 for k up to 300, the node count of the cut (1, 2) tree, the baselines √2 and √1.6740 rounded up, and the leaf count 2^{2s/3} of the classical recursion. Run it with `python tfvs.py` in `sim/`.

## 9. Limits

- The search tree of [1], the safeness of its rules and its analysis are used as stated, as are its reductions and those of [4]. The same holds for the trees of [5] to [12], [15] and [18]; their case analyses are used as stated.
- The polynomial factor of the walk is not given explicitly, and there is no gate count.
- Theorem 6 uses [19, Lemmas 5, 6, 7, 9 and 10] as stated, including the bound of [19, Lemma 10] on the crossing and remaining edges; the factors 2^{O(k/log k)} and 2^{O(n/log n)} are absorbed into 1.2721^k and 1.2107^n only for large k and n.

## References

1. D. Lokshtanov, N. S. Narayanaswamy, V. Raman, M. S. Ramanujan, S. Saurabh. Faster parameterized algorithms using linear programming. ACM Transactions on Algorithms, 2014. arXiv:1203.0833.
2. Vertex Cover and Independent Set with a quantum algorithm. [quantum-vertex-cover](../quantum-vertex-cover/).
3. A. Montanaro. Quantum-walk speedup of backtracking algorithms. Theory of Computing 14, 2018. arXiv:1509.02374.
4. Y. Iwata, K. Oka, Y. Yoshida. Linear-time FPT algorithms via network flow. SODA 2014. arXiv:1307.4927.
5. D. Tsur. Faster parameterized algorithm for Cluster Vertex Deletion. arXiv:1901.07609.
6. A. Boral, M. Cygan, T. Kociumaka, M. Pilipczuk. Fast branching algorithm for Cluster Vertex Deletion. arXiv:1306.3877.
7. K. Iwaide, H. Nagamochi. An improved algorithm for parameterized edge dominating set problem. Journal of Graph Algorithms and Applications 20(1), 2016.
8. M. Xiao, T. Kloks, S.-H. Poon. New parameterized algorithms for edge dominating set. arXiv:1104.4160.
9. R. Červený, O. Suchý. Generating faster algorithms for d-Path Vertex Cover. arXiv:2111.05896.
10. D. Tsur. Parameterized algorithm for 3-path vertex cover. arXiv:1809.02636.
11. D. Tsur. An O*(2.619^k) algorithm for 4-path vertex cover. arXiv:1811.03592.
12. D. Tsur. l-path vertex cover is easier than l-hitting set for small l. arXiv:1906.10523.
13. 3-Hitting Set and d-Hitting Set with a quantum algorithm. [quantum-hitting-set](../quantum-hitting-set/).
14. Quantum monotone local search. [quantum-monotone-local-search](../quantum-monotone-local-search/).
15. S. Böcker. A golden ratio parameterized algorithm for Cluster Editing. Journal of Discrete Algorithms, 2012.
16. S. Böcker, P. Damaschke. Even faster parameterized cluster deletion and cluster editing. Information Processing Letters, 2011.
17. A. Jeļisejevs. Parametrizētu algoritmu paātrinājumi kvantu datoram. Bachelor's thesis, University of Latvia, 2021. https://dspace.lu.lv/handle/7/55878. The bounds are as stated in its abstract.
18. L. Dublois, M. Lampis, V. Th. Paschos. New algorithms for Mixed Dominating Set. Discrete Mathematics and Theoretical Computer Science 23(1), 2021. arXiv:1911.08964.
19. M. Kumar, D. Lokshtanov. Faster exact and parameterized algorithm for Feedback Vertex Set in Tournaments. STACS 2016. arXiv:1510.07676.
20. C. Dürr, P. Høyer. A quantum algorithm for finding the minimum. arXiv:quant-ph/9607014.
21. C. H. Bennett. Time/space trade-offs for reversible computation. SIAM Journal on Computing 18(4), 1989.
22. L. K. Grover. A fast quantum mechanical algorithm for database search. STOC 1996.
23. M. Dom, J. Guo, F. Hüffner, R. Niedermeier, A. Truß. Fixed-parameter tractability results for feedback set problems in tournaments. CIAC 2006.
24. S. Gaspers, M. Mnich. Feedback vertex sets in tournaments. arXiv:0905.0567.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean files, and to draft the text.
