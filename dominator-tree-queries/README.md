# Dominator trees and strong connectivity structure with quantum queries

Sebastian Senge, Independent Researcher. Written 4 Nov 2026.

**Setting.** G is a directed graph with n vertices, m edges, and a root r. Vertex d **dominates** w if every path from r to w contains d. The **dominator tree** gives each reachable w ≠ r its immediate dominator idom(w). A **strong bridge** is an edge, and a **strong articulation point** a vertex, whose removal increases the number of strongly connected components.

Query models. Matrix: a query (u, v) returns whether uv is an edge. Array: out-lists and in-lists are both available, and a query returns one list entry; degrees are known.

| | Problem | Matrix, quantum | Array, quantum | Classical, matrix | Status |
|---|---|---|---|---|---|
| Thm 1 | Depth-first search, strongly connected components (known, see below) | O(n^{3/2}) | O(√(nm) log n) | Θ(n²) | Correctness and search counts in Lean; query count is a claim |
| Thm 2 | Dominator tree | Θ(n^{3/2}) | O(√(nm) log n) | Θ(n²) | Correctness in Lean; lower bound in Lean, assuming DHHM Thm 23; query count is a claim |
| Thm 3 | Bridges of a flow graph, strong bridges, strong articulation points | Θ(n^{3/2}) | O(√(nm) log n) | Θ(n²) | Reductions and gadgets in Lean; lower bounds assuming DHHM Thm 23 and classical connectivity; query count is a claim |

The lower bounds are unconditional. Upper and lower bounds match in the matrix model. The explicit algorithm below has an extra log n, and the log-free bound comes from Section 2's remark. In the array model a random scan order should give O(√(nm log n)) through Beigi and Taghavi's Theorem 4(ii); I did not simulate that. In the array model I have no matching lower bound: DHHM's Ω(√(nm)) for strong connectivity (Theorem 22) is for out-lists only, and having in-lists as well may make the problem easier. Classical array cost is O(m) by Lengauer-Tarjan and is not separately bounded below here.

This is a minor result.

**Prior work, and how new this is.** This is a modest result. Quantum depth-first search with this cost is DHHM Theorem 12 (quant-ph/0401091), with the same stack and the same sum as Lemma 1. DHHM also say their algorithms can output strongly connected components, and Beigi and Taghavi (arXiv:1905.13095, Proposition 10) give DFS, topological sort and components at O(n^{3/2}). I found no paper on quantum dominators, strong bridges or strong articulation points, from about 25 arXiv queries and web searches, but those searches also failed to surface the DFS results above, so that evidence is weak. The matrix results are a routine corollary of Lin and Lin's O(√(TG)) theorem (arXiv:1410.0932) plus Lengauer-Tarjan. So the fair claim is: not stated in the papers I found, and easy once stated.

## 1. Depth-first search

**DFS.** Keep a stack. At the top vertex v, search its entries for an unvisited out-neighbour. If one is found, push it. Otherwise pop v. Any choice of unvisited neighbour gives a valid depth-first search, so no specific order is needed. Which vertices are unvisited is classical data.

**Lemma 1 (DHHM Theorem 12).** The searches cost O(√(nm) log n) in the array model and O(n^{3/2} log n) in the matrix model.

*Proof.* A vertex v with c_v tree children has c_v + 1 searches. When the k-th search runs, at least c_v − k + 1 unvisited out-neighbours remain if it will succeed, so with N = deg(v) successive searches cost O(√(N/(c_v − k + 1))) in expectation, given what is known when each starts. A search that makes several neighbours visited does no harm, since later children are by definition still unvisited. They sum to O(√(c_v N)), and the final failed search costs O(√N). So the total is O(Σ_v √((c_v + 1) deg v)) ≤ O(√(Σ(c_v + 1) · Σ deg v)) = O(√(nm)) by Cauchy-Schwarz, since Σ c_v ≤ n. In the matrix model N = n and the same sum is O(n^{3/2}). There are at most 2n searches, so error 1/(cn) each, for a large enough constant c over the whole algorithm, costs a factor O(log n), and truncating costs a constant. ∎

**Theorem 1.** Strongly connected components follow by Kosaraju: DFS on G over all roots, then DFS on the reverse graph, with roots in decreasing finish time. Each tree of the second round is one component. Both rounds have the cost of Lemma 1, because visited vertices are excluded from all searches and each vertex is pushed once.

## 2. Dominators

Number vertices by DFS preorder, and identify a vertex with its number. Lengauer and Tarjan (1979) define the semidominator sdom(w), and prove (Theorem 4 there):

    sdom(w) = min( {v : (v, w) ∈ E, v < w} ∪ {sdom(u) : u > w, and (v, w) ∈ E for some v having u as a tree ancestor} ).

**Algorithm.** Process w in decreasing preorder. Keep the forest of processed vertices, with their parent links and semidominators. For a predecessor v of w define

    f_w(v) = v if v < w, and otherwise the smallest sdom(u) over u on the forest path from v to the root of its forest tree; f_w(v) = ∞ if v is unreachable.

f_w(v) is computed from classical data with no queries. By the formula above, sdom(w) is the minimum of f_w over the predecessors of w. Find it by Dürr-Høyer minimum finding on the entering entries of w.

Once sdom is known, the dominator tree follows with no queries, since Lengauer and Tarjan's Theorems 2 and 3 use only the DFS tree and sdom. The code uses the equivalent form of Georgiadis, Tarjan and Werneck (2006, Lemma 3): idom(w) is the nearest common ancestor of parent(w) and sdom(w) in the dominator tree so far, in preorder.

**Theorem 2.** The dominator tree costs O(√(nm) log n) in the array model and O(n^{3/2} log n) in the matrix model.

*Proof.* DFS by Lemma 1. Minimum finding at w costs O(√(deg⁻ w)), and with error 1/(cn) a factor O(log n). Σ_w √(deg⁻ w) ≤ √(nm) by Cauchy-Schwarz. In the matrix model each costs √n. The f_w depend only on classical data fixed during that search, so the oracle for minimum finding is well defined. ∎

**Remark (no log factor in the matrix model).** Lin and Lin's Theorem 9 gives O(√(TG)) queries for a classical algorithm with T queries and at most G wrong guesses. DFS has T ≤ n² and G ≤ n, guessing "no edge". For each w, scan candidates by increasing f_w and stop at the first edge, so G ≤ 1 per w. The bridge test also has G ≤ 1 per vertex. So T = O(n²), G = O(n), and the bound is O(n^{3/2}). An independent run counted this decision tree up to n = 128: T/n² at most 0.81, G/n at most 1.98, no wrong trees. The algorithm that this theorem gives is a span program, so `sim/dom.py` keeps the explicit Grover form with its log factor.

## 3. Bridges and strong connectivity

**Lemma 2 (standard).** Let v ≠ r be reachable. Edge (u, v) is on every path from r to v iff u = idom(v) and v dominates every reachable predecessor w ≠ u of v.

*Proof.* Suppose (u, v) is on every path. Cut any path at its first arrival at v. The prefix contains (u, v) and contains v only at its end, so its last edge is (u, v). Hence u strictly dominates v. Let d ≠ u be another strict dominator of v, and Q a path from r to u. If Q avoids v, then Q followed by (u, v) reaches v, so d is on Q. If Q contains v, its first arrival at v is through u, and d lies on that prefix before u, so again d is on Q. So every other strict dominator of v dominates u, which gives u = idom(v). If w ≠ u is a reachable predecessor of v and some path from r to w avoids v, extending it by (w, v) avoids (u, v), a contradiction. So v dominates w.

Conversely, on any path from r to v take the first arrival at v, by edge (w, v). If w ≠ u, then v dominates w, so the path reached v before w, a contradiction. So w = u. ∎

**Bridge test.** For each reachable v, search the in-entries of v for a reachable predecessor w ≠ idom(v) that v does not dominate. Dominance is read from entry and exit numbers of the tree, with no queries. Cost Σ_v √(deg⁻ v), so it is dominated by Theorem 2.

**Lemma 3 (Italiano, Laura, Santaroni 2012; I read this through later papers citing it).** Let G be strongly connected, s ∈ V. An edge is a strong bridge iff it is a bridge of the flow graph of G from s, or of the reverse graph from s. A vertex v ≠ s is a strong articulation point iff it dominates some other vertex in one of those two flow graphs.

*Proof.* G − e is strongly connected iff every vertex is still reachable from s and can still reach s. That is the same as e being a bridge of neither flow graph. For v ≠ s, G − v is strongly connected iff every other vertex is reachable from s and can reach s avoiding v, which means v dominates no other vertex in either flow graph. ∎

**Theorem 3.** Compute the strongly connected components. Removing an edge or vertex only affects its own component: an edge between components changes nothing, and a vertex alone in its component reduces the count. Within each component C with |C| ≥ 2 pick s, and apply Lemma 3 with the searches restricted to C. Test s itself by two DFS runs on C − s, from any vertex and in both directions. Restricted searches run over the same lists, so sum over components: Σ_C √(n_C m_C) ≤ √(nm) in the array model, and Σ_C n_C √n = n^{3/2} in the matrix model. The number of calls is O(n), so the error per call is 1/(cn) as in Lemma 1. ∎

## 4. Lower bounds

**Quantum, matrix.** Connectivity needs Ω(n^{3/2}) queries (DHHM Theorem 23). Bidirecting an undirected graph gives a digraph with one query per query. Then all vertices are reachable from r iff the graph is connected, and the dominator tree shows the reachable set.

For strong bridges: to G, bidirected, add for each v ≠ v₀ a new vertex a_v with edges v₀ → a_v → v. If G is connected, all vertices form one component, and v₀ → a_v is a strong bridge, because its removal cuts a_v off. If v is in another component than v₀, then a_v is on no cycle, its removal changes no component, and v₀ → a_v is no strong bridge. So the output decides Connectivity on a graph of 2n − 1 vertices.

For strong articulation points: use two new vertices per v, v₀ → a_v → b_v → v, for 3n − 2 vertices in all. If v is connected to v₀, then removing b_v leaves a_v as its own component, and the count grows by one. Otherwise a_v, b_v are singletons, and removing b_v lowers the count.

For bridges of a flow graph: the gadget above does not work, since v₀ → a_v is always a bridge from v₀. Instead add a sink t_v for each v, with edge v → t_v, and root at v₀. Every vertex of the component of v₀ has this edge, and it is a bridge exactly when v is reachable, since it is the only way into t_v. So the output shows which vertices are connected to v₀.

**Classical, matrix.** Dominators: let r → u, r → x for x ∈ X, u → v for v ∈ V, with hidden bits on the pairs (x, v) ∈ X × V, and |X|, |V| = Θ(n). If v has no hidden in-edge, then idom(v) = u; otherwise idom(v) = r, since paths through u and x meet only at r. So the output computes OR on Θ(n²) bits, which needs Ω(n²) randomized queries. Bridges, strong bridges and articulation points: the gadgets above with classical Connectivity, which needs Ω(n²).

**Array model.** DHHM's Theorem 22 uses out-lists only, and in-lists do collapse their instance: every vertex but v₀ has in-degree 1, so one query per in-list recovers all bits. An AI review sketched a degree-fixing gadget that should give Ω(√(nm)) for these output problems with both lists, through Lee and Roland's strong direct product theorem (arXiv:1104.4468). I have not checked it, so I do not claim it.

## 5. Practical reading

`sim/check.log`: about 34 n^{3/2} oracle applications at budget 16 per search, so the quantum algorithm beats reading n² entries only above about n ≈ 1200. Budget 16 is close to its limit there: minimum finding fails about 5 times in 10,000 calls at N = 2048, in an independent run, and a real run would need a larger budget. The constant is almost all the fixed budget, as each minimum finding spends its budget before stopping. With the classical Lengauer-Tarjan on an array, O(m) on sparse graphs is cheaper at any realistic size: √(nm) · 34 is below m only for m/n above about 1100.

## 6. Measurements

`sim/check.py`: runs agree with networkx dominators, and with brute-force removal for flow-graph bridges, strong bridges and points, in both models, on random and layered graphs up to n = 80 (bridges and points up to n = 20). Fitted exponents in the matrix model are 1.50 at n ≤ 2048. Applications/√(nm) in the array model is flat at about 34. All in `sim/check.log`. A fixed budget cannot show the log factor, and the scaling part does not check answers. `sim/qiskit_check.py`: every search a circuit, 20 runs, 0 wrong, at most 4 qubits. The simulator's Grover law and the padded circuit differ when N is not a power of 2 (0.97 against 0.79 at N = 5, t = 1, j = 1), a constant-factor difference.

## 7. Limits

- Queries only. A gate count is not worked out.
- The results are a routine corollary of Lin and Lin's theorem plus Lengauer-Tarjan, in the matrix model. Depth-first search and strongly connected components are known.
- The explicit algorithm has an extra log n against the Θ(n^{3/2}) of the table. The log-free bound rests on the span program behind Lin and Lin's theorem, which is not simulated here.
- No matching lower bound in the array model.
- On sparse graphs a classical array algorithm at O(m) is cheaper at any realistic size.
- The review of these proofs was by an AI agent. No human has checked them.
- Searches for earlier work failed to surface some known results, so they are weak evidence.

## 8. Formal verification

`lean/` builds with `lake build` (Lean 4 v4.36.0-rc1, Mathlib `d875a8de`), with no `sorry` and no `axiom` declaration. `lake env lean Dominators/Axioms.lean` prints the axioms of 77 theorems: only `propext`, `Classical.choice` and `Quot.sound`.

| Part | Theorems |
|---|---|
| Lemma 2, the bridge test | `lemma2`, `dominates_iff_paths`, `onAllPaths_iff_paths`, `exists_idom`, `IsIdom.unique`, `isBridge_iff_test`, `isBridge_iff_cuts` |
| Lemma 3, Theorem 3's reduction | `lemma3_edge`, `lemma3_vertex`, `isSAP_self_iff`, `isStrongBridge_iff_mutual`, `isSAP_iff_separates`, `theorem3_edge`, `theorem3_vertex` |
| Depth-first search | `dfs_visited_iff`, `dfs_searches_le`, `dfs_stack_nil`, `forest_searches_le`, `run_stack_nil`, `dfs_isDfsTree` |
| Kosaraju | `kosaraju_correct`, `round1_order`, `kosaraju_same_iff` |
| Semidominators to dominators, proved and not assumed | `IsDfsTree.sdom_formula`, `IsDfsTree.sdom_key`, `IsDfsTree.idom_iff_nca`, `sdomTable_spec`, `nca_spec`, `idomOfTree_spec`, `dominators_correct`, `dominators_none_iff` |
| Cost sums | `lemma1_cauchy`, `lemma1_array`, `lemma1_matrix`, `sum_sqrt_inDeg_le`, `expected_search_sum`, `vertex_cost_le`, `partition_sum_le`, `partition_matrix_sum`, `union_error_le`, `runCharge_total`, `dfs_charge_array`, `dfs_charge_matrix`, `dominator_charge_total`, `minFind_calls_le`, `minFind_charge_le` |
| Gadgets | `sink_bridge_iff`, `sink_connected_iff`, `sb_bridge_iff`, `sb_strongConn`, `sb_isolated`, `sb_no_change`, `sb_connected_iff`, `sb_edge_always_bridge`, `sap_iff`, `sap_b_alone`, `sap_a_alone`, `sap_count_conn`, `sap_count_not`, `or_idom_no_edge`, `or_idom_edge`, `or_of_output` |
| Lower bounds | `dominators_lower_bound`, `bridges_lower_bound`, `strongBridges_lower_bound`, `saps_lower_bound`, `classical_bridges_lower_bound`, `classical_strongBridges_lower_bound`, `classical_saps_lower_bound`, `or_lower_bound`, `classical_dominators_lower_bound` |

**Assuming.** Named hypotheses in `lean/Dominators/Model.lean`: `DHHM_Thm23` for the four quantum lower bounds, `ClassicalConnectivity` for three classical ones, `BBHT` for `bbht_budget`, `DurrHoyer` for `durrHoyer_total`. The algorithm theorems assume only that the search and minimum-finding parameters meet exact specs, and enough fuel. `or_lower_bound` and `classical_dominators_lower_bound` assume nothing.

**Not formalized.** Quantum subroutines are not composed under classical control into one query algorithm, and the charge theorems bound sums of real numbers, so the overall upper bounds are claims. Search failure inside the depth-first search, past the arithmetic of `union_error_le`. Kosaraju's cost past its search count. Theorem 3 and the bridge test as code. The Lin-Lin remark, the Beigi-Taghavi remark, the array-model lower-bound discussion, and Sections 5 and 6. The idom step follows Georgiadis, Tarjan and Werneck, not Lengauer and Tarjan's link-eval forest.

## References

1. C. Dürr, M. Heiligman, P. Høyer, M. Mhalla. Quantum query complexity of some graph problems. quant-ph/0401091.
2. C. Y.-Y. Lin, H.-H. Lin. Upper bounds on quantum query complexity inspired by the Elitzur-Vaidman bomb tester. arXiv:1410.0932.
3. S. Beigi, L. Taghavi. Quantum speedup based on classical decision trees. arXiv:1905.13095.
4. T. Lengauer, R. E. Tarjan. A fast algorithm for finding dominators in a flowgraph. ACM TOPLAS 1(1), 1979.
5. L. Georgiadis, R. E. Tarjan, R. F. Werneck. Finding dominators in practice. J. Graph Algorithms and Applications 10(1), 2006.
6. G. F. Italiano, L. Laura, F. Santaroni. Finding strong bridges and strong articulation points in linear time. Theoretical Computer Science 447, 2012.
7. T. Lee, J. Roland. A strong direct product theorem for quantum query complexity. arXiv:1104.4468.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
