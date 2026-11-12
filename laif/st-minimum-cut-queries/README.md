# Quantum query complexity of s-t minimum cut on simple graphs

Written 5 Nov 2026.

## Result

Let G be a simple undirected graph with n vertices and m edges, let s and t be two vertices, and let f = λ_st(G). In the adjacency list model one can query the degree of a vertex and the name of its i-th neighbour. The previous upper bound is Õ(√m n^{5/6}), so Õ(n^{11/6}), by [1]. The previous lower bound in this model is Ω(n), from connectivity [2].

**Theorem 1 (lower bound).** Computing λ_st on dense simple graphs needs Ω(n^{3/2}) adjacency list queries, with lists in arbitrary order. With weights in {1, τ}, 1 ≤ τ ≤ n/4, it needs Ω(n^{3/2}√τ).

**Theorem 2.** λ_st and a minimum s-t cut take Õ(√(mn) + n (mf)^{1/4}) adjacency list queries. Since f ≤ n and m ≤ n², this is Õ(n^{7/4}).

**Theorem 3 (high minimum degree).** If G has minimum degree δ ≥ 111√(2f), then Õ(√(mn) + n√(mf)/δ) adjacency list queries suffice, and Õ(n^{3/2}(1 + √(nf)/δ)) adjacency matrix queries. So for δ = Ω(n) the complexity is Õ(n^{3/2}), which matches Theorem 1 up to polylogarithmic factors.

| Graphs | Previous best bound | This folder |
|---|---|---|
| m ≥ n^{2/3} f | Õ(√m n^{5/6}) [1] | Õ(√(mn) + n (mf)^{1/4}) |
| All, worst case over m and f, taking the better of the two bounds | Õ(n^{11/6}) [1] | Õ(n^{7/4}) |
| Minimum degree Ω(n) | Õ(n^{11/6}) [1] | Õ(n^{3/2}), tight |
| Dense, lower bound in the list model | Ω(n) [2] | Ω(n^{3/2}) |

Below m = n^{2/3} f, the bound of [1] is the smaller one: at m = n^{3/2} and f = n it is n^{19/12} against n^{13/8}. The bounds concern the value and a minimum cut. Computing a maximum flow in o(m) queries remains open, as in [1].

The algorithm builds on the contraction scheme of [1], which goes back to [3]. Our contribution: the contraction is repeated without new queries until it is stable, the flow has minimum cost for a cost that counts the unknown edges, and low degree vertices are read first.

## Proof of Theorem 1

Take the family of [`minimum-cut-array-queries`](../minimum-cut-array-queries/), Theorem 1, with s ∈ A and t ∈ B. The shore A ∪ C separates s and t and has weight 2|x|, and every cut has weight at least 2|x| in the range of Hamming weights used there. So λ_st = 2|x|, and the counting bound of that folder applies. The family has minimum degree about n/2. ∎

## Algorithm for Theorem 2, with a parameter D

0. **Estimate.** Read all n degrees, which gives m. Compute a 1/3-cut sparsifier of G with Õ(√(mn)) queries [4], and from it a value f̂ with f ≤ f̂ ≤ 2f. If f̂ = 0, output the component of s and stop. Let D = (m f̂)^{1/4}. If D < 111√f̂, then m = O(n), and reading everything costs O(√(mn)).
1. **Peel.** While some vertex has fewer than D neighbours in the remaining graph, read its list and remove it. Let K be what remains, so G[K] has minimum degree at least D. Let E_L be the edges with an endpoint outside K. They are now known. The peeled lists have total length at most 2nD, since each removal deletes fewer than D edges and each edge lies on two lists.
2. **Sparsify.** Let ε = min{1/3, D/(128 √(n f̂))}. Compute an ε-spectral sparsifier H_K of G[K] with Õ(√(mn)/ε) queries, as described below. Let H = H_K ∪ E_L. It is an ε-cut sparsifier of G. Edges of H_K have cost 1, and edges of E_L have cost 0. If ε < √(n/m), read everything instead, at cost m ≤ √(mn)/ε.
3. **Contract, with no queries.** From P = singletons, repeat: compute a maximum s-t flow F of minimum cost in H/P, with value f_H. Let k = 4ε f_H. Take a k-strong partition of the residual graph (H/P) − F and coarsen P by it. Stop when P is stable.
4. **Learn.** Find with Grover search all edges of G[K] between different parts of P, with Õ(√(mC)) queries, where C is their number. Now G/P is known. Solve on it.

**The sparsifier.** Use Algorithm 3 of [4] on the lists of G, with weight 0 on E_L. Weight 0 is the mechanism of [4, Section 5.2] for forbidden edges. An edge e is kept with probability p_e = min(1, c R̃_e log(n)/ε²) and gets weight 1/p_e, where R̃_e estimates the effective resistance R_e in G[K] within a constant factor [4, Theorem 10]. The cost is Õ(√(mn)/ε) [4, Theorem 11].

An edge at a vertex of degree d has R_e ≥ 1/d, so R_e ≥ 1/n. Hence every weight in H_K is at most W := max{1, ε²n}, once c log n ≥ 2. The p_e have O(log n) bits, so all weights of H are rational with a common denominator L.

## Proof of Theorem 2

**Safety.** Let X be a minimum s-t cut of G, and suppose P respects every such cut. Then w_{H/P}(∆X) ≤ (1 + ε) f and F carries at least f_H across ∆X. Since f_H ≥ (1 − ε) f and f > 0, the residual weight of ∆X is at most (1 + ε) f − f_H < 4εf_H = k. So X cannot split a k-strong part. By induction, every P respects every minimum s-t cut, so λ(G/P) = f, and a minimum cut of G/P is one of G.

Fix the stable P. Let b be the number of parts with at least D/2 vertices of K, the big parts. So bD ≤ 2n. Let S be the vertices of K in the other parts, s = |S|, and let t_K ≤ b + s be the number of parts meeting K.

**Lemma A.** Residual core edges between parts have total weight at most k(t_K − 1).

Stability means all residual edges between parts are k-weak, and they stay k-weak in the subgraph of residual core edges. By [1, Lemma 7], from [5], Σ_e w_e/k_e ≤ t_K − 1 on that subgraph, with all strengths k_e < k.

**Lemma B.** The flow F on core edges between parts has total weight at most 2b f_H + 2s√(W f_H).

Rescale all weights by L. The bound is homogeneous, and flows now move in steps δ = 1/L. The minimum cost is reached by successive shortest paths, so it equals δ Σ_j d_j, where d_j is the s-t distance in the residual network when jδ units remain. Fix j, let π be the distances from s, and let r = jδ. A residual arc from u to v has π(v) ≤ π(u) + cost. For 0 ≤ i < d_j, consider the cut {π ≤ i}. Arcs of cost 0 or −1 cannot leave it, so all leaving arcs have cost 1 and go from level i to level i + 1. They carry at least r. Each big part spoils at most two values of i. For any other i the arcs join vertices of S, and each pair of vertices has weight at most W, so r ≤ W c_i c_{i+1}, where c_i counts the vertices of S at level i. By AM-GM, √r ≤ √W (c_i + c_{i+1})/2. Summing over the levels, with Σ_i c_i ≤ s, gives d_j √r ≤ 2b √r + s√W. Summing over j, with Σ_{j ≤ N} j^{−1/2} ≤ 2√N and f_H = Nδ, gives the claim.

**Lemma C.** C ≤ (k(t_K − 1) + 2b f_H + 2s√(W f_H))/(1 − ε).

The crossing weight of core edges in H is the sum of Lemmas A and B. Summing the sparsifier bound for the cuts around the parts gives the same bound for G[K].

**Lemma D.** A vertex of S has at least D neighbours in K and fewer than D/2 in its part. So sD/4 ≤ C.

**Combination.** Since f_H ≤ (4/3) f, f ≤ f̂, f ≤ n and D ≥ 111√f̂, the choice of ε gives k ≤ D/24 and √(W f_H) ≤ D/96. With ε ≤ 1/3, Lemmas C and D give C ≤ (D/8) b + 6 b f_H ≤ n/4 + 12 n f_H/D. So C = O(n(1 + f/D)).

**Cost.** Õ(nD + √(mn)/ε + √(mn(1 + f/D))). Since D ≤ n, √(mnf/D) ≤ n√(mf)/D, so the total is Õ(nD + √(mn) + n√(mf)/D). The choice of D gives Theorem 2. ∎

**Theorem 3.** Take K = V and D = δ, or a factor 2 estimate of δ. In the list model the degrees give δ. In the matrix model, approximate counting gives the estimate with Õ(n^{3/2}) queries, and each row is a list with weight 0 at the non-edges, so m becomes n² in the sparsifier and in the search. The same proof applies. ∎

## Machine check

`lean/StCut.lean` checks the deterministic part of the proof, with Lean 4.36.0-rc1 and Mathlib revision `d875a8de5222f62cf1c2fafc7984588adadc990a`. It contains no `sorry`, and its theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

| Step | Theorem |
|---|---|
| Flow across a level cut, on a residual network with flow conservation and potentials | `level_capacity`, `level_pairs` |
| Length of a shortest path | `rest_path_length`, `good_levels`, `path_length` |
| Lemma B | `flow_cost_graph` |
| Summing cuts around the parts, Lemma C | `sum_partCut`, `crossing_sparsifier` |
| Lemma D, number of big parts and of parts meeting K | `small_vertices`, `big_parts`, `parts_meeting` |
| Choice of ε and D, safety inequality | `parameters`, `safety_margin` |
| Peeling | `peel_total` |
| C ≤ n/4 + 12 n f_H/D | `crossing_edges` |

**Hypotheses of these statements.** Successive shortest paths: `flow_cost_graph` takes the residual flows and potentials of each step, and the total cost δ Σ_j d_j, as hypotheses. The sparsifier: `crossing_sparsifier` takes the lower bound on the cuts as a hypothesis, and `parameters` takes the bound on W. Lemma A enters `crossing_edges` through the hypothesis `hres`.

**Not machine-checked:** the quantum algorithms of [4], Grover search, the bound of [1, Lemma 7], the deduction of the weight bound from effective resistances, the query counts, and Theorem 1 in its s-t form. The counting bound behind Theorem 1 is checked in [`minimum-cut-array-queries`](../minimum-cut-array-queries/).

The script `sim/check_contract.py` tests safety and Lemmas A, B and D on graphs with n = 150, using a sampled graph with weight 2 in place of a sparsifier. Its docstring states the limits.

## Open

- Whether Õ(n^{7/4}) can be lowered, against the lower bound Ω(n^{3/2}).
- Bounds for moderately dense graphs, below m = n^{2/3} f.

## Related work

[6] gives friendly cut sparsifiers, with contracted graphs of Õ(n√w) edges, in the time model. [7] gives deterministic Õ(n^{5/3}) cut queries for s-t maximum flow on simple graphs. [8] contracts simple graphs of minimum degree δ to Õ(m/δ) edges for global minimum cuts. [9, Theorem 8.14] gives Ω(n^{3/2}) for directed s-t minimum cut in the adjacency matrix model.

## References

[1] S. Apers, A. Auza, T. Lee. A sublinear query quantum algorithm for s-t minimum cut on dense simple graphs. arXiv:2110.15587.

[2] C. Dürr, M. Heiligman, P. Høyer, M. Mhalla. Quantum query complexity of some graph problems. SIAM J. Comput. 35(6), 2006.

[3] A. Rubinstein, T. Schramm, S. M. Weinberg. Computing exact minimum cuts without knowing the graph. ITCS 2018.

[4] S. Apers, R. de Wolf. Quantum speedup for graph sparsification, cut approximation and Laplacian solving. arXiv:1911.07306v4.

[5] A. Benczúr, D. Karger. Randomized approximation schemes for cuts and flows in capacitated graphs. SIAM J. Comput. 44(2), 2015.

[6] A. Abboud, R. Krauthgamer, O. Trabelsi. Friendly cut sparsifiers and faster Gomory-Hu trees. arXiv:2110.15891.

[7] A. Anand, T. Saranurak, Y. Wang. Deterministic edge connectivity and max flow using subquadratic cut queries. arXiv:2410.18704.

[8] K. Kawarabayashi, M. Thorup. Deterministic edge connectivity in near-linear time. J. ACM 66(1), 2018.

[9] A. Auza. PhD thesis, University of Technology Sydney. https://opus.lib.uts.edu.au/bitstream/10453/171481/1/thesis.pdf

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
