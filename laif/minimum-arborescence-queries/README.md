# Minimum-cost arborescence with quantum queries

Written 4 Nov 2026.

| | Problem | Quantum queries | Classical | Status |
|---|---|---|---|---|
| Thm 1 | Minimum arborescence | O(√(nm) log³ n), O(n^{3/2} log³ n) in the matrix model | Θ(m), Θ(n²) | Correctness and certificate in Lean; query sum in Lean, assuming DHHM Theorem 6; the error bound is a claim |
| Thm 2 | Lower bounds | Ω(√(nm)), Ω(n^{3/2}) | as above | Reductions in Lean; the bounds they reduce to are cited |
| Remark | Fewer logs, by another route | O(√(nm) log² n √(1 + log(m/n))) | | Claim |

This is a minor result, see "Prior work" below.

**Setting.** G = (V, E) is a directed graph with n vertices, m edges, integer weights w and a root r. A spanning arborescence is a parent function p on V \ {r} such that every vertex reaches r by following p, and every (p(v), v) is an edge. Its cost is the sum of w(p(v), v). The task is to output one of minimum cost, or report that none exists.

Query models. Matrix: a query (u, v) returns w(u, v) or ∞. Array: a query (v, i) returns the i-th entering edge of v and its weight. The in-degrees are known. The matrix model is treated below as the array model with m = n(n−1), where an absent edge has weight ∞.

**Theorem 1.** There is a bounded-error quantum algorithm with O(√(nm) log³ n) queries in the array model and O(n^{3/2} log³ n) in the matrix model.

**Theorem 2.** Let m ≥ n − 1. Any bounded-error quantum algorithm needs Ω(n^{3/2}) queries in the matrix model, and in the array model Ω(√(nm)) on families with Θ(m) edges, for m ≤ n²/2. Classical randomized algorithms need Ω(n²) and Ω(m). Below n − 1 edges no arborescence exists and the known in-degrees show it, at no queries.

So the quantum complexity is Θ̃(√(nm)) in that range and Θ̃(n^{3/2}), against the classical Θ(m) and Θ(n²). The gain is a factor √(m/n) up to logs: n² becomes n^{3/2} on dense graphs, and there is no gain at m = Θ(n). The array bound for n²/2 < m ≤ n(n − 1) is not worked out.

**Earlier work.** Theorem 1 is close to a corollary of known theorems, so this is a minor result. Fischer and Oshman (DISC 2019), using a variant of Lovász's parallel algorithm (FOCS 1985), solve directed MST in at most ⌈log₂ n⌉ iterations, each one a single-source shortest-path computation inside disjoint components. A virtual graph with one input query per virtual query fits that computation into Dürr, Heiligman, Høyer and Mhalla's shortest-path algorithm (quant-ph/0401091, "DHHM", Theorem 18), and that gives O(√(nm) log³ n), the bound of Theorem 1. We use log² n for Theorem 18, as in their Table 1. To our knowledge this reduction has not been stated before. It is a claim and is not in Lean, and `sim/check_fo.py` and `sim/check_virtual.py` test it on small instances.

DHHM settle undirected MST at Θ(√(nm)). The lists below take their idea from DHHM's Theorem 18, on a binary-counter partition. What this work still adds: an explicit single-pass Edmonds algorithm, a correctness proof and an output certificate checked in Lean, and the lower bounds written out. To our knowledge no query bound for arborescences has been stated before. The closest result is Kerger et al. (arXiv:2304.02825), in CONGEST-CLIQUE, using the same O(log n) contraction scheme.

## 1. The subroutine

**DHHM Problem 3, Theorem 6.** Given f: [N] → Z ∪ {∞}, a type function g: [N] → types, and d′, let e be the number of types and d = min(d′, e). Find I ⊆ [N] with |I| = d, with distinct types, such that for all j ∉ I and i ∈ I: if f(j) < f(i), then f(i′) ≤ f(j) for some i′ ∈ I with g(i′) = g(j). Bounded-error complexity O(√(dN)); error 2^{−k} costs a factor k (their Remark 1). We call this TopK. In the array model the source of an edge comes from the query that reads its weight, so one query gives both f and g, as in DHHM's own MST algorithm. If d′ > N/2 we read all N items, which costs N ≤ √(2d′N). By Lemma 3(c) K_G ≤ n − 2 before an exhaustion build, so d′ can reach about 2n, and the accounting charges K in any case. We skip the case N = 0.

**Lemma 1.** (a) If i ∈ I and g(j) = g(i), then f(i) ≤ f(j). So each entry is the minimum of its type. (b) If |I| < d′, or some entry has f = ∞, then every type with a finite value has a finite entry in I.

*Proof.* (a) If j ≠ i and f(j) < f(i), the spec gives i′ ∈ I of type g(j) = g(i) with f(i′) ≤ f(j). Types in I are distinct, so i′ = i, a contradiction. (b) If |I| < d′, then d = e, so every type occurs in I, and by (a) its entry is minimal, hence finite if the type has a finite value. If f(i) = ∞ for an i ∈ I, take j with f(j) finite. If j ∈ I we are done. Otherwise f(j) < f(i), and the spec gives a finite entry of type g(j). ∎

## 2. Edmonds' algorithm, path-growing form

A **node** is a vertex set: each single vertex is a node, and each contraction creates one. The current nodes (**containers**) partition V. The root stays a singleton and never selects. Each vertex has an offset y(v), initially 0. The reduced cost of (u, v) is w(u, v) − y(v).

    attached := {{r}}
    for v0 in V:
        a := container of v0; if a is attached, continue
        path := empty
        loop:
            e = (u, v) := cheapest edge entering a by reduced cost, with value c
            if there is none: report that no arborescence exists
            y_a := c;  add c to y(x) for all x in a;  in(a) := e
            b := container of u
            if b is attached: mark a and all of path attached; break
            if b is on path: a := contract(the part of path from b on, and a); drop that part from path
            else: push a on path; a := b

Each node selects at most once, so there are at most 2n − 1 selections and n − 1 contractions. Nothing above reads a weight except "cheapest edge entering a", which Section 3 provides.

**Expansion, no queries.** For a top container T ≠ {r}, assign a(T) := in(T). For a contracted node X with assigned a(X) = (u, v), let h be its child containing v, and assign a(h) := a(X) and a(c) := in(c) for every other child c. Output p(v) := source of a({v}).

**Lemma 2 (optimality).** If selection always returns a true minimum, the output is a minimum-cost arborescence and a report of none is correct.

*Proof.* A report of none is correct: a is a nonempty set without r and no edge enters it, while every arborescence has an edge entering each such set.

*Dual feasibility.* Every node X ≠ {r} that exists at the end or was contracted has selected. Fix an edge (u, v) with u ≠ v and v ≠ r, since a self-loop enters no set. Let X₁ ⊂ … ⊂ X_t be the nodes containing v and not u, in order, with X₁ = {v}. When X_i selects, y(v) = y_{X₁} + … + y_{X_{i−1}}, and (u, v) enters X_i. Minimality gives y_{X_i} ≤ w(u, v) − Σ_{j<i} y_{X_j}. For i = t this says

    w(u, v) ≥ Σ_{X : v ∈ X, u ∉ X} y_X.    (1)

*Sign.* If |X| ≥ 2, then y_X ≥ 0. Take the entering edge (u, v) that X selects. It also enters the child X′ containing v, and X′ has selected. Applying the inequality at X′ gives w(u, v) − y(v) ≥ 0 at that moment, and y_X is this value. Singletons may have any sign.

*Assignment.* By construction a(X) enters X for every node X ≠ {r}. Let A_X be the set of edges a({v}) over v ∈ X. Induction on the forest: A_X contains exactly one edge entering X, namely a(X), and from the head of a(X) every vertex of X is reachable inside A_X. For a singleton this is immediate. For X with children forming the cycle c₁ → … → c_k, where in(c_{i+1}) has its source in c_i: the edges of A_X entering any c_i are a(c_i). For c ≠ h, a(c) = in(c) has its source in X, because the source lies on the cycle. For h, a(h) = a(X) enters X. Reachability runs around the cycle from h, using the induction hypothesis in each child.

*Top level.* Attached nodes form a tree towards {r} in the sense that each top T has a(T) with source in a node attached earlier. A cycle cannot arise, since a path is attached only when it meets an attached node. So every vertex is reachable from r in the output, which is therefore an arborescence.

*Tightness.* Let e = (u, v) = a({v}), and let S be the highest node with a(S) = e. Then a(S) = in(S). The nodes containing v and not u are exactly those from {v} up to S, because if S is not top, then its parent contains u. Equality holds in the minimality step at S, so (1) holds with equality for e.

*Optimality.* Output cost = Σ_e Σ_{X entered by e} y_X = Σ_X y_X, since exactly one output edge enters each X. The sum runs over nonempty sets X without r. For any arborescence A, (1) gives cost(A) ≥ Σ_X y_X · |A ∩ δ⁻(X)| ≥ Σ_X y_X. The last step uses |A ∩ δ⁻(X)| = 1 for singletons, and ≥ 1 with y_X ≥ 0 for larger X. ∎

Finding the cheapest entering edge of a container C by plain minimum finding costs √(N(C)), where N(C) = Σ_{v∈C} deg⁻(v). When C grows one vertex at a time, this totals Θ(n²) in the matrix model. The family `chain` in `sim/instances.py` does this, and `sim/scaling.log` shows the fitted exponent 1.98.

## 3. Lists

Each container C ≠ {r} is partitioned into **groups**, at most one in each class, where the class of G is ⌊log₂|G|⌋. Each group has a budget K_G ≥ 1 and a list L_G. N(G) = Σ_{v∈G} deg⁻(v).

**Build(G, K).** Run TopK on the N(G) entering edges of G with error δ, with g(u, v) = u, d′ = K, f(u, v) = w(u, v) − y(v) if u ∉ C and ∞ otherwise. L_G is the set of returned finite entries, sorted by f. Mark L_G complete if |I| < K or some entry had f = ∞. Set K_G := K.

**Cheapest(C).** For each group G of C: discard the leading entries of L_G with source in C. If L_G is now empty and not complete, run Build(G, 2K_G). Return the entry of smallest current reduced cost among all heads, or none.

**Initial.** Every v ≠ r starts with group {v} and Build({v}, 1).

**Contract(C₁, …, C_k).** Let S be a largest C_i, and M the union of the others. Set H := M. The groups of the other C_i are discarded. While S has a group G in the class of H: remove G from S and set H := H ∪ G. Add H to the new container with Build(H, |H|).

**Lemma 3 (lists answer correctly).** Assume all TopK calls are correct. Let G be a group of C, and C₀ ⊆ C the container at its last build. (a) If L_G has an entry with source outside C, then its first such entry minimizes reduced cost over edges entering C with head in G. (b) If L_G is complete and has no such entry, no edge enters C with head in G. (c) If L_G is not complete and has no such entry, then |C| − |C₀| ≥ K_G.

*Proof.* Since the build, y changed only by adding one value to all of a container that contains G, so differences of reduced costs within G are unchanged, and the list stays sorted. Let (u, v) enter C with v ∈ G. Then u ∉ C₀, so f(u, v) was finite. (a) Let i* be the first entry with source outside C. If f(u, v) < f(i*) at the build, then (u, v) is not an entry, and the spec gives an entry i′ of type u with f(i′) ≤ f(u, v) < f(i*), whose source u is outside C. That contradicts the choice of i*. (b) By Lemma 1(b), type u has an entry, whose source is outside C. (c) Not complete means |I| = K with all f finite, so there are K distinct sources outside C₀, all now inside C. ∎

With (c), the loop in Cheapest terminates: after Build(G, 2K_G) the sources are outside C, so the entries are valid or the list is complete. A singly rebuilt group therefore needs at most one Build per Cheapest call.

## 4. Counting

Let L = ⌊log₂ n⌋ + 1. Three kinds of Build: initial, contraction, exhaustion. Exhaustion is the rebuild in Cheapest.

**Lemma 4.** (a) A vertex is in M at most L times. (b) A vertex is in a group absorbed into H at most L times. (c) Summing over contraction builds, Σ|H| ≤ 2nL. (d) Each vertex lies in at most (2L + 1)(L + 1) builds. (e) Summing over all builds, ΣK ≤ n + 2nL + 2nL² .

*Proof.* (a) A vertex in M has its container at least double, since |S| ≥ |C_i|. (b) Let φ(v) be the class of the group containing v. When v is in M, its old group lies inside H, so φ does not decrease. When v is in a group G absorbed by H, then |H| and |G| are in the same class at that moment, so the new size is at least 2^{φ(v)+1}, and φ increases. φ ≤ L − 1. (c) Each vertex of a contraction's H is either in M or absorbed, so this follows from (a) and (b). (d) The group of v is replaced at most 2L times by (a) and (b), so v lies in at most 2L + 1 groups. While a group stays, each exhaustion build doubles K_G, and by Lemma 3(c) K_G ≤ n before any such build, which allows at most L exhaustion builds, so at most L + 1 builds per group. (e) Initial builds give n and contraction builds give 2nL by (c). For an exhaustion build, Lemma 3(c) says the new budget 2K_G is at most twice the growth of C since the last build of G. Growth occurs only in contractions in which G stays a group, so its container is S, and the increment is |M|. A contraction therefore credits |M| to each of at most L groups, and credits are reset at each build. So the total is at most 2L Σ|M| ≤ 2nL². ∎

**Lemma 5.** Σ_builds √(K N(G)) ≤ √(ΣK · ΣN(G)) = O(√(nm) L²).

*Proof.* Cauchy-Schwarz; ΣK = O(nL²) by Lemma 4(e); ΣN(G) ≤ m(2L + 1)(L + 1) by Lemma 4(d). ∎

*Proof of Theorem 1.* There are at most n(2L + 1)(L + 1) builds. Set δ so that the union bound gives total error at most 1/3, which costs a factor O(log n) per build by DHHM's Remark 1, and each call is truncated, so this is a worst-case bound. Lemmas 3(c) and 4 hold even when a TopK call returned a non-minimal answer, as long as its outputs are items with distinct types, which a truncated run can enforce classically: 3(c) uses only that a list has K distinct sources with finite values, and Lemma 4 never uses minimality. So the build count and ΣK are unconditional, and the union bound runs over a fixed number of calls. Lemma 5 gives O(√(nm) log³ n), and Lemmas 2 and 3 give correctness. ∎

**Remark (checking the output).** The output comes with (y_X). Inequality (1) can be searched for a violation by Grover over the edges with O(√m) queries, with the sums read from classical data, and with no further queries the output's cost and tightness can be checked. The signs y_X ≥ 0 for contracted X are checked classically, at no queries, because (1) and tightness alone do not imply them. A report of none is checked by a Grover search over the N(a) entering edges of a. So a wrong run is detected with high probability at small extra cost.

**Remark (decision trees).** Beigi and Taghavi's generalized decision trees (arXiv:1905.13095, Theorem 4(ii)) improve the bound to O(√(nm) log² n √(1 + log(m/n))), which has fewer logs than Theorem 1. Run the shortest-path route above with every scan in random order. Then T ≤ m(L + 2)I + m, with I ≤ ⌈log₂ n⌉ iterations, and the expected number of red edges is O(I L n (1 + ln(m/n))), up to constants, and the theorem gives the bound. Ties need a fixed lexicographic rule, so that every tree computes the same function. The lists of Section 3 should reach the same bound the same way. This is a claim and is not in Lean. `sim/trees.py` measures T and G on single paths of hand-built families, which does not establish a worst case. At n = 256 in the matrix model, √(TG)/n^{3/2} is 11.6 on `chain` with the lists here against 43.7 with the plain tree. On `binmerge` it is 16.5 with the lists here against 34.9 with Fischer-Oshman, a constant-factor advantage.

**Remark (time).** With QRAM to the classical arrays, each f is computed with polylog overhead. Keep a container label per vertex, relabelled on the smaller side, and offsets y(v) = a(v) + b(group), where only b changes on selection. All work is then O(n polylog n) classical plus the searches, for time Õ(√(nm)). This is not carried out in detail.

## 5. Lower bounds

*Proof of Theorem 2.*

**Quantum, matrix.** Connectivity needs Ω(n^{3/2}) queries (DHHM Theorem 23). Given an undirected G, give each edge both directions with weight 0. Then one matrix query to the digraph is one query to G, and an arborescence rooted at r exists exactly when G is connected.

**Quantum, array.** For 4n ≤ m ≤ n²/2: MST needs Ω(√(nm)) queries (DHHM Theorem 24). Their instance has n = n₀ + k + 1 vertices and k(n₀ + 1) edges, with bound Ω(n₀√k), for k ≥ 2. Bidirect the graph with the same weights, and take the entering list of v to be the adjacency list of v. A spanning tree rooted at r gives an arborescence of the same cost, and an arborescence is a spanning tree with the same cost, so an output arborescence is an MST. With k = Θ(m/n) ≤ n/2, n₀ ≥ n/2 − 1 and the bound is Ω(√(nm)).

**Hidden parents, m < 4n.** Number the non-root vertices v₁, …, v_{n−1}, with v₀ = r. Each v_i has one entering edge of weight 0 and hidden source r or v_{i−1}, stored first in its list. The other m − n + 1 edges have known sources and large weight. Every choice gives an arborescence, the optimum uses exactly the hidden edges, and so the output reveals n − 2 bits. That needs Ω(n) = Ω(√(nm)) quantum queries and Ω(m) classical ones.

**Classical.** Let every non-root v have an edge from r of weight 1, and let each of the m′ other edges (u, v), u, v ≠ r, have weight 0 or 2. If all are 2, the star from r is the unique optimum, of cost n − 1. If (u, v) has weight 0, taking it with r → x for all x ≠ v costs n − 2, so no optimum is the star. So the output alone, with no extra reads, computes OR of m′ bits, which needs Ω(m′) randomized queries. Here m = m′ + n − 1, so this is Ω(m) for m ≥ 2n. For m < 2n use the hidden parents above. In the matrix model m′ = (n − 1)(n − 2), giving Ω(n²). ∎

## 6. What the measurements add

`sim/check_small.py`: brute force, networkx and the dual certificate agree on 951 runs (840 brute force, 48 networkx, 63 with Grover statistics), all families, including the back end. `sim/qiskit_check.py`: the whole algorithm with each search a Qiskit circuit, at most 9 qubits, 24 runs, 0 wrong, with success frequency matching sin²((2j+1)θ) within 0.02. `sim/topk_constant.py`: applications/√(dN) stays between 4.3 and 8.4 up to N = 2^16. `sim/scaling.log`: on `chain`, plain minimum finding fits exponent 1.98 and ours 1.63 on sizes up to 2048, with cost/n^{1.5} growing by 0.5 per doubling, consistent with a single log factor at these sizes.

`sim/check_fo.py`: the Fischer-Oshman route gives the optimal cost on 4000 small random instances and 300 networkx comparisons, with iterations at most ⌈log₂ n⌉ on the random ones. `sim/check_virtual.py`: on 1869 components, one Dijkstra on the virtual graph matches the distances inside the component.

These runs are weaker than they look. In `scaling.log` the family `chain` has 0 rebuilds, and the largest rebuild count at any size is 57, so the exhaustion term of Lemma 4(e) is barely exercised there. `stats.cost` charges √(min(K, n)·N) and is not a query count: no read-all branch and no log factor. The back end `top_k_bbht` stops when no good element remains, which a real run cannot detect, so it measures time to success and not the truncated budget.

## 7. Limits

- Queries only. Time is sketched in a remark and not carried out.
- There is no gain at m = Θ(n). The array bound for n²/2 < m ≤ n(n − 1) is not worked out.
- Theorem 1 is close to a corollary of Fischer-Oshman plus DHHM. That route and the bound with fewer logs are claims, and neither is in Lean.

## 8. Formal verification

`lean/` builds with `lake build` (Lean 4 v4.36.0-rc1, Mathlib `d875a8de`), with no `sorry` and no `axiom` declaration. `lake env lean Arborescence/Axioms.lean` prints the axioms of 36 theorems: only `propext`, `Classical.choice` and `Quot.sound`.

| Part | Theorems |
|---|---|
| Weak duality, certificate | `weak_duality`, `isMinArb_of_cost_eq`, `certificate`, `no_arb_of_no_entering` |
| Lemma 1 | `IsTopK.min_of_type` |
| Lemmas 3 to 5 | `lemma3a`, `lemma3b`, `lemma3c`, `lemma4a`, `lemma4b`, `lemma4c`, `lemma4d`, `lemma4e`, `sum_wt_le`, `lemma5_cs`, `lemma5` |
| The algorithm | `solve_correct`, `solve_some`, `solve_none`, `solve_reach`, `solve_run`, `solve_sum_K`, `solve_sum_N`, `solve_cost`, `solve_queries`, `exactTopK_correct` |
| Reductions for the lower bounds | `exists_arb_iff_connected`, `isMinArb_to_isMST`, `isMST_to_isMinArb`, `or_iff_cost_lt`, `hidden_reveals` |

**Assuming.** `DHHMTheorem6` for `solve_queries`, and `Oracle.Correct`, `Oracle.Structural` on the list oracle, with `vs` a duplicate-free list.

**Not formalized.** TopK error and the union bound, which account for one log of the log³. The read-all branch. Restricting the algorithm to its queries: the cost is a charge on the trace. DHHM's Theorems 23 and 24 and the OR bound themselves, of which only the reductions are in Lean. The Fischer-Oshman route and the decision-tree remark.

## References

1. C. Dürr, M. Heiligman, P. Høyer, M. Mhalla. Quantum query complexity of some graph problems. quant-ph/0401091.
2. S. Fischer, R. Oshman. A distributed algorithm for directed minimum-weight spanning tree. DISC 2019, LIPIcs 146, 16. Journal version: Distributed Computing 36(1), 2023.
3. L. Lovász. Computing ears and branchings in parallel. FOCS 1985.
4. S. Beigi, L. Taghavi. Quantum speedup based on classical decision trees. arXiv:1905.13095.
5. P. A. Kerger, D. E. Bernal Neira, Z. Gonzalez Izquierdo, E. G. Rieffel. Mind the Õ: asymptotically better, but still impractical, quantum distributed algorithms. arXiv:2304.02825.
6. J. Edmonds. Optimum branchings. J. Res. Nat. Bur. Standards 71B, 1967.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
