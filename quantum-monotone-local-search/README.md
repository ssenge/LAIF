# Quantum monotone local search

Written 7 Nov 2026.

Monotone local search [1] turns an algorithm that extends a partial solution into an exact algorithm. If the extension problem is solved in time c^k, a solution is found in time (2 − 1/c)^n. Here the same scheme is run with amplitude amplification over the samples and a quantum walk on the extension algorithm. This gives (2 − 1/c)^{n/2} whenever the extension algorithm is a backtracking tree.

**Setting [1].** An implicit set system Φ maps an instance I of size N to a universe U_I of n elements and a family F_I of subsets, with membership decidable in polynomial time.

- *Φ-Subset:* find a set in F_I.
- *Φ-Extension:* given I, a set X ⊆ U_I and an integer k, decide whether some S ⊆ U_I \ X with |S| ≤ k has X ∪ S ∈ F_I.

**Theorem 1.** Let c > 1. Suppose Φ-Extension is decided by a backtracking tree with at most p(N) · c^k nodes, for a fixed polynomial p. That is, every node answers, makes one call, or branches into the OR of polynomially many children; it computes them in polynomial time and stores an instance of polynomial size; and the depth is polynomial. Then Φ-Subset has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, running in time (2 − 1/c)^{n/2} N^{O(1)}. The same holds if Φ-Extension has any bounded-error quantum algorithm in polynomial space whose running time on every input is at most c^{k/2} p(N).

Status: Claim, implied by the quantum walk of [2], amplitude amplification [6] and Lemma 2.2 of [1], with the classical extension algorithms of [3], [4], [5] and [8] as stated. The averaging lemma for amplitude amplification and the bases of the corollaries are in Lean. The amplitude amplification over samples is simulated with an exact classical oracle on small instances.

## Corollaries

| Problem | Extension algorithm | c | Classical, [1] with the same extension | Quantum, this work |
|---|---|---|---|---|
| Feedback Vertex Set | highest-degree branching [3] | 3.460 | O(1.7110^n) | **O(1.3081^n)** |
| Cluster Vertex Deletion | branching [4] | 1.811 | O(1.4479^n) | **O(1.2033^n)** |
| Subset Feedback Vertex Set, Group Feedback Vertex Set | LP-branching [8] | 4 | O(1.7500^n) | **O(1.3229^n)** |
| Node Unique Label Cover, constant label set Σ | LP-branching [8] | \|Σ\|² | (2 − \|Σ\|^{−2})^n | **(2 − \|Σ\|^{−2})^{n/2}** |
| Multicut on Trees (n edges) | branch and search [5] | √(√2 + 1) ≈ 1.5538 | O(1.3565^n) | **O(1.1647^n)** |
| Min-Ones d-SAT, d ≥ 3 | branching on an unsatisfied clause [1] | d | (2 − 1/d)^n | **(2 − 1/d)^{n/2}**: 1.2910^n, 1.3229^n, 1.3417^n for d = 3, 4, 5 |
| d-Hitting Set, d ≥ 4 | the same, as a special case | d | below this, by [1] | **(2 − 1/d)^{n/2}** |

All quantum rows are for bounded error, polynomial space and no quantum random access memory, up to polynomial factors, and use the classical analyses as stated.

**Before.** Grover search over all subsets takes 2^{n/2} ≈ 1.4142^n. For Feedback Vertex Set, a quantum walk on the branching algorithm of Razgon gives O*(1.8899^{n/2}) ⊂ O(1.3748^n), stated for Maximum Induced Forest in [9]. A quantum walk on a classical exact algorithm with base b gives √b, but only if that algorithm is a backtracking tree. Even the square roots of the exact bases listed in [1] are larger than the bounds above: √1.7347 ≈ 1.3171 for Feedback Vertex Set, √1.6181 ≈ 1.2721 for Cluster Vertex Deletion, √1.8638 ≈ 1.3652 for Subset Feedback Vertex Set and √1.8704 ≈ 1.3677 for 4-Hitting Set. For Group Feedback Vertex Set, Node Unique Label Cover, Multicut on Trees and Min-Ones d-SAT, [1] lists no exact algorithm faster than brute force. To our knowledge, no quantum version of monotone local search has been stated before. The classical column uses the same extension algorithm; faster classical bounds exist for some rows, such as 1.6097^n for Min-Ones 3-SAT in [1] and the randomized bounds for Feedback Vertex Set.

For 3-Hitting Set the base 3 is not enough: a walk on the exact algorithm of Wahlström, if it is a backtracking tree, gives about 1.2759^n. Any backtracking tree for the extension with c < 2.687 would give a lower bound. The 2.0409^k algorithm of [7] contains a step that computes the optimum of a component before a tail call, so it is not a plain OR tree; older branching algorithms for 3-Hitting Set are not checked here.

## 1. The algorithm

Fix the input I and a budget k′ ≤ n, and let t ≤ k′ minimize C(n, t)/C(k′, t) · c^{k′−t}, as in [1].

1. **Samples.** Prepare the uniform superposition over all subsets Y ⊆ U_I of size t (a Dicke state, polynomially many gates).
2. **Oracle.** On each Y, run the detection walk of [2] on the extension tree of (I, Y, k′ − t) with the bound T = p(N) c^{k′−t}. Reduce its error to δ by O(log 1/δ) repetitions and a majority vote, with measurements deferred, and write the answer bit. Its running time is √T · poly(N), the same for every Y.
3. **Amplification.** Let p₀ = C(k′, t)/C(n, t) and m = ⌈1/√p₀⌉. Measure once without amplification, and once after j rounds of amplitude amplification for j uniform in {0, …, m − 1}. Accept if a measured Y passes a final check: the extension decision run again on Y, with a majority vote over O(log n) runs.

Run this for every k′ ≤ n. Accept if some run accepts.

**The bound T.** The walk needs an explicit bound on the number of nodes of the full tree, explored without stopping at the first accepting leaf. The measure and conquer analyses of the corollaries prove, by induction on the measure, a bound C · c^k on the leaves of the full tree with an explicit constant C, and the depth is at most a fixed polynomial. Their product is the bound p(N) c^k used here.

**Correctness.** If some S ∈ F_I has |S| = k′, then every Y ⊆ S with |Y| = t is a yes-instance of the extension, with S \ Y as the completion, so at least C(k′, t) samples are marked. If a solution of size s ≤ k exists, this applies to the run with k′ = s. With an exact oracle the success probability p of step 1 is then at least p₀. There are two cases.

- If p > 3/4, the unamplified measurement succeeds with probability above 3/4.
- Otherwise sin 2θ = 2√(p(1 − p)) ≥ √p ≥ √p₀, where sin² θ = p. So m sin 2θ ≥ 1, and the mean of sin²((2j + 1)θ) over j < m is at least 1/4 (`amp_avg`, the lemma of [6]).

The oracle with error δ differs from the exact one by O(√δ) in norm per call, so δ = 1/(m² poly(n)) changes the success probability by at most 1/100. This costs O(log m) = O(n) repetitions.

If no solution of size at most k exists, no sample is marked, and the final check rejects except with small probability. A constant number of repetitions gives bounded error.

**Time.** The run for k′ costs m · √T · poly(N) = √(C(n, t)/C(k′, t) · c^{k′−t}) · poly(N). This is the square root of the cost of the classical run in [1]. By Lemma 2.2 of [1], max over k′ of min over t of C(n, t)/C(k′, t) · c^{k′−t} is at most (2 − 1/c)^n n^{O(1)}. So the total over k′ ≤ n is (2 − 1/c)^{n/2} N^{O(1)}.

The space is that of the walk plus the n qubits of the sample, so it is polynomial, and no quantum random access memory is used. A solution follows from an accepted sample Y by descending the extension tree with the detection walk at each child. ∎

## 2. The extension trees

In each case below, deleting X (or cutting X, for Multicut on Trees) turns the extension instance into an instance of the same problem with budget k − |X|. That instance has at most as many elements.

- **Feedback Vertex Set [3].** The algorithm works on (G, F, k), with undeletable vertices F, which are empty at the start.
  - *Single calls.* Reductions 1 to 5 each delete a vertex, bypass a degree-two vertex or lower an edge multiplicity, and each makes one call with budget k or k − 1.
  - *Answers.* Reduction 6 answers through matroid matching in polynomial time. The pruning rule answers no.
  - *OR.* The branching rule makes two children: (G − u, F, k − 1), and u contracted with its neighbours in F into F, budget k.
  - *Size.* Every branch removes a free vertex, so the depth is at most n. The measure starts at k and is non-negative after pruning, so the full tree has O*(3.460^k) leaves.
- **Cluster Vertex Deletion [4].**
  - *Reductions R1 to R5.* Each answers or makes one call; R5 solves components of maximum degree two in polynomial time.
  - *Branching rules B1 to B3.* Each branches over Twins(v) and the members of a k-dominating family, the latter computed by the recursion VCalg. Each step of VCalg recurses on a constant number of sets. Expanding VCalg inside the tree gives a backtracking tree: each VCalg leaf X is followed by the call (G − X, k − |X|).
  - *Size.* The analysis of [4] bounds the leaves of the full combined recursion by O*(1.811^k); a VCalg leaf with negative budget is a no leaf.
- **Group Feedback Vertex Set, Subset Feedback Vertex Set and Node Unique Label Cover [8].** The algorithms are LP-branching. Each node solves a half-integral relaxation in polynomial time and fixes, by single calls, assignments that do not raise the relaxed optimum. Otherwise it branches into two children for Group Feedback Vertex Set (Lemma 8 of [8]) or |Σ| children for Unique Label Cover (Lemma 1 and Corollary 4 of [8]). Each branch lowers the gap between the budget and the relaxed optimum by at least 1/2, so the depth of branching is at most 2k and there are at most 4^k or |Σ|^{2k} leaves. Subset Feedback Vertex Set reduces to Group Feedback Vertex Set on the same graph with the same budget, in polynomial time, by Lemma 5 of [10], with the group Z₂^{|S|}. This group is exponentially large, so the relaxation is solved in the oracle model of Section 5.2 of [8]. For Node Unique Label Cover the label set is fixed, so c = |Σ|² is a constant.
- **Multicut on Trees [5].** Cutting X removes its edges and the requests they separate, which leaves a forest; the algorithm of [5] cuts edges itself and handles forests. The reduction rules are single calls; those that use minimum vertex covers do so on auxiliary graphs of maximum degree two. The branching rules make two or a constant number of children, and the depth is polynomial. The number of leaves is bounded by L(k) ≤ ρ^k, with ρ = √(√2 + 1).
- **Min-Ones d-SAT and d-Hitting Set [1].** Pick an unsatisfied clause and branch over its at most d variables set to 1, with budget k − 1. The depth is at most k, and there are at most d^{k+1} nodes.

## 3. Measurements

| Script | What it checks | Result |
|---|---|---|
| [`bounds.py`](bounds.py) | the bases √(2 − 1/c), and max_k min_t C(n,t)/C(k,t) c^{k−t} against (2 − 1/c)^n for n up to 3000 | all bases hold; the ratio stays below 1 ([`bounds.log`](bounds.log)) |
| [`qmls_sim.py`](qmls_sim.py) | the sampling and amplification of Section 1, with an exact classical oracle given by three extension trees: clause branching for 3-Hitting Set, the branching of [3] (reduction 6 replaced by further branching), and induced-P3 branching for Cluster Vertex Deletion | 120 random instances each: the smallest accepted budget equals the optimum by brute force; at k′ = OPT at least C(k′, t) samples are marked; the averaged success is at least 0.417 ≥ 1/4; 40 state-vector runs per problem match the closed form; a greedy tree without the second branch misses the optimum on 13 of 100 graphs ([`qmls_sim.log`](qmls_sim.log)) |

The script for Cluster Vertex Deletion runs the basic branching of base 3, not the algorithm of [4]. The scripts do not run the quantum walk, the bounded-error oracle or the algorithms of [4], [5] and [8], and they do not check tree sizes.

## 4. Limits

- The running times of [3], [4], [5] and [8] are used as stated there; their analyses are not reproduced here. The LP-branching algorithms of [8] are not run by the scripts.
- The quantum walk of [2] and Lemma 2.2 of [1] are used as stated.
- The scheme is the quantum form of the basic theorem of [1]. Its multivariate and sample-dependent extensions are not treated here.

## 5. Formal verification

The Lean library [`lean/`](lean/) is built on Mathlib and uses only the standard axioms ([`lean/axioms.log`](lean/axioms.log)).

| Theorem | Statement |
|---|---|
| `two_sin_mul_sum_cos` | 2 sin x · Σ_{j<m} cos((2j + 1)x) = sin(2mx) |
| `amp_avg` | if sin 2θ > 0 and m sin 2θ ≥ 1, then Σ_{j<m} sin²((2j + 1)θ) ≥ m/4 |
| `fvs_base` | √(2 − 1/3.460) ≤ 1.3081 |
| `cvd_base` | √(2 − 1/1.811) ≤ 1.2033 |
| `mct_base` | √(2 − 1/√(√2 + 1)) ≤ 1.1647 |
| `d3_base`, `d4_base`, `d5_base` | √(2 − 1/d) ≤ 1.2910, 1.3229, 1.3417 (d = 4 also for c = 4 in the feedback vertex set rows) |

Not formalized: Lemma 2.2 of [1], the quantum walk, the error analysis of the oracle and the extension trees.

## References

1. F. V. Fomin, S. Gaspers, D. Lokshtanov and S. Saurabh. Exact algorithms via monotone local search. Journal of the ACM 66(2), 2019. STOC 2016. arXiv:1512.01621.
2. A. Montanaro. Quantum-walk speedup of backtracking algorithms. Theory of Computing 14(15), 2018. arXiv:1509.02374.
3. Y. Iwata and Y. Kobayashi. Improved analysis of highest-degree branching for Feedback Vertex Set. IPEC 2019. arXiv:1905.12233.
4. D. Tsur. Faster parameterized algorithm for Cluster Vertex Deletion. arXiv:1901.07609.
5. I. Kanj, G. Lin, T. Liu, W. Tong, G. Xia, J. Xu, B. Yang, F. Zhang, P. Zhang and B. Zhu. Algorithms for cut problems on trees. arXiv:1304.3653.
6. M. Boyer, G. Brassard, P. Høyer and A. Tapp. Tight bounds on quantum searching. Fortschritte der Physik 46, 1998. G. Brassard, P. Høyer, M. Mosca and A. Tapp. Quantum amplitude amplification and estimation. Contemporary Mathematics 305, 2002.
7. D. Tsur. Faster parameterized algorithm for 3-Hitting Set. arXiv:2501.06452.
8. Y. Iwata, M. Wahlström and Y. Yoshida. Half-integrality, LP-branching and FPT algorithms. SIAM Journal on Computing 45(4), 2016. SODA 2014. arXiv:1310.2841.
9. Kvantu algoritms maksimāla inducēta meža problēmai (a quantum algorithm for the maximum induced forest problem). Thesis, University of Latvia. https://dspace.lu.lv/handle/7/66169.
10. M. Cygan, M. Pilipczuk and M. Pilipczuk. On group feedback vertex set parameterized by the size of the cutset. Algorithmica 74, 2016. arXiv:1112.6255.
