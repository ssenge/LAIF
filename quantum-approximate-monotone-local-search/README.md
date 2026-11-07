# Quantum approximate monotone local search

Written 7 Nov 2026.

Approximate monotone local search [1, 4] turns extension algorithms with ratio α and running time c^k into an exponential-time β-approximation. Here the same scheme is run with amplitude amplification over the samples, and with a quantum walk on the extension algorithm where that algorithm is an exact backtracking tree. The quantum time is the square root of the classical time. This gives, to our knowledge, the first quantum exponential-time approximation algorithms for Vertex Cover, d-Hitting Set, Feedback Vertex Set, Subset Feedback Vertex Set, Cluster Vertex Deletion, Proper Interval Vertex Deletion and Multicut on Trees.

**Setting [1].** An implicit set system Φ maps an instance I of size N to a universe U_I of n elements and a monotone family F_I of subsets, with membership decidable in polynomial time. Φ_min-Subset asks for a set in F_I of minimum size OPT. A β-approximation returns some S ∈ F_I with |S| ≤ β · OPT.

**Cost [4].** Let L be a finite list of pairs (α, c) with α, c ≥ 1, and let β ≥ 1. For a guess k of OPT, a pair (α, c) and a sample size t ≤ βk, let

- x = max(0, ⌈(1 − β/α) k + t/α⌉) and ℓ = k − x;
- hyper(n, k, t, x) be the probability that a uniform t-subset of [n] meets [k] in at least x elements.

Then best(L, β) is the base of the maximum over k ≤ n/β of the minimum over (α, c) ∈ L and t of c^ℓ / hyper(n, k, t, x), up to polynomial factors. For L = {(β, c)} it is the value amls(β, c) of [1], and for L = {(1, c)} and β = 1 it is 2 − 1/c, the base of monotone local search.

**Theorem 1.** Let β ≥ 1, and let each pair (α, c) of L come with an extension procedure of one of two kinds.

- (a) A randomized algorithm, polynomial in N, that on (I, X, ℓ) returns a set Y. If some S with |S| ≤ ℓ has X ∪ S ∈ F_I, then X ∪ Y ∈ F_I and |Y| ≤ αℓ with probability at least q(N, ℓ) ≥ c^{−ℓ}/p(N). Here q is computable in polynomial time and p is a fixed polynomial. A deterministic polynomial-time α-approximation, run on the instance left after X, is of this kind with c = 1.
- (b) For α = 1: a backtracking tree, as in Theorem 1 of [quantum monotone local search](../quantum-monotone-local-search/), with at most p(N) c^ℓ nodes. It accepts (I, X, ℓ) exactly when some S with |S| ≤ ℓ has X ∪ S ∈ F_I, and its accepting leaves give such an S.

Then Φ_min-Subset has a quantum β-approximation with bounded error, polynomial space and no quantum random access memory, running in time best(L, β)^{n/2} N^{O(1)}.

Status: Claim, implied by amplitude amplification [3], the quantum walk of [10] and the cost analysis of [1, 4], with the extension algorithms as stated in their sources. The averaging lemma of amplitude amplification is the Lean lemma `amp_avg` of [quantum monotone local search](../quantum-monotone-local-search/). [`bounds.py`](bounds.py) computes best(L, β), reproduces six values stated in [1, 4] and [5], and checks the exact cost at n = 1000.

## Corollaries

| Problem | Extension procedures (α, c) | β = 1.1 | β = 1.2 | β = 1.5 | β = 1.8 | Quantum exact |
|---|---|---|---|---|---|---|
| Vertex Cover | (a) randomized branching [2], (α, c(α)) for the ratios α ∈ [1.1, 1.9] tabulated there; (a) (2, 1), maximal matching | **1.0555^n** | **1.0312^n** | **1.0050^n** | **1.0003^n** | 1.0953^n |
| 3-Hitting Set | (a) randomized branching [2], (α, c(α)) for α ∈ {1.2, 1.4, …, 2.8}; (b) (1, 2.168); (a) (3, 1) | **1.1607^n** | **1.1135^n** | **1.0458^n** | **1.0211^n** | 1.2405^n |
| 4-Hitting Set | (b) (1, 4), branching on a hyperedge; (a) (4, 1) | **1.2288^n** | **1.1861^n** | **1.1233^n** | **1.0933^n** | 1.3229^n |
| Feedback Vertex Set | (b) (1, 3.460); (a) (2, 1) [6] | **1.2161^n** | **1.1752^n** | **1.0987^n** | **1.0315^n** | 1.3081^n |
| Subset Feedback Vertex Set | (b) (1, 4); (a) (8, 1) [7] | **1.2288^n** | **1.1861^n** | **1.1233^n** | **1.0933^n** | 1.3229^n |
| Cluster Vertex Deletion | (b) (1, 1.811); (a) (2, 1) [8] | **1.1318^n** | **1.1047^n** | **1.0676^n** | **1.0315^n** | 1.2033^n |
| Proper Interval Vertex Deletion | (b) (1, 6); (a) (6, 1) [9] | **1.2558^n** | **1.2097^n** | **1.1404^n** | **1.1066^n** | 1.3541^n |
| Multicut on Trees (n edges) | (b) (1, √(√2 + 1)); (a) (2, 1) [11] | **1.1034^n** | **1.0817^n** | **1.0525^n** | **1.0315^n** | 1.1647^n |

All entries are quantum times for a β-approximation with bounded error, polynomial space and no quantum random access memory, up to polynomial factors, rounded up. The trees of kind (b) are those of [quantum monotone local search](../quantum-monotone-local-search/), and the last column is the quantum exact bound from there, or from [quantum vertex cover](../quantum-vertex-cover/) for Vertex Cover. [`bounds.log`](bounds.log) lists β = 1.1 to 2.0 and the classical values best(L, β), whose square roots these are. For β = 2, Feedback Vertex Set, Cluster Vertex Deletion and Multicut on Trees take polynomial time.

**Before.** To our knowledge, no quantum exponential-time approximation algorithm for these problems has been stated. Every entry is below the quantum exact bound in the last column. Amplitude amplification over random sets of size β · OPT, the quantum form of the brute-force approximation of [1], gives √brute(β): 1.3097^n, 1.2580^n, 1.1769^n and 1.1360^n for β = 1.1, 1.2, 1.5 and 1.8. The classical bounds of [1, 4] are the squares of these entries or smaller. For example, [4] uses the randomized 2.69998^k algorithm for Feedback Vertex Set, and for Vertex Cover close to ratio 1 it also uses deterministic algorithms that are not used here.

## 1. The algorithm

For each guess k ≤ n/β, choose (α, c) ∈ L and t that minimize c^ℓ / hyper(n, k, t, x), and let q₀ = hyper(n, k, t, x) · q(N, ℓ) for kind (a), and q₀ = hyper(n, k, t, x) for kind (b).

1. **Samples.** Prepare the uniform superposition over the t-subsets X of U_I (a Dicke state). For kind (a), also prepare the random bits of the procedure.
2. **Marking.** For kind (a), run the procedure on (I, X, ℓ) reversibly, and mark the branch if Z = X ∪ Y lies in F_I and |Z| ≤ βk. For kind (b), run the detection walk of [10] on the tree of (I, X, ℓ) with the node bound T = p(N) c^ℓ. Reduce its error to δ by a majority vote, and mark X if it accepts.
3. **Amplification.** Let m = ⌈1/√q₀⌉. Measure once without amplification, and once after j rounds of amplitude amplification for j uniform in {0, …, m − 1}. For kind (b), find Y for a measured X by descending the tree with the detection walk at each child. Keep every Z = X ∪ Y with Z ∈ F_I and |Z| ≤ βk.

Return the smallest set kept, or U_I if none is kept.

**Size.** Suppose |X ∩ OPT| ≥ x for an optimum solution OPT with |OPT| = k. Then OPT \ X has at most ℓ elements and completes X. Hence the procedure returns |Y| ≤ αℓ, and |Z| ≤ t + αℓ ≤ βk. If x = ⌈(1 − β/α)k + t/α⌉, this follows from αx ≥ (α − β)k + t. If x = 0, then t + αk ≤ βk.

**Correctness.** Every kept set lies in F_I. Consider k = OPT. By the size argument, the probability p of a marked branch is at least q₀. With an exact marking, there are two cases.

- If p > 3/4, the unamplified measurement succeeds.
- Otherwise sin 2θ = 2√(p(1 − p)) ≥ √p ≥ √q₀, where sin² θ = p. So m sin 2θ ≥ 1, and the mean success probability over j < m is at least 1/4 (`amp_avg`, the lemma of [3]).

For kind (a) the marking is exact, since it is a polynomial-time check. For kind (b), δ = 1/(m² poly(n)) changes the success probability by at most 1/100, as in [quantum monotone local search](../quantum-monotone-local-search/), at the cost of O(n) repetitions. A constant number of repetitions of the whole scheme gives bounded error.

**Random bits.** The algorithms of [2] choose branches with fixed probabilities γ. Round each γ to a dyadic number with O(log N) bits. This changes the probability of each sequence of coin outcomes, a product of polynomially many factors, by at most a constant factor, so q₀ changes by at most a constant factor. The coins are then Hadamard gates on fresh qubits.

**Time.** The run for k costs m · poly(N) for kind (a), and m · √T · poly(N) for kind (b). In both cases this is √(c^ℓ / hyper(n, k, t, x)) · poly(N), the square root of the classical cost of [1, 4]. Taking the maximum over k gives best(L, β)^{n/2} N^{O(1)}. The space is polynomial, and no quantum random access memory is used. ∎

## 2. The extension procedures

Every problem in the table is a deletion problem whose remaining instance, after X is deleted, is an instance of the same problem: for hitting sets, delete the hyperedges hit by X; for Multicut on Trees, cut the edges in X and drop the requests they separate. So any algorithm for the problem with budget ℓ is an extension procedure.

- **Vertex Cover [2].** For α ≥ 1.4 the algorithm EnhancedVC3* branches at random on a vertex of degree at least 3, choosing either the vertex or its neighbours, at most Δ of them. At maximum degree 2 it solves the graph exactly. For α < 1.4 the algorithm BetterVC replaces the branching of an exact 1.33^k algorithm by random choices. On regular and on disconnected graphs it makes two recursive calls, and Lemma 7 of [2] bounds the number of calls by a polynomial. Both always return a vertex cover. They return one of size at most αk with probability at least p(⌊αk⌋, k), which is at least (c + ε)^{−k} for every ε > 0 and large k, where c is the rounded-up base of the tables of [2] and p is a recurrence evaluated by dynamic programming. The 2-approximation by a maximal matching is of kind (a) with c = 1.
- **3-Hitting Set [2].** The algorithm 3HS chooses at random between a vertex v and a hitting set of the neighbours graph of v. Its rules were found by a computer-aided search with Δ = 7. It is polynomial, with the success probability of the table of [2]. The tree of kind (b) is the 2.168^k algorithm with unit weights and weight bound ℓ, so its accepted sets have at most ℓ elements. Taking all elements of a maximal family of disjoint hyperedges is a 3-approximation.
- **4-Hitting Set.** Branching on the at most four elements of a hyperedge that is not hit is a tree with at most 4^{ℓ+1} nodes. The same maximal-disjoint-family rule gives a 4-approximation.
- **The other rows.** The trees are those of [quantum monotone local search](../quantum-monotone-local-search/): highest-degree branching with 3.460^ℓ leaves for Feedback Vertex Set, LP-branching with 4^ℓ leaves for Subset Feedback Vertex Set, branching with 1.811^ℓ leaves for Cluster Vertex Deletion, branching on obstructions with at most six vertices for Proper Interval Vertex Deletion, and branch and search with ρ^ℓ leaves, ρ = √(√2 + 1), for Multicut on Trees. Each counts its budget and accepts only within it. The polynomial-time approximations are those of [6], [7], [8], [9] and [11], with ratios 2, 8, 2, 6 and 2.

## 3. Measurements

| Script | What it checks | Result |
|---|---|---|
| [`bounds.py`](bounds.py) | best(L, β) from the large-deviation exponent of the hypergeometric tail, maximized over k/n and minimized over t/n on a grid with refinement. It reproduces 1.2072, 1.2099, 1.2068 and 1.4156 from Table 2 of [4], 1.114 from [1] and 2 − 1/3 from [5]. For every row and β it also checks the exact discrete cost at n = 1000 against best(L, β)^n | all values reproduced; the logarithm of the exact cost exceeds n ln best by at most 3.99, below 2 ln(n + 1) ≈ 13.8 ([`bounds.log`](bounds.log)) |

The script does not run the extension algorithms or the quantum procedure. The maximization over k/n is numerical, not certified.

## 4. Limits

- The success probabilities of [2], the running times of the trees and approximations, and the asymptotic analysis of the cost in [1, 4] are used as stated. They are not reproduced here.
- Extension procedures that are neither of kind (a) nor of kind (b) are not covered. These include deterministic approximate branching algorithms and randomized algorithms that are not polynomial-time procedures, such as the 2.69998^k algorithm for Feedback Vertex Set.

## References

1. B. C. Esmer, A. Kulik, D. Marx, D. Neuen and R. Sharma. Faster exponential-time approximation algorithms using approximate monotone local search. ESA 2022. arXiv:2206.13481.
2. A. Kulik and H. Shachnai. Analysis of two-variable recurrence relations with application to parameterized approximations. FOCS 2020. arXiv:1911.02653.
3. M. Boyer, G. Brassard, P. Høyer and A. Tapp. Tight bounds on quantum searching. Fortschritte der Physik 46, 1998. G. Brassard, P. Høyer, M. Mosca and A. Tapp. Quantum amplitude amplification and estimation. Contemporary Mathematics 305, 2002.
4. B. C. Esmer, A. Kulik, D. Marx, D. Neuen and R. Sharma. Optimally repurposing existing algorithms to obtain exponential-time approximations. SODA 2024. arXiv:2306.15331.
5. F. V. Fomin, S. Gaspers, D. Lokshtanov and S. Saurabh. Exact algorithms via monotone local search. Journal of the ACM 66(2), 2019. arXiv:1512.01621.
6. V. Bafna, P. Berman and T. Fujito. A 2-approximation algorithm for the undirected feedback vertex set problem. SIAM Journal on Discrete Mathematics 12(3), 1999.
7. G. Even, J. Naor and L. Zosin. An 8-approximation algorithm for the subset feedback vertex set problem. SIAM Journal on Computing 30(4), 2000.
8. M. Aprile, M. Drescher, S. Fiorini and T. Huynh. A tight approximation algorithm for the cluster vertex deletion problem. Mathematical Programming 197(2), 2023.
9. P. van 't Hof and Y. Villanger. Proper interval vertex deletion. Algorithmica 65(4), 2013.
10. A. Montanaro. Quantum-walk speedup of backtracking algorithms. Theory of Computing 14(15), 2018. arXiv:1509.02374.
11. N. Garg, V. V. Vazirani and M. Yannakakis. Primal-dual approximation algorithms for integral flow and multicut in trees. Algorithmica 18, 1997. ICALP 1993.
