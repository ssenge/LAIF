# Quantum approximate monotone local search

Written 7 Nov 2026.

Approximate monotone local search [1, 4] turns extension algorithms with ratio α and running time c^k into an exponential-time β-approximation. Here the same scheme is run with amplitude amplification over the samples, and with a quantum walk on the extension algorithm where that algorithm is an exact backtracking tree. The quantum time is the square root of the classical time. For Vertex Cover, d-Hitting Set, Feedback Vertex Set, Subset Feedback Vertex Set, Cluster Vertex Deletion, Proper Interval Vertex Deletion and Multicut on Trees, and for weighted versions of several of them (Section 5), this gives quantum exponential-time approximation algorithms below both the quantum exact algorithms and the quantum form of brute-force approximation. To our knowledge, none have been stated before.

**Setting [1].** An implicit set system Φ maps an instance I of size N to a universe U_I of n elements and a monotone family F_I of subsets, with membership decidable in polynomial time. Φ_min-Subset asks for a set in F_I of minimum size OPT. A β-approximation returns some S ∈ F_I with |S| ≤ β · OPT.

**Cost [4].** Let L be a finite list of pairs (α, c) with α, c ≥ 1, and let β ≥ 1. For a guess k of OPT, a pair (α, c) and a sample size t ≤ βk, let

- x = max(0, ⌈(1 − β/α) k + t/α⌉) and ℓ = k − x;
- hyper(n, k, t, x) be the probability that a uniform t-subset of [n] meets [k] in at least x elements.

Then best(L, β) is the base of the maximum over k ≤ n/β of the minimum over (α, c) ∈ L and t of c^ℓ / hyper(n, k, t, x), up to polynomial factors. For L = {(β, c)} it is the value amls(β, c) of [1], and for L = {(1, c)} and β = 1 it is 2 − 1/c, the base of monotone local search.

**Theorem 1.** Let β ≥ 1, and let each pair (α, c) of L come with an extension procedure of one of two kinds.

- (a) A randomized algorithm, polynomial in N, that on (I, X, ℓ) returns a set Y. If some S with |S| ≤ ℓ has X ∪ S ∈ F_I, then X ∪ Y ∈ F_I and |Y| ≤ αℓ with probability at least q(N, ℓ) ≥ c^{−ℓ}/p(N). Here q is computable in polynomial time and p is a fixed polynomial. A deterministic polynomial-time α-approximation, run on the instance left after X, is of this kind with c = 1. If the bound only holds as q(N, ℓ) ≥ (c + ε)^{−ℓ}/p_ε(N) for every ε > 0, the conclusion holds with (best(L, β) + ε)^{n/2} for every ε > 0.
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

The bases c of [2] are evaluated numerically there and rounded up, and [2] proves success probability (c* + ε)^{−k} for its exact base c* ≤ c. Since best(L, β) is continuous in the bases and every entry is rounded up from its value, the ε-form of Theorem 1 gives the entries. All entries are quantum times for a β-approximation with bounded error, polynomial space and no quantum random access memory, up to polynomial factors, rounded up. The trees of kind (b) are those of [quantum monotone local search](../quantum-monotone-local-search/), and the last column is the quantum exact bound from there, or from [quantum vertex cover](../quantum-vertex-cover/) for Vertex Cover. [`bounds.log`](bounds.log) lists β = 1.1 to 2.0 and the classical values best(L, β), whose square roots these are. For β = 2, Feedback Vertex Set, Cluster Vertex Deletion and Multicut on Trees take polynomial time.

**Before.** Any quantum exact algorithm is also a β-approximation, and every entry is below the quantum exact bound in the last column. To our knowledge, no quantum algorithm designed for exponential-time approximation of these problems has been stated. Amplitude amplification over random sets of size β · OPT, the quantum form of the brute-force approximation of [1], gives √brute(β): 1.3097^n, 1.2580^n, 1.1769^n and 1.1360^n for β = 1.1, 1.2, 1.5 and 1.8. The classical bounds of [1, 4] are the squares of these entries or smaller. For example, [4] uses the randomized 2.69998^k algorithm for Feedback Vertex Set, and for Vertex Cover close to ratio 1 it also uses deterministic algorithms that are not used here.

## 1. The algorithm

For each guess k ≤ n/β, choose (α, c) ∈ L and t that minimize c^ℓ / hyper(n, k, t, x), and let q₀ = hyper(n, k, t, x) · q(N, ℓ) for kind (a), and q₀ = hyper(n, k, t, x) for kind (b).

1. **Samples.** Prepare the uniform superposition over the t-subsets X of U_I (a Dicke state). For kind (a), also prepare the random bits of the procedure.
2. **Marking.** For kind (a), run the procedure on (I, X, ℓ) reversibly, and mark the branch if Z = X ∪ Y lies in F_I and |Z| ≤ βk. For kind (b), run the detection walk of [10] on the tree of (I, X, ℓ) with the node bound T = p(N) c^ℓ. Reduce its error to δ by a majority vote, and mark X if it accepts.
3. **Amplification.** Let m = ⌈1/√q₀⌉. Measure once without amplification, and once after j rounds of amplitude amplification for j uniform in {0, …, m − 1}. For kind (b), find Y for a measured X by descending the tree with the detection walk at each child. Keep every Z = X ∪ Y with Z ∈ F_I and |Z| ≤ βk.

Return the smallest set kept, or U_I if none is kept.

**Size.** Suppose |X ∩ OPT| ≥ x for an optimum solution OPT with |OPT| = k. Then OPT \ X has at most ℓ elements and completes X. Hence the procedure returns Y with |Y| ≤ αℓ, with probability at least q(N, ℓ) for kind (a), and |Z| ≤ t + αℓ ≤ βk. If x = ⌈(1 − β/α)k + t/α⌉, this follows from αx ≥ (α − β)k + t. If x = 0, then t + αk ≤ βk.

**Correctness.** Every kept set lies in F_I. Consider k = OPT. By the size argument, the probability p of a marked branch is at least q₀. With an exact marking, there are two cases.

- If p > 3/4, the unamplified measurement succeeds.
- Otherwise sin 2θ = 2√(p(1 − p)) ≥ √p ≥ √q₀, where sin² θ = p. So m sin 2θ ≥ 1, and the mean success probability over j < m is at least 1/4 (`amp_avg`, the lemma of [3]).

For kind (a) the marking is exact, since it is a polynomial-time check. For kind (b), δ = 1/(m² poly(n)) changes the success probability by at most 1/100, as in [quantum monotone local search](../quantum-monotone-local-search/), at the cost of O(n) repetitions. A constant number of repetitions of the whole scheme gives bounded error.

**Random bits.** The algorithms of [2] choose branches with fixed probabilities γ. Round each γ to a dyadic number with O(log N) bits. This changes the probability of each sequence of coin outcomes, a product of polynomially many factors, by at most a constant factor, so q₀ changes by at most a constant factor. The coins are then Hadamard gates on fresh qubits.

**Time.** The run for k costs m · poly(N) for kind (a), and m · √T · poly(N) for kind (b). In both cases this is √(c^ℓ / hyper(n, k, t, x)) · poly(N), the square root of the classical cost of [1, 4]. Taking the maximum over k gives best(L, β)^{n/2} N^{O(1)}. The space is polynomial, and no quantum random access memory is used. ∎

## 2. The extension procedures

Every problem in the table is a deletion problem whose remaining instance, after X is deleted, is an instance of the same problem: for hitting sets, delete the hyperedges hit by X; for Multicut on Trees, cut the edges in X and drop the requests they separate. So any algorithm for the problem with budget ℓ is an extension procedure.

- **Vertex Cover [2].** For α ≥ 1.4 the algorithm EnhancedVC3* branches at random on a vertex of degree at least 3, choosing either the vertex or its neighbours, at most Δ of them. On disconnected graphs and on regular graphs it makes two recursive calls and returns the smaller cover, and at maximum degree 2 it solves the graph exactly. For α < 1.4 the algorithm BetterVC replaces the branching of an exact 1.33^k algorithm by random choices, with the same kind of two-call rules. Lemma 7 of [2] bounds the number of calls of BetterVC by a polynomial, and [2] states the same for EnhancedVC3* by a similar argument. Both always return a vertex cover. They return one of size at most αk with probability at least p(⌊αk⌋, k), which is at least (c + ε)^{−k} for every ε > 0 and large k, where c is the rounded-up base of the tables of [2] and p is a recurrence evaluated by dynamic programming. The 2-approximation by a maximal matching is of kind (a) with c = 1.
- **3-Hitting Set [2].** The algorithm 3HS chooses at random between a vertex v and a hitting set of the neighbours graph of v. Its rules were found by a computer-aided search with Δ = 7. It is polynomial, with the success probability of the table of [2]. The tree of kind (b) is the 2.168^k algorithm of [12] with unit weights and weight bound ℓ, so its accepted sets have at most ℓ elements. Taking all elements of a maximal family of disjoint hyperedges is a 3-approximation.
- **4-Hitting Set.** Branching on the at most four elements of a hyperedge that is not hit is a tree with at most 4^{ℓ+1} nodes. The same maximal-disjoint-family rule gives a 4-approximation.
- **The other rows.** The trees are those of [quantum monotone local search](../quantum-monotone-local-search/): highest-degree branching with 3.460^ℓ leaves for Feedback Vertex Set, LP-branching with 4^ℓ leaves for Subset Feedback Vertex Set, branching with 1.811^ℓ leaves for Cluster Vertex Deletion, branching on obstructions with at most six vertices for Proper Interval Vertex Deletion, and branch and search with ρ^ℓ leaves, ρ = √(√2 + 1), for Multicut on Trees. Each counts its budget and accepts only within it. The polynomial-time approximations are those of [6], [7], [8], [9] and [11], with ratios 2, 8, 2, 6 and 2.

## 3. Measurements

| Script | What it checks | Result |
|---|---|---|
| [`bounds.py`](bounds.py) | best(L, β) from the large-deviation exponent of the hypergeometric tail, maximized over k/n and minimized over t/n on a grid with refinement. It reproduces 1.2072, 1.2099, 1.2068 and 1.4156 from Table 2 of [4], 1.114 from [1] and 2 − 1/3 from [5]. For every row and β it also checks the exact discrete cost at n = 1000 against best(L, β)^n | all values reproduced; the logarithm of the exact cost exceeds n ln best by at most 3.99, below 2 ln(n + 1) ≈ 13.8 ([`bounds.log`](bounds.log)) |
| [`wbounds.py`](wbounds.py) | the weighted rows of Section 5, one oracle per run; reproduces 1.158 and 1.659 from Table 1 of [13]; the same exact check at n = 1000 | all values reproduced ([`wbounds.log`](wbounds.log)) |

The scripts do not run the extension algorithms or the quantum procedure. The maximization over k/n is numerical, not certified. The check at n = 1000 is coarse: it would also pass a base that is too low by about 1%, so the fourth decimals rest on the grid search and on the reference values, which agree to within 6 · 10⁻⁴.

## 4. Limits

- The success probabilities of [2], the running times of the trees and approximations, and the asymptotic analysis of the cost in [1, 4] are used as stated. They are not reproduced here.
- The weighted rows use one extension procedure per run, as [13] does; mixing several procedures across weight classes is not treated.
- Extension procedures that are neither of kind (a) nor of kind (b) are not covered. These include deterministic approximate branching algorithms and randomized algorithms that are not polynomial-time procedures, such as the 2.69998^k algorithm for Feedback Vertex Set.

## 5. Weighted problems

In the weighted setting each element has a weight w(u) ≥ 1 and OPT is the minimum weight of a set in F_I. Following [13], an α-extension for (I, X, ℓ) returns T with X ∪ T ∈ F_I and w(T) ≤ α · W_ℓ(X), where W_ℓ(X) is the minimum weight of an extension of X with at most ℓ elements; T may have more than ℓ elements.

**Theorem 2.** Let β > 1, and let (α, c) come with a weighted extension procedure of kind (a), with weights in place of sizes in the guarantee, or of kind (b): for α = 1 a backtracking tree with at most p(N) c^ℓ nodes on (I, X, ℓ, B) that accepts whenever an extension of at most ℓ elements and weight at most B exists, accepts only if an extension of weight at most B exists, and whose accepting leaves give one. Then the weighted problem has a quantum β-approximation with bounded error, polynomial space and no quantum random access memory, in time (best({(α, c)}, β) + ε)^{n/2} for every ε > 0.

*Proof.* We follow the construction of [13] and replace its families by sampling. Let γ = 1 + δ/2 and U_i = {u : γ^i ≤ w(u) < γ^{i+1}}. Guess the largest class k_max that meets an optimum solution S, and let D = ⌈(2/δ) log(2n/δ)⌉. Every element of a class below k_max − D is put into X; their total weight is at most (δ/2) γ^{k_max} ≤ (δ/2) w(S). For each of the at most D + 1 classes i in the window, guess k_i = |S ∩ U_i|, and choose t_i and x_i, ℓ_i as in Section 1 with ζ = β/(1 + δ) in place of β. The procedure samples a uniform t_i-subset X_i of every U_i in the window, adds the light classes, and queries the extension with ℓ = Σ ℓ_i. It marks the result Z if Z ∈ F_I and w(Z) ≤ τ, where τ = w(light classes) + γ ζ Σ_i γ^i k_i. For kind (b) the tree is called with B = τ − w(X).

If |X_i ∩ S| ≥ x_i for every i, then S \ X has at most ℓ elements and weight at most Σ_i γ^{i+1}(k_i − x_i). So w(Z) ≤ w(light classes) + γ Σ_i γ^i (t_i + α(k_i − x_i)) ≤ τ by the size argument of Section 1 in each class, and τ ≤ (δ/2) w(S) + γ ζ w(S) ≤ (1 + δ) ζ w(S) = β w(S). The marked probability is at least Π_i hyper(n_i, k_i, t_i, x_i) times q for kind (a), and amplitude amplification as in Section 1 costs the square root of Π_i c^{ℓ_i} / hyper(n_i, k_i, t_i, x_i) ≤ Π_i best({(α, c)}, ζ)^{n_i} n^{O(1)}. There are at most n^{O(D)} guesses. With δ = 1/log n this is 2^{O(log³ n)}, and best is continuous in ζ, so the total is (best({(α, c)}, β) + ε)^{n/2} for large n. ∎

| Weighted problem | Extension procedure used | β = 1.1 | β = 1.2 | β = 1.5 | β = 1.8 | Quantum exact |
|---|---|---|---|---|---|---|
| Vertex Cover | (b) (1, 1.381), the polynomial-space algorithm of [12] | **1.0788^n** | **1.0620^n** | **1.0397^n** | **1.0297^n** | 1.1296^n |
| 3-Hitting Set | (b) (1, 2.168) [12] | **1.1607^n** | **1.1284^n** | **1.0834^n** | **1.0626^n** | 1.2405^n |
| 4-Hitting Set | (b) (1, 4), branching on a hyperedge | **1.2288^n** | **1.1861^n** | **1.1233^n** | **1.0933^n** | 1.3229^n |
| 5-Hitting Set | (b) (1, 5), branching on a hyperedge | **1.2450^n** | **1.2002^n** | **1.1334^n** | **1.1012^n** | 1.3417^n |
| Feedback Vertex Set | (a) (2, 1) [6] | **1.2880^n** | **1.2185^n** | **1.0987^n** | **1.0315^n** | 2^{n/2} |
| Multicut on Trees (n edges) | (a) (2, 1) [11] | **1.2880^n** | **1.2185^n** | **1.0987^n** | **1.0315^n** | 2^{n/2} |

The table takes, for each β, the better of the tree and the polynomial-time approximation (2-approximation for Vertex Cover [14], d-approximation for d-Hitting Set [14]); here the tree is always the better one. The weighted extensions delete X as before, and the polynomial-time approximations are applied to what remains. Problems with a finite family of forbidden induced subgraphs reduce to weighted d-Hitting Set on the same vertex set, so weighted Cluster Vertex Deletion and weighted Feedback Vertex Set in Tournaments get the 3-Hitting Set row, weighted Cograph Vertex Deletion the 4-Hitting Set row and weighted Split Vertex Deletion the 5-Hitting Set row. The algorithm WVC-Alg of [12] returns NIL or a vertex cover of weight at most W, and it returns one whenever a vertex cover of weight at most W and size at most k exists. Its reductions answer or make one call, and its branching rules return the first answer that is not NIL, so it is a tree of kind (b). Through Theorem 1 of [quantum monotone local search](../quantum-monotone-local-search/) it also gives quantum exact Weighted Vertex Cover in √(2 − 1/1.381)^n ≤ 1.1296^n, the last column. The quantum exact bounds for weighted d-Hitting Set come from the same theorem; for weighted Feedback Vertex Set and Multicut on Trees the last column is quantum minimum finding over all subsets. The classical bounds of [13] are the squares of these entries.

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
12. H. Shachnai and M. Zehavi. A multivariate approach for weighted FPT algorithms. ESA 2015. arXiv:1407.2033 (as A multivariate framework for weighted FPT algorithms).
13. B. C. Esmer, A. Kulik, D. Marx, D. Neuen and R. Sharma. Approximate monotone local search for weighted problems. IPEC 2023. arXiv:2308.15306.
14. R. Bar-Yehuda and S. Even. A local-ratio theorem for approximating the weighted vertex cover problem. Annals of Discrete Mathematics 25, 1985.
