# Optimal copy complexity of anti-symmetrization

2026-11-22

## Problem

Let ρ be a state on ℂ^d of rank r < d with nonzero eigenvalues λ_1, …, λ_r, and let λ_min be the smallest of them. The anti-symmetric state of ρ is

|A_ρ⟩ = Π_anti (|φ_1⟩ ⊗ ⋯ ⊗ |φ_r⟩) / ‖Π_anti (|φ_1⟩ ⊗ ⋯ ⊗ |φ_r⟩)‖,

for any orthonormal basis φ_1, …, φ_r of the support of ρ. It depends only on the support, up to a phase. Anti-symmetrization asks for a copy of |A_ρ⟩ from n copies of the unknown ρ [1].

*Protocols.* A protocol is any quantum channel Φ from (ℂ^d)^{⊗n} to (ℂ^d)^{⊗r}. This covers measurements, adaptive choices, ancillas, classical randomness and any order of processing the copies. Its success at ρ is the fidelity ⟨A_ρ|Φ(ρ^{⊗n})|A_ρ⟩, and its worst-case success is the minimum over all ρ with the given eigenvalues. A protocol that returns |A_ρ⟩ with probability 1 − δ, as in [1], has fidelity at least 1 − δ. A *permutation protocol* uses only instruments whose Kraus operators are linear combinations of permutations of the registers it holds, the discarding of registers, and classical control; it adds no registers. The algorithms of [1] are permutation protocols [1, proof of Theorem 7].

In [1], O(r/λ_min) copies suffice (Theorem 7), and O(r log(r)/λ_min) copies suffice for a streaming protocol (Theorem 5). The optimal complexity is named there as an open question [1, Section 1.2]: Θ(Σ_i λ_i^{-1}) copies are suggested for permutation protocols, while general protocols might need only Ω(λ_min^{-1}), and it is asked whether a protocol matches that bound.

| | copies for success 1 − δ |
|---|---|
| Previous best bound | O(r/λ_min) [1, Theorem 7] |
| Previous lower bound | Ω(1/λ_min), implicit in [1, Section 1.2] |
| Theorem 3 (every protocol, every d > r, r ≥ 2, δ ≤ 1/12) | Θ(Σ_i 1/λ_i + log(1/δ)/λ_min) |

Since Σ_i 1/λ_i ≥ r², no protocol uses O(1/λ_min) = O(r) copies when the spectrum is flat. For spectra with one small eigenvalue, Σ_i 1/λ_i can be much smaller than r/λ_min, and the algorithm of [1] needs only the smaller count.

## Results

Let L_n be the number of rows of the irrep label obtained by weak symmetric-group sampling of ρ^{⊗n}. Its law depends only on λ_1, …, λ_r. Let G_1, …, G_r be independent geometric variables with P(G_i = j) = λ_i (1 − λ_i)^{j−1} for j ≥ 1.

**Theorem 1 (optimal fidelity).** For all d > r ≥ 1 and n ≥ 1, the maximum over all protocols of the worst-case success is

F*_n = E[ 1 / C(d − L_n, r − L_n) ],

where C denotes a binomial coefficient.

**Theorem 2 (permutation protocols).** The supremum over permutation protocols of the worst-case success is P(L_n = r) = P(G_1 + ⋯ + G_r ≤ n).

**Theorem 3 (copies).** Let r ≥ 2 and δ ≤ 1/12.

(a) Every protocol with worst-case success at least 1 − δ uses n ≥ max{ (1/2) Σ_i 1/λ_i, ln(1/(2δ))/(2λ_min) } copies.

(b) The algorithm of [1, Theorem 7] with confidence parameter δ/2 returns |A_ρ⟩ with probability at least 1 − δ once n ≥ max{ 2 Σ_i 1/λ_i, 7 ln(2/δ)/λ_min }.

## Proofs

*Law of L_n.* L_n has the law of the length of the longest strictly decreasing subsequence of a word of n independent letters from {1, …, r} with probabilities λ_1, …, λ_r [2, Remark 2.24 and Theorem 2.14]. With r letters, a strictly decreasing subsequence of length r is r, r − 1, …, 1. Searching for it greedily, the waiting times for the letters r, r − 1, …, 1 are independent geometric variables, so P(L_n = r) = P(G_1 + ⋯ + G_r ≤ n). This is the counting behind the rank test of [2, Section 6].

*Theorem 2.* Split (ℂ^d)^{⊗m} into its isotypic components, indexed by partitions of m. Permutations of the registers commute with u^{⊗m} for every unitary u, so they map each component to itself. Discarding one register maps a component into components whose partitions have one box less (branching rule), and hence at most as many rows. The state ρ^{⊗n} is block diagonal, with weight P(label = μ) on the component μ. So every branch of a permutation protocol that starts in components with k rows stays in components with at most k rows. The space Λ^r(ℂ^d) of anti-symmetric vectors on r registers is the component with r rows. For k < r the output therefore has fidelity 0 with |A_ρ⟩, and the success is at most P(L_n = r).

Conversely, by [1, Corollary 13] the algorithm of [1, Theorem 7] applied to a component with k rows returns an anti-symmetric state on k registers with probability at least 1 − ε, for any ε > 0. That state lies in Λ^k(supp ρ). For k = r this space is spanned by |A_ρ⟩, so the success is at least (1 − ε) P(L_n = r).

*Upper bound of Theorem 1.* The worst case is at most the average over the following prior: V is a uniformly random r-dimensional subspace, and ρ has the given eigenvalues and a uniformly random orthonormal eigenbasis of V. The weights P(label = μ) do not depend on V or the eigenbasis.

Fix V and a component μ with k rows. Average the normalized block σ_μ(ρ) of ρ^{⊗n} over the eigenbasis. The result is invariant under the unitaries of V. Inside V^{⊗n}, the component μ is an irreducible representation of these unitaries, tensored with the representation of the permutations. So the average is the same as the average of τ_W over a uniformly random k-dimensional subspace W of V, where τ_W is the corresponding normalized projector state of the component μ inside W^{⊗n}. This state is nonzero because μ has k rows, and it is supported on W^{⊗n}.

The pair (W, V) can be drawn the other way round: W uniform of dimension k, then V = W ⊕ V′ with V′ uniform of dimension r − k in W^⊥. For fixed W, the states |A_{W⊕V′}⟩ span the image of Λ^{r−k}(W^⊥) under y ↦ A_W ∧ y. This is an irreducible representation of the unitaries of W^⊥, of dimension C(d − k, r − k). So E_{V′} |A_V⟩⟨A_V| is the normalized projector onto it, with operator norm 1/C(d − k, r − k). Hence the average success on the component μ is at most E_W ‖E_{V′} |A_V⟩⟨A_V|‖ = 1/C(d − k, r − k), whatever Φ(τ_W) is. Summing over μ gives F*_n ≤ E[1/C(d − L_n, r − L_n)].

*Lower bound of Theorem 1.* Run the algorithm of [1, Theorem 7] with parameter ε. With probability at least 1 − ε, it returns k = L_n and a state X on Λ^k(supp ρ). Then apply the completion channel

Ψ_k(X) = Π_anti^{(r)} (X ⊗ I^{⊗(r−k)}) Π_anti^{(r)} / c_k,  c_k = C(d, r)/C(d, k),

extended by any fixed state outside Λ^k(ℂ^d). The functional X ↦ Tr[Π_anti^{(r)}(X ⊗ I)] is invariant on the irreducible space Λ^k(ℂ^d), so it equals c_k Tr X, and Ψ_k is trace preserving. Since Π_anti^{(r)} |A_ρ⟩ = |A_ρ⟩, the fidelity is Tr[X Tr_{r−k}|A_ρ⟩⟨A_ρ|]/c_k. The partial trace is Π_{Λ^k(supp ρ)}/C(r, k), by invariance and irreducibility. So the fidelity is C(d, k)/(C(r, k) C(d, r)) = 1/C(d − k, r − k) for every such X. The success is at least (1 − ε) E[1/C(d − L_n, r − L_n)], and ε > 0 is arbitrary. ∎

*Theorem 3.* Write S = G_1 + ⋯ + G_r and M = E S = Σ_i 1/λ_i, so λ_min M ≥ 1. By [3, Theorems 2.1 and 3.1], P(S ≥ tM) ≤ exp(−λ_min M (t − 1 − ln t)) for t ≥ 1, and P(S ≤ tM) obeys the same bound for t ≤ 1.

(a) For k < r, C(d − k, r − k) ≥ d − r + 1. So Theorem 1 gives F*_n ≤ P(S ≤ n) + (1 − P(S ≤ n))/(d − r + 1). Success 1 − δ therefore forces P(S ≤ n) ≥ 1 − δ(d − r + 1)/(d − r) ≥ 1 − 2δ ≥ 5/6.

- Since P(S ≤ n) ≤ P(G_min ≤ n) = 1 − (1 − λ_min)^n and λ_min ≤ 1/2, we get n ≥ ln(1/(2δ))/(−ln(1 − λ_min)) ≥ ln(1/(2δ))/(2λ_min).
- If n ≤ M/2, then P(S ≤ n) ≤ exp(−(ln 2 − 1/2)) < 0.83 < 5/6. So n > M/2.

(b) For t ≥ 2, t − 1 − ln t ≥ t/7. So P(S > n) ≤ exp(−λ_min n/7) ≤ δ/2 for the stated n. With Theorem 2 and parameter ε = δ/2, the probability of returning |A_ρ⟩ is at least (1 − δ/2)² ≥ 1 − δ. ∎

## Check

`sim/check.py` checks four things, and `sim/sdp.py` a fifth.

- **The law of L_n, in exact rational arithmetic:** P(L_n = r) = P(G_1 + ⋯ + G_r ≤ n), by enumerating all words for r ≤ 4 and n ≤ 8.
- **Agreement with the quantum weights:** the law of L_n from the words equals the weights of ρ^{⊗n} on the isotypic components, for d = 3 and n ≤ 5. The components are found as eigenspaces of the sum of all transpositions.
- **The averaging step and the completion channel:** E_{V′} |A_V⟩⟨A_V| has operator norm 1/C(d − k, r − k), checked by sampling. The constant c_k and the fidelity 1/C(d − k, r − k) of the completion channel are exact for random states X, for (d, r) ∈ {(4, 2), (4, 3), (5, 3)}.
- **The optimum itself:** `sim/sdp.py` solves the semidefinite program for the best covariant channel, which is optimal after averaging over unitaries. Its value equals E[1/C(d − L_n, r − L_n)] up to 1e-6 for eight cases with d ≤ 4, r ≤ 3 and n ≤ 3.
- **The copy bounds:** the constants of Theorem 3, and on random spectra with r ≤ 6, that the smallest n with P(S ≤ n) ≥ 1 − 2δ lies above the bound of (a) and the count of (b) suffices.

## Lean

`lean/AntiSym/Basic.lean` proves the combinatorial and scalar steps: the completion identity C(d, r) C(r, k) = C(d, k) C(d − k, r − k) (`completion_identity`), C(d − k, r − k) ≥ d − r + 1 (`choose_ge`), Σ 1/λ_i ≥ r² (`sum_inv_ge`), and the constants of the copy bounds (`rate_ge`, `lower_tail_constant`, `neg_log_le`, `success_forces`, `two_halves`). `lean/axioms.txt` lists the axioms of every named theorem: only `propext`, `Classical.choice` and `Quot.sound`. The rest of the proofs is a Claim.

## Scope

- Theorem 1 holds for every channel on the n copies, so for every measurement strategy, adaptive or not. The maximum is attained, since the channels form a compact set; the algorithm of [1, Theorem 7] followed by the completion channel approaches it as its confidence parameter goes to 0.
- The completion channel adds registers and then anti-symmetrizes. With that one extra operation, protocols built from permutations reach the value of Theorem 1, so the gap between Theorems 1 and 2 is exactly the effect of added registers.
- Theorem 3 counts copies. The running time of the algorithm is as in [1]. Streaming protocols with small memory are not covered.
- [1, Corollary 13], [2, Remark 2.24 and Theorem 2.14] and [3, Theorems 2.1 and 3.1] are used as stated there. Lean covers only the steps listed in the Lean section.

## References

[1] A. Bene Watts, J. Bostanci, M. C. Caro, D. Grier, S. Liu, G. Mahajan. Anti-symmetrization is cheap and useful. arXiv:2610.06737.

[2] R. O'Donnell, J. Wright. Quantum spectrum testing. Commun. Math. Phys. 387 (2021). arXiv:1501.05028.

[3] S. Janson. Tail bounds for sums of geometric and exponential variables. arXiv:1709.08157.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
