# Auxiliary-free single-copy Clifford testing needs Ω(√n) queries

2026-11-12

## Problem

A tester gets query access to an unknown n-qubit unitary U. It must accept if U is a Clifford unitary and reject if U is ε-far from every Clifford unitary. In the single-copy, auxiliary-free model of [1], each query applies U to an n-qubit state with no ancilla, and the output is measured before the next query. The tester may be adaptive. In [1, Theorem 1.4] such a tester is given with Õ(n/ε³) queries, and [1, Theorem 1.5] shows that Ω(n^{1/4}) queries are necessary. For single-copy stabilizer testing, the corresponding bounds are Ω(√n) and O(n) [4].

## Results

**Theorem 1.** Let 0 < ε < 1 − Ω(n²/2^{2n}). Every auxiliary-free, possibly adaptive, single-copy Clifford tester with accuracy ε and success probability 2/3 uses at least √(2n) − C queries, for an absolute constant C. Previous best bound: Ω(n^{1/4}) [1, Theorem 1.5].

The lower bound now matches that of single-copy stabilizer testing. The gap to the upper bound O(n) stays open.

Theorem 1 comes from the proof of [1, Theorem 6.24], made uniform in t and with a sharper count of its terms. In that proof the entries of the inverse Gram matrix are bounded for fixed t, and the sums over pairs (T, T′) of stochastic Lagrangian subspaces are bounded by 2^{O(t⁴)} terms. Lemma 1 gives explicit bounds on these entries for every t with |Σ_{t,t}| ≤ 2^{n−1}, following the diagonal-dominance argument used for stabilizer testing in [4, Fact 2.28 and Lemma 4.6]. Lemma 2 shows that the three sums of the proof total at most 2^{−n} + 2|Σ_{t,t}| 2^{−n} = 2^{−n+O(t²)}.

## Notation

Σ_{t,t} is the set of stochastic Lagrangian subspaces T ⊂ F₂^{2t} [1, Definition 2.18], and R(T) = r(T)^{⊗n} with r(T) = Σ_{(x,y)∈T} |x⟩⟨y|. For n ≥ t − 1 the R(T) form a basis of the commutant of the t-th tensor power of the Clifford group [1, Theorem 2.19], and |Σ_{t,t}| = Π_{k=0}^{t−2} (2^k + 1) ≤ 2^{(t² + 5t)/2} [1, Fact 2.20]. G is the Gram matrix with G_{T,T′} = tr R(T)†R(T′), and W is its pseudo-inverse [1, Definition 2.21]. Write w = |Σ_{t,t}| 2^{−n}. If w ≤ 1/2, then G is invertible (Lemma 1), so W = G⁻¹, the R(T) are linearly independent, and n ≥ t − 1.

## Proofs

**Lemma 1 (inverse Gram matrix).** If w ≤ 1/2, then G is invertible and |W_{T,T′} − 2^{−nt} δ_{T,T′}| ≤ 2^{−nt} 2^{−n}/(1 − w) for all T, T′ ∈ Σ_{t,t}.

*Proof.* tr r(T)ᵀ r(T′) = |T ∩ T′|. This equals 2^t for T = T′ and is at most 2^{t−1} for T ≠ T′, since distinct subspaces of dimension t meet in a subspace of dimension at most t − 1. So G = 2^{nt}(I + E) with E_{T,T} = 0 and |E_{T,T′}| ≤ 2^{−n}. Then ‖E‖_op ≤ w ≤ 1/2, (I + E)⁻¹ = Σ_k (−E)^k, and |(E^k)_{T,T′}| ≤ |Σ_{t,t}|^{k−1} 2^{−nk} = 2^{−n} w^{k−1}. Summing over k ≥ 1 gives the bound. ∎

**Lemma 2 (total variation against the depolarizing channel).** Let w ≤ 1/2 (this implies t ≤ n + 1). For every auxiliary-free, possibly adaptive single-copy algorithm with t queries, the leaf distributions under the completely depolarizing channel and under a uniformly random Clifford unitary are at total variation distance at most 2^{−n} + 2w.

*Proof.* The proof of [1, Theorem 6.24] splits the distance into three sums, eq. (175) to (184), using |tr R(T′)†ρ_ℓ| ≤ 1 [1, Corollary 6.11], Σ_ℓ tr M_ℓ = 2^{nt} and Σ_ℓ |tr R(T)M_ℓ| ≤ 2^{n(t−1)} for T ≠ e [1, Theorem 6.8 and (183)], from [4]. With Lemma 1 and a = 2^{−n}/(1 − w):

- the (e, e) term is at most (1/2) a ≤ 2^{−n};
- the (e, T′) terms with T′ ≠ e are at most (1/2)(|Σ_{t,t}| − 1) a ≤ w;
- the terms with T ≠ e are at most (1/2) 2^{−n} (|Σ_{t,t}| − 1)(1 + a + (|Σ_{t,t}| − 1) a) ≤ (w/2)(1 + w/(1 − w)) ≤ w.

The sum of the three is at most 2^{−n} + 2w. ∎

*Proof of Theorem 1.* By the triangle inequality [1, (150)], the leaf distributions under a uniformly random unitary and under a random Clifford unitary are at total variation distance at most O(t³/2^n) [1, Theorem 6.5] plus the bound of Lemma 2. By [1, Lemma 6.3] and the two-point method [1, Lemma 6.2], a tester with t queries forces this distance to be at least an absolute constant c > 0, up to 2^{−Ω(n²)}. If t² + 5t ≤ 2n − 2 log₂(8/c), then 2w ≤ 2^{1 − n + (t² + 5t)/2} ≤ c/4, and for n large enough the whole distance is below c. Hence t² + 5t > 2n − 2 log₂(8/c), which gives t ≥ √(2n) − C. ∎

## Check

`sim/commutant.py` enumerates Σ_{t,t} for t = 2, 3, 4 and 5 and checks with asserts:

- the count Π_{k=0}^{t−2}(2^k + 1), which is 2, 6, 30 and 270;
- the bound |T ∩ T′| ≤ 2^{t−1} for T ≠ T′;
- the entry bound of Lemma 1, after inverting the Gram matrix numerically for every n ≤ 39 with w ≤ 1/2;
- the three sums of Lemma 2, evaluated with the exact entries of W, against 2^{−n} + 2w.

Output in `sim/commutant_out.txt`.

## Scope

- **Assuming:** the description of the commutant [1, Theorem 2.19 and Fact 2.20], from [2]; the partial-transpose bounds [1, Theorem 6.8 and Corollary 6.11], the first from [4]; the reduction [1, Lemma 6.3 and Fact 6.4]; and the bound for uniformly random unitaries [1, Theorem 6.5], from [3].
- **Not formalized:** the results have no Lean proof.
- The bound is for auxiliary-free single-copy testers, as in [1]. The constant C is not made explicit, since the constants of [1, Theorem 6.5 and Lemma 6.3] are not.

## References

[1] M. Hinsche, Z. Bao, P. van Dordrecht, J. Eisert, J. Briët, J. Helsen. Clifford testing: algorithms and lower bounds. arXiv:2510.07164.

[2] D. Gross, S. Nezami, M. Walter. Schur-Weyl duality for the Clifford group with applications: property testing, a robust Hudson theorem, and de Finetti representations. Commun. Math. Phys. 385 (2021). arXiv:1712.08628.

[3] S. Chen, J. Cotler, H.-Y. Huang, J. Li. Exponential separations between learning with and without quantum memory. FOCS 2021. arXiv:2111.05881.

[4] M. Hinsche, J. Helsen. Single-copy stabilizer testing. arXiv:2410.07986.

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
