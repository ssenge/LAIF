# Overlap thresholds for perfect classification of pure states with k guesses

2026-11-21

## Problem

A multiset {|ψ_1⟩, …, |ψ_n⟩} of pure states is k-learnable if some POVM {M_I}, indexed by the subsets I of size k, has ⟨ψ_i|M_I|ψ_i⟩ = 0 whenever i ∉ I. A measurement then names k candidates that always contain the true index [1, Definition 1]. For k = n − 1 this is antidistinguishability. Let t*(n, k) be the largest t such that every multiset of n pure states with |⟨ψ_i|ψ_j⟩| ≤ t for all i ≠ j is k-learnable. Then

W(n, k) = √((k − 1)/((n − 1)(n − k + 1))) ≤ t*(n, k) ≤ (k − 1)/(n − 1),

by [1, Theorem 2, Inequality (4)] and [1, Theorem 3, Inequality (6)]. The lower bound is tight for k = 2 [1], and for k = n − 1 with n ≤ 4 [2, Section 6]. The optimality of Inequality (4) is left open in [1, Section 1.1]. For k = n − 1 and n ≥ 5 it is open in [2, Section 6].

Previous best bounds for the smallest open cases:

| n | k | lower bound W(n, k) | upper bound |
|---|---|---|---|
| 5 | 4 | √(3/8) = 0.6123724 | 3/4 |
| 5 | 3 | √(1/6) = 0.4082483 | 1/2 |
| 6 | 3 | √(1/10) = 0.3162278 | 2/5 |
| 6 | 4 | √(1/5) = 0.4472136 | 3/5 |
| 6 | 5 | √(2/5) = 0.6324555 | 4/5 |

## Result

**Theorem 1.** For each row below there are n pure states with |⟨ψ_i|ψ_j⟩| ≤ t_0 for all i ≠ j that are not k-learnable. Hence t*(n, k) ≤ t_0.

| n | k | t_0 | t_0 − W(n, k) |
|---|---|---|---|
| 5 | 4 | 0.612528751 | 1.6 · 10⁻⁴ |
| 5 | 3 | 0.410428727 | 2.2 · 10⁻³ |
| 6 | 3 | 0.319134087 | 2.9 · 10⁻³ |
| 6 | 4 | 0.461190778 | 1.4 · 10⁻² |
| 6 | 5 | 0.703912114 | 7.1 · 10⁻² |

For n = 5 and k = 4 this means that five pure states with all overlaps at most 0.6125288 need not be antidistinguishable, while all overlaps at most 0.6123724 guarantee it [2, Corollary 5.4]. In particular the threshold (4) is within 1.6 · 10⁻⁴ of optimal for n = 5 and k = 4. Here W(5, 4) is the smallest possible largest overlap of five unit vectors in ℂ², and no five vectors in ℂ² attain it.

## Proof

A multiset of pure states is k-learnable if and only if its Gram matrix G is k-incoherent, that is, a sum of positive semidefinite matrices each supported on a k × k principal submatrix [1, Proposition 10]. If X is a Hermitian matrix whose k × k principal submatrices are all positive semidefinite, then Tr(X M) = Tr(X_S M_S) ≥ 0 for every positive semidefinite M supported on a k-subset S, so Tr(XG) ≥ 0 for every k-incoherent G. Hence a positive semidefinite G with unit diagonal and Tr(XG) < 0 is the Gram matrix of n pure states that are not k-learnable.

The files `sim/cert_{n}{k}.json` give, for each row, a matrix G and a matrix X with entries in ℚ(i). In exact rational arithmetic: G is Hermitian with unit diagonal and positive definite, |G_ij|² ≤ t_0² for i ≠ j, every k × k principal submatrix of X is positive definite, and Tr(XG) < 0. Positive definiteness is checked by an LDLᵀ elimination of the real form [[A, −B], [B, A]] of each Hermitian matrix A + iB. ∎

## Lean

The module `lean/KLearn/Basic.lean` defines k-learnability of a family of vectors in ℂ^d (a POVM indexed by the k-subsets whose outcome always contains the index of the state) and proves, for every n, d and k:

- `trace_nonneg_of_kLearnable`: if the family is k-learnable and every k × k principal submatrix of Y is positive semidefinite, then Tr(YG) ≥ 0 for the Gram matrix G.
- `not_kLearnable`: so a witness Y with Re Tr(YG) < 0 shows that the family is not k-learnable.
- `exists_unit_not_kLearnable`: normalization, from a family with real positive norms and normalized overlaps at most t to unit vectors with overlaps of modulus at most t.

The proof goes straight from the measurement: each POVM element M_I annihilates ψ_i for i ∉ I, so the matrix of M_I in the basis of the states is supported on I × I, and Tr(Y · that matrix) ≥ 0 because the entrywise product of two positive semidefinite matrices is positive semidefinite. It does not use [1, Proposition 10].

`lean/KLearn/Instance54.lean` checks one instance for n = 5, k = 4: five vectors in ℚ(i)³ (`Data54.lean`), a witness Y whose 4 × 4 principal submatrices are written as L diag(d) Lᴴ with d ≥ 0, and Tr(YG) < 0, all by `norm_num` in exact arithmetic. The theorem `Instance54.main` states that there are five unit vectors in ℂ³ with all overlaps of modulus at most 0.612528754 that are not 4-learnable. This instance is a separate rounding of the same numerical solution as `sim/cert_54.json`, so its t_0 differs from the table in the ninth digit. `lean/axioms.txt` lists the axioms of every named theorem: only `propext`, `Classical.choice` and `Quot.sound`.

## Structure (numerical)

The certificates come from a local search that alternates two semidefinite programs. For fixed X it finds the unit-diagonal G with Tr(XG) ≤ −δ and the least largest overlap. For fixed G it finds the best X. For n = 5 and k = 4 the largest overlap behaves like W(5, 4) + 0.5 √δ as δ → 0. The matrices found have all overlaps equal and rank 3, and as δ → 0 they approach equiangular Gram matrices with all overlaps exactly W(5, 4). Every such matrix has frame potential Σ_{i,j} |G_ij|² = n²/(n − k + 1) and so lies on the boundary of the region covered by [1, Inequality (3)]. For the other rows the search stops at the values in the table.

## Check

`sim/search.py n k seeds δ` runs the alternating search with the solver Clarabel. `sim/certify.py` rounds a numerical pair (G, X) to rationals, shifts G and X by small multiples of the identity, renormalizes G to unit diagonal, checks all conditions exactly and writes `sim/cert_{n}{k}.json`. `sim/check_cert.py` reads the stored files and checks every condition again in exact arithmetic. Output in `sim/out.txt`. `sim/gen_lean.py sim/G54.npy sim/X54.npy lean/KLearn/Data54.lean` rounds the stored (5, 4) solution, checks the factorizations exactly and writes the Lean data module.

## Scope

- Upper bounds on t*(n, k) for five small cases; t*(n, k) itself is not determined, and the case k = n − 1, n ≥ 5 stays open.
- Lean covers the soundness of the witness for all n, d and k, and the case n = 5, k = 4 with t_0 = 0.612528754.
- Not formalized: the rows (5, 3), (6, 3), (6, 4) and (6, 5), which are checked in exact rational arithmetic by `sim/check_cert.py`, and the search itself.

## References

[1] N. Johnston, B. Lovitz, V. Russo, J. Sikora. Sharp bounds for perfect quantum state classification beyond antidistinguishability. arXiv:2609.17411.

[2] N. Johnston, V. Russo, J. Sikora. Tight bounds for antidistinguishability and circulant sets of pure quantum states. Quantum 9, 1622 (2025). arXiv:2311.17047.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
