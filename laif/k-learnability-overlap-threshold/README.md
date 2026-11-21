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

For n = 5 and k = 4 this means that five pure states with all overlaps at most 0.6125288 need not be antidistinguishable, while all overlaps at most 0.6123724 guarantee it [2, Corollary 5.4]. In particular the threshold (4) is within 1.6 · 10⁻⁴ of optimal for n = 5 and k = 4. Here W(5, 4) is the Welch bound for five unit vectors in ℂ², which no five vectors in ℂ² attain.

## Proof

A multiset of pure states is k-learnable if and only if its Gram matrix G is k-incoherent, that is, a sum of positive semidefinite matrices each supported on a k × k principal submatrix [1, Proposition 10]. If X is a Hermitian matrix whose k × k principal submatrices are all positive semidefinite, then Tr(X M) = Tr(X_S M_S) ≥ 0 for every positive semidefinite M supported on a k-subset S, so Tr(XG) ≥ 0 for every k-incoherent G. Hence a positive semidefinite G with unit diagonal and Tr(XG) < 0 is the Gram matrix of n pure states that are not k-learnable.

The files `sim/cert_{n}{k}.json` give, for each row, a matrix G and a matrix X with entries in ℚ(i). In exact rational arithmetic: G is Hermitian with unit diagonal and positive definite, |G_ij|² ≤ t_0² for i ≠ j, every k × k principal submatrix of X is positive definite, and Tr(XG) < 0. Positive definiteness is checked by an LDLᵀ elimination of the real form [[A, −B], [B, A]] of each Hermitian matrix A + iB. ∎

## Structure (numerical)

The certificates come from a local search that alternates two semidefinite programs. For fixed X it finds the unit-diagonal G with Tr(XG) ≤ −δ and the least largest overlap. For fixed G it finds the best X. For n = 5 and k = 4 the largest overlap behaves like W(5, 4) + 0.5 √δ as δ → 0. The matrices found have all overlaps equal and rank 3, and as δ → 0 they approach equiangular Gram matrices with all overlaps exactly W(5, 4). Every such matrix has frame potential Σ_{i,j} |G_ij|² = n²/(n − k + 1) and so lies on the boundary of the region covered by [1, Inequality (3)]. For the other rows the search stops at the values in the table.

## Check

`sim/search.py n k seeds δ` runs the alternating search with the solver Clarabel. `sim/certify.py` rounds a numerical pair (G, X) to rationals, shifts G and X by small multiples of the identity, renormalizes G to unit diagonal, checks all conditions exactly and writes `sim/cert_{n}{k}.json`. `sim/check_cert.py` reads the stored files and checks every condition again in exact arithmetic. Output in `sim/out.txt`.

## Scope

- Upper bounds on t*(n, k) for five small cases; t*(n, k) itself is not determined, and the case k = n − 1, n ≥ 5 stays open.
- The certificates are computer-checked in exact rational arithmetic; they are not formalized in Lean.
- The equivalence of k-learnability and k-incoherence is taken from [1, Proposition 10].

## References

[1] N. Johnston, B. Lovitz, V. Russo, J. Sikora. Sharp bounds for perfect quantum state classification beyond antidistinguishability. arXiv:2609.17411.

[2] N. Johnston, V. Russo, J. Sikora. Tight bounds for antidistinguishability and circulant sets of pure quantum states. Quantum 9, 1622 (2025). arXiv:2311.17047.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
