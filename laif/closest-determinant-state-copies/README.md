# Learning the closest determinant state from single-copy measurements

2026-11-23

## Problem

A determinant state of n fermions in m modes is the antisymmetrized product of n orthonormal orbitals u_1, …, u_n ∈ ℂ^m. If U is the m × n matrix with these columns, the state is written |S(U)⟩, and ⟨S(U)|S(V)⟩ = det(U†V). Given copies of an unknown n-fermion state ρ, the task of [1] is to output a determinant state S with

⟨S|ρ|S⟩ ≥ OPT − ε,  OPT = max_U ⟨S(U)|ρ|S(U)⟩,

with probability at least 1 − δ. The quantum algorithm of [1] works in two stages:
- It first estimates the one-particle reduced density matrix to operator-norm error of order ε/n, which costs O(m² n² log(m/δ)/ε²) copies [1, Appendix C].
- It then searches a finite set of determinant states in an active space of dimension O(n²/ε). This search uses the threshold search procedure, with entangled measurements on Õ(n⁶/ε⁴) copies [1, Theorem 2].

| | copies for fidelity OPT − ε | measurements |
|---|---|---|
| Previous best bound [1, Theorem 2 and Appendix C] | O(m² n² log(m/δ)/ε²) + Õ(n⁶/ε⁴) | entangled across copies |
| Theorem 1 | O(√m log m · (m n log(n/ε) + log(1/δ))/ε²) | single copy, random matchgate circuits |
| Proposition 2 (every algorithm) | Ω(log(1/δ)/ε²) | |

So the copy count is Õ(n m^{3/2}/ε²). The exponent of 1/ε is optimal. Up to logarithms, the bound lies below the first term O(m² n²/ε²) of the previous bound by a factor of order √m · n, and it has no term n⁶/ε⁴. If n > m/2, then n can be replaced by m − n.

## Results

**Theorem 1.** Measure each of N copies of ρ in the occupation basis after a uniformly random circuit from the discrete matchgate ensemble of [2], and form the classical shadow of [2]. Here N = 612 b(m) (2mk ln(1 + 6√k/ε) + ln(2/δ))/ε², with k = min{n, m − n}. The constant b(m) is the variance bound of [2, eq. (40)], and b(m) = O(√m log m) [2, Appendix F]. Then a determinant state S with ⟨S|ρ|S⟩ ≥ OPT − ε can be computed from the outcomes with probability at least 1 − δ. The measurements are fixed in advance and act on one copy at a time.

The estimator of each fidelity is computed classically in time polynomial in m [2, Theorem 2]. The selection runs over a set of exp(O(mk log(k/ε))) states, so the total running time is exponential in mk. The algorithm of [1] runs in time m^{poly(n,1/ε)}.

**Remark (active space).** Suppose the selection step of [1, Theorem 2] uses the same shadows, on its set of determinant states with orbitals in an active space of dimension r = O(n²/ε). Then that step needs O(b(m) (n r log(n/ε) + log(1/δ))/ε²) = Õ(√m n³/ε³) single-copy measurements instead of Õ(n⁶/ε⁴) entangled ones. Its running time is that of [1].

**Proposition 2.** Let m ≥ n + 1, 0 < ε ≤ 1/8 and δ < 1/4. Every algorithm that learns the closest determinant state to fidelity OPT − ε with probability 1 − δ, with any joint measurement on its N copies, needs N ≥ ln(1/(4δ))/(64ε²).

## Proof

**Lemma 1 (Lipschitz bound).** Let U, V be m × n matrices with orthonormal columns. Then |⟨S(U)|ρ|S(U)⟩ − ⟨S(V)|ρ|S(V)⟩| ≤ ‖U − V‖_F for every state ρ.

*Proof.* For two unit vectors the difference of their projectors has eigenvalues ±√(1 − |⟨a|b⟩|²) and 0. So the left side is at most √(1 − |det(U†V)|²). Let σ_1, …, σ_n ∈ [0, 1] be the singular values of U†V. Then 1 − ∏σ_i² ≤ Σ(1 − σ_i²) ≤ 2Σ(1 − σ_i). The first inequality holds because 1 − ∏a_i ≤ Σ(1 − a_i) for a_i ∈ [0, 1], and the second because 1 − σ² ≤ 2(1 − σ). Finally ‖U − V‖_F² = 2n − 2 Re tr(U†V) ≥ 2n − 2Σσ_i, since |tr(U†V)| ≤ Σσ_i.

**The finite set.** The matrices with orthonormal columns lie on the sphere of radius √n in ℝ^{2mn}. A maximal subset with pairwise distances at least ε/3 has at most (1 + 6√n/ε)^{2mn} elements, because the balls of radius ε/6 around its points are disjoint and lie in the ball of radius √n + ε/6. Its points are determinant states, and by Lemma 1 every determinant state has a point within fidelity ε/3.

**Selection.** By [2, eqs. (36) and (40)], the single-shot shadow estimate of tr(ϱρ) has second moment at most b(m), for every state ρ and every density operator ϱ of a pure free-fermion state. Every determinant state is such a state. Split the N shots into K = 2 ln(2M/δ) groups of 34 · 9 b(m)/ε² shots and take the median of the group means. By [3, Theorem 1], all M fidelities are then estimated to within ε/3 with probability at least 1 − δ. Output the point with the largest estimate. Its fidelity is at least that of the best point minus 2ε/3, and so at least OPT − ε. The particle-hole map is a free-fermion unitary that maps n-fermion determinant states to (m − n)-fermion determinant states, and the matchgate ensemble is invariant under it. This gives k = min{n, m − n}.

**Proposition 2.** Take two orthogonal determinant states S_1, S_2 and ρ_± = (1/2 ± 2ε)|S_1⟩⟨S_1| + (1/2 ∓ 2ε)|S_2⟩⟨S_2|. For ρ_+ we have OPT ≥ 1/2 + 2ε. Let a = |⟨S|S_1⟩|² and b = |⟨S|S_2⟩|², so a + b ≤ 1. A state S with fidelity at least 1/2 + ε satisfies (a + b)/2 + 2ε(a − b) ≥ 1/2 + ε, so a − b ≥ 1/2. For ρ_− the same argument gives b − a ≥ 1/2. So the algorithm distinguishes ρ_+^{⊗N} from ρ_−^{⊗N} with both errors at most δ. Both states are diagonal in one product basis, so the error sum of any test is at least one minus the total variation distance of the two coin sequences with biases 1/2 ± 2ε, which is at least (1/2) exp(−N D). Here D = 4ε ln((1 + 4ε)/(1 − 4ε)) ≤ 64ε² is their relative entropy per copy. Hence 2δ ≥ (1/2) exp(−64Nε²).

## Check

`sim/bvar.py`, output in `sim/out_bvar.txt`:
- computes b(m) from [2, eq. (40)] exactly (rational arithmetic) for m ≤ 12 and in floating point up to m = 256;
- asserts that b(m) is increasing and at most 1.5 √m ln(m + 1) for m ≤ 128; for example b(256) = 40.08.

`sim/mgshadow.py`, output in `sim/out_mgshadow.txt`, for m = 3:
- enumerates the discrete matchgate group, all 46080 signed permutations of the six self-adjoint generators of the fermionic algebra;
- checks the eigenvalues of the shadow channel and that the estimator is unbiased;
- computes the largest second moment of the fidelity estimator over n-particle states, for random determinant states with n = 1, 2. It is 2.0, equal to b(3) = 2.

`sim/net.py`, output in `sim/out_net.txt`:
- checks det(U†V) = ⟨S(U)|S(V)⟩ and the chain of inequalities in Lemma 1 on 3000 random instances with m ≤ 7;
- checks the reduction a − b ≥ 1/2 and the bound D ≤ 64ε² of Proposition 2.

## Scope

- Theorem 1 bounds copies. Its running time is exponential in m·min{n, m − n}, and [1] gives an algorithm with running time m^{poly(n,1/ε)}. The remark keeps that running time and improves only the selection step.
- The variance bound b(m) and its order √m log m are taken from [2]. For m = 3 they are checked exactly here.
- Between Proposition 2 and Theorem 1 the dependence on m and n remains open.
- The statements are Claims with the listed checks.

## References

1. N. Paul, H. Zhao, D. D. Dai. Learning the closest Slater determinant. arXiv:2607.20623 (2026).
2. K. Wan, W. J. Huggins, J. Lee, R. Babbush. Matchgate shadows for fermionic quantum simulation. Communications in Mathematical Physics 404, 629 (2023). arXiv:2207.13723.
3. H.-Y. Huang, R. Kueng, J. Preskill. Predicting many properties of a quantum system from very few measurements. Nature Physics 16, 1050-1057 (2020).

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
