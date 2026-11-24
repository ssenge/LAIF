# Learning the closest determinant state from single-copy measurements

2026-11-23

## Problem

A determinant state of n fermions in m modes is the antisymmetrized product of n orthonormal orbitals u_1, …, u_n ∈ ℂ^m. If U is the m × n matrix with these columns, the state is written |S(U)⟩, and ⟨S(U)|S(V)⟩ = det(U†V). Given copies of an unknown n-fermion state ρ, the task of [1] is to output a determinant state S with

⟨S|ρ|S⟩ ≥ OPT − ε,  OPT = max_U ⟨S(U)|ρ|S(U)⟩,

with probability at least 1 − δ. The quantum algorithm of [1] works in two stages:
- It first estimates the one-particle reduced density matrix to operator-norm error of order ε/n, which costs O(m² n² log(m/δ)/ε²) copies [1, Appendix C].
- It then runs the threshold search procedure over a finite set of determinant states in an active space of dimension O(n²/ε). This uses entangled measurements on Õ(n⁶/ε⁴) copies [1, Theorem 2].

Below, k = min{n, m − n}, and ‖·‖₂ is the entrywise norm, the square root of the sum of the squared moduli of all entries.

| | copies for fidelity OPT − ε | measurements | time per fidelity estimate |
|---|---|---|---|
| Previous best bound [1, Theorem 2 and Appendix C] | O(m² n² log(m/δ)/ε²) + Õ(n⁶/ε⁴) | entangled across copies | |
| Theorem 1, implied by [3] | O((mk log(k/ε) + log(1/δ))/ε²) | single copy, global random circuits of [3] on the m-qubit encoding | C(m, k) · poly(m) |
| Theorem 2, fermionic measurements | O(b(m) (mk log(k/ε) + log(1/δ))/ε²) | single copy, random matchgate circuits of [2] | poly(m) |
| Proposition 3 (every algorithm, n ≥ 1) | Ω(log(1/δ)/ε²) | | |
| Proposition 5 (every algorithm, 1 ≤ n ≤ m − 1, δ ≤ 1/2) | Ω(m/(ε log(2 + εm))) | any, entangled across copies | |
| Proposition 5 (non-adaptive single-copy algorithms, δ ≤ 1/2) | Ω(m/ε²) | each copy measured alone, measurements fixed in advance | |
| Corollary 4, closest pure free-fermion state | O((m² log(m/ε) + log(1/δ))/ε²) | as in Theorem 1 | |

The exponent of 1/ε in Theorem 1 is optimal by Proposition 3. Among non-adaptive single-copy algorithms, the class of Theorems 1 and 2, Theorem 1 is optimal up to the factor k log(k/ε) by Proposition 5, so for n = 1 or n = m − 1 up to log(1/ε). Asymptotically, the copy count Õ(nm/ε²) of Theorem 1 lies below the first term of the previous bound by a factor of order mn up to a logarithm, and it has no term n⁶/ε⁴. The constants of [1] are not stated, so no crossover point is given.

## Results

**Theorem 1 (implied by [3]).** Encode the m modes in m qubits, one per mode. Measure each of N copies of ρ in the computational basis after a uniformly random circuit from the global ensemble of [3], and form the classical shadows of [3]. Here, up to rounding, N = 1836 (2mk ln(1 + 6√k/ε) + ln(2/δ))/ε². A determinant state S with ⟨S|ρ|S⟩ ≥ OPT − ε can then be computed from the outcomes with probability at least 1 − δ. The measurements are fixed in advance and act on one copy at a time.

The selection runs over a set of exp(O(mk log(k/ε))) states, so the total running time is exponential in mk. The algorithm of [1] runs in time m^{poly(n,1/ε)}.

**Theorem 2 (fermionic measurements).** The same holds with the random matchgate circuits of [2] and, up to rounding, N = 612 b(m) (2mk ln(1 + 6√k/ε) + ln(2/δ))/ε². Here b(m) is the variance bound of [2, eq. (40)]. It is at most 1.5 √m ln(m + 1) for m ≤ 128 (`sim/bvar.py`), and of order √m log m by the asymptotic argument of [2, Appendix F]. These circuits preserve the fermionic structure, and each fidelity estimate is computed in time polynomial in m [2, Theorem 2].

**Remark (active space).** Keep the first stage of [1], and run the selection step of [1, Theorem 2] with the shadows of Theorem 1 on fresh copies, independent of the first stage, over its set of determinant states with orbitals in the active space of dimension r = O(n²/ε). That step then needs O((n r log(n/ε) + log(1/δ))/ε²) = Õ(n³/ε³) single-copy measurements, independent of m, instead of Õ(n⁶/ε⁴) entangled ones. The fidelity estimates cost m^{O(n)} time each, which fits in the running time m^{poly(n,1/ε)} of [1].

**Proposition 3.** Let n ≥ 1, m ≥ n + 1, 0 < ε ≤ 1/8 and δ < 1/4. Every algorithm that learns the closest determinant state to fidelity OPT − ε with probability 1 − δ, with any joint measurement on its N copies, needs N ≥ ln(1/(4δ))/(64ε²).

**Corollary 4 (pure free-fermion states).** A pure free-fermion state of m modes is determined by its covariance matrix M_{ab} = (i/2)⟨[c_a, c_b]⟩, where c_1, …, c_{2m} are the self-adjoint generators of the fermionic algebra. M is real antisymmetric with M² = −I. Let OPT_G be the largest fidelity of an arbitrary state ρ of m modes with such a state. With the measurements of Theorem 1 and, up to rounding, N = 1836 (m(2m − 1) ln(1 + 3√m/ε) + ln(2/δ))/ε² copies, a pure free-fermion state of fidelity at least OPT_G − ε is computed with probability at least 1 − δ. With the matchgate circuits of Theorem 2, N = 612 b(m) (m(2m − 1) ln(1 + 3√m/ε) + ln(2/δ))/ε² copies suffice. The lower bound of Proposition 3 holds here as well, with the vacuum and a two-particle occupation state as the two orthogonal states. In [1, Section VII] the closest such state is named as a direction for further study.

**Proposition 5 (dependence on m).** Let 1 ≤ n ≤ m − 1, 0 < ε ≤ 1/8, d = max{n, m − n} + 1, and let an algorithm output a determinant state of fidelity at least OPT − ε with probability at least 1 − δ on every n-fermion state. Then:
- if it measures each copy separately with measurements fixed in advance, N ≥ ((1 − δ)(d − 1) ln 8 − ln 2)/(64ε²);
- for any joint measurement on the N copies, N ≥ ((1 − δ)(d − 1) ln 8 − ln 2)/((8ε + 1/d) ln(1 + 8εd)).

## Proof

**Lemma 1 (overlap bound).** Let U, V be m × n matrices with orthonormal columns. Then |⟨S(U)|ρ|S(U)⟩ − ⟨S(V)|ρ|S(V)⟩| ≤ ‖U − V‖₂ for every state ρ.

*Proof.* For two unit vectors the difference of their projectors has eigenvalues ±√(1 − |⟨a|b⟩|²) and 0. So the left side is at most √(1 − |det(U†V)|²). Let σ_1, …, σ_n ∈ [0, 1] be the singular values of U†V. Then 1 − ∏σ_i² ≤ Σ(1 − σ_i²) ≤ 2Σ(1 − σ_i). The first inequality holds because 1 − ∏a_i ≤ Σ(1 − a_i) for a_i ∈ [0, 1], and the second because 1 − σ² ≤ 2(1 − σ). Finally ‖U − V‖₂² = 2n − 2 Re tr(U†V) ≥ 2n − 2Σσ_i, since |tr(U†V)| ≤ Σσ_i.

**The finite set.** The matrices with orthonormal columns lie on the sphere of radius √n in ℝ^{2mn}. A maximal subset with pairwise distances at least ε/3 has at most (1 + 6√n/ε)^{2mn} elements, because the balls of radius ε/6 around its points are disjoint and lie in the ball of radius √n + ε/6. Its points are determinant states, and by Lemma 1 every determinant state has a point within fidelity ε/3. Such a set is fixed in advance. A greedy pass over a fine grid gives one with the same bounds up to a factor close to 1 in the radii. The orthonormal complements satisfy |det(U†V)| = |det(U_⊥†V_⊥)|, so the same holds with n replaced by m − n, and hence by k.

**Selection.** Let v bound the second moment of the single-shot shadow estimate of each fidelity. The shadow channel preserves the trace, so the variance is at most v, and the median-of-means argument of [3, Theorem 1] uses only this variance bound. Split the N shots into ⌈2 ln(2M/δ)⌉ groups of ⌈306 v/ε²⌉ shots and take the median of the group means. All M fidelities are then estimated to within ε/3 with probability at least 1 − δ. Output the point with the largest estimate. Its fidelity is at least that of the best point minus 2ε/3, and so at least OPT − ε.
- For Theorem 1, v = 3: for the global ensemble the shadow norm of a pure-state projector is at most 3 [3], and the constant part adds nothing to the variance. One estimate is (2^m + 1)|⟨b|C|S⟩|² − 1, with C the random circuit and b the outcome. The amplitude ⟨b|C|S⟩ is a sum over the C(m, n) occupation patterns of a minor of U times an amplitude of a stabilizer state.
- For Theorem 2, v = b(m): by [2, eqs. (36) and (40)], the single-shot estimate of tr(ϱρ) has second moment at most b(m), for every state ρ and every density operator ϱ of a pure free-fermion state. Every determinant state is such a state.

**Proposition 3.** Take two orthogonal determinant states S_1, S_2 and ρ_± = (1/2 ± 2ε)|S_1⟩⟨S_1| + (1/2 ∓ 2ε)|S_2⟩⟨S_2|. For ρ_+ we have OPT = 1/2 + 2ε. Let a = |⟨S|S_1⟩|² and b = |⟨S|S_2⟩|², so a + b ≤ 1. A state S with fidelity at least 1/2 + ε satisfies (a + b)/2 + 2ε(a − b) ≥ 1/2 + ε, so a − b ≥ 1/2. For ρ_− the same argument gives b − a ≥ 1/2. So the algorithm distinguishes ρ_+^{⊗N} from ρ_−^{⊗N} with both errors at most δ. Both states are diagonal in one product basis, so the error sum of any test is at least one minus the total variation distance of the two coin sequences with biases 1/2 ± 2ε. That is at least (1/2) exp(−N D), where D = 4ε ln((1 + 4ε)/(1 − 4ε)) ≤ 64ε² is their relative entropy per copy. Hence 2δ ≥ (1/2) exp(−64Nε²).

**Proposition 5.** Take n ≤ m − n; otherwise exchange particles and holes, a free-fermion map that sends determinant states to determinant states, so d = m − n + 1 in both cases after relabelling. Fix the core orbitals e_1, …, e_{n−1}, and put the last particle in the d remaining modes, in the one-particle state ρ_v = (1 − β)I/d + βvv† with β = 8ε and v a uniformly random unit vector of ℂ^d. The n-fermion state ρ is the core with ρ_v added.
- *Reduction.* For a determinant state S′, let ψ ∈ ℂ^d be its amplitudes on the configurations core ∪ {j}. Then ⟨S′|ρ|S′⟩ = ⟨ψ|ρ_v|ψ⟩ and ‖ψ‖ ≤ 1, so u = ψ/‖ψ‖ satisfies ⟨u|ρ_v|u⟩ ≥ ⟨S′|ρ|S′⟩. Also OPT = λ_max(ρ_v), attained by the core with v. Since λ_max(ρ_v) − ⟨u|ρ_v|u⟩ = β(1 − |⟨u|v⟩|²), a successful output gives a unit vector u with |⟨u|v⟩|² ≥ 7/8.
- *Guessing.* For uniformly random v, the probability that |⟨u|v⟩|² ≥ 7/8 for a fixed u is 8^{−(d−1)}. Let Z indicate success. Comparing the joint law of (v, outcomes) with the product of its marginals, the binary relative entropy gives (1 − δ) ln 8^{d−1} − ln 2 ≤ J, where J is the mutual information between v and the outcomes.
- *Single copies.* With measurements fixed in advance, the outcomes are independent given v, so J ≤ Σ_t J_t. If the measurements are drawn from a random seed shared across copies, the same holds conditioned on the seed, which is independent of v, with J_t the mutual information of v and the outcome of copy t. Each measurement acts on ρ_v through a measurement on ℂ^d, refined into rank-one elements w_x|φ_x⟩⟨φ_x| with Σw_x = d. The average outcome law is w_x/d. Its χ² divergence from the law under v, averaged over v, is Σ_x w_x d β² Var|⟨φ_x|v⟩|² = β²(d − 1)/(d + 1) ≤ 64ε², since |⟨φ|v⟩|² has the law Beta(1, d − 1). Relative entropy is at most the χ² divergence, so J_t ≤ 64ε².
- *Joint measurements.* The average of ρ_v is I/d, so by subadditivity and the bound of accessible information by the entropy difference, J ≤ N(ln d − S(ρ_v)). This is the relative entropy of ρ_v to I/d, at most (β + 1/d) ln(1 + βd).

**Corollary 4.** For two pure free-fermion states with covariance matrices M_1, M_2, |⟨ψ_1|ψ_2⟩|² = √det((M_1 + M_2)/2). Write M_1 + M_2 = M_1(I + O) with O = M_1ᵀM_2 orthogonal. Its eigenvalues are e^{±iθ_j}, j = 1, …, m, and det M_1 = 1, so |⟨ψ_1|ψ_2⟩|² = ∏_j |cos(θ_j/2)|. Then 1 − ∏_j |cos(θ_j/2)| ≤ Σ_j sin²(θ_j/2) = ‖I − O‖₂²/8 = ‖M_1 − M_2‖₂²/8. As in Lemma 1, the two fidelities with ρ differ by at most ‖M_1 − M_2‖₂/(2√2). The covariance matrices lie on the sphere of radius √(2m) in the space of antisymmetric matrices, which has dimension m(2m − 1). A maximal subset with pairwise distances at least 2√2ε/3 has at most (1 + 3√m/ε)^{m(2m−1)} elements, and every pure free-fermion state is within fidelity ε/3 of one of them. The variance bounds 3 of [3] and b(m) of [2] hold for every pure free-fermion state, of either parity, so the selection step is unchanged.

## Check

`sim/bvar.py`, output in `sim/out_bvar.txt`:
- computes b(m) from [2, eq. (40)] exactly (rational arithmetic) for m ≤ 12 and in floating point up to m = 256;
- asserts that b(m) is increasing and at most 1.5 √m ln(m + 1) for m ≤ 128. For example b(256) = 40.08, and b(m) > 3 from m = 6 on.

`sim/mgshadow.py`, output in `sim/out_mgshadow.txt`, for m = 3:
- enumerates the discrete matchgate group, all 46080 signed permutations of the six self-adjoint generators of the fermionic algebra;
- checks the eigenvalues of the shadow channel on the even monomials and that the estimator is unbiased;
- computes the largest second moment of the fidelity estimator over n-particle states, for random determinant states with n = 1, 2. It is 2.0, equal to b(3) = 2.

`sim/net.py`, output in `sim/out_net.txt`:
- checks det(U†V) = ⟨S(U)|S(V)⟩ and the chain of inequalities in Lemma 1 on 3000 random instances with m ≤ 7;
- checks the reduction a − b ≥ 1/2 and the bound D ≤ 64ε² of Proposition 3.

`sim/lower.py`, output in `sim/out_lower.txt`: it checks the reduction ⟨S′|ρ|S′⟩ = ⟨ψ|ρ_v|ψ⟩ with ‖ψ‖ ≤ 1 on 400 random instances with m ≤ 7, the identity λ_max − ⟨u|ρ_v|u⟩ = β(1 − |⟨u|v⟩|²), the cap probability (by sampling), the averaged χ² divergence (by sampling), and the relative-entropy bound on a grid.

`sim/quasifree.py`, output in `sim/out_quasifree.txt`: for 600 pairs of random pure free-fermion states of both parities with m ≤ 4, it checks M² = −I, the overlap formula, the bound 1 − |⟨ψ_1|ψ_2⟩|² ≤ ‖M_1 − M_2‖₂²/8, which is attained up to 10⁻⁴ by close pairs, and the fidelity bound for random states ρ.

## Lean

`lean/DetState/Basic.lean` proves the scalar steps of the proofs:

- `one_sub_prod_le_sum`: 1 − ∏a_i ≤ Σ(1 − a_i) for a_i ∈ [0, 1] (Lemma 1 and Corollary 4);
- `one_sub_sq_le`: 1 − σ² ≤ 2(1 − σ) (Lemma 1);
- `one_sub_le_one_sub_sq`: 1 − c ≤ 1 − c² for c ∈ [0, 1] (Corollary 4);
- `log_ratio_le` and `coin_divergence_le`: 4ε ln((1 + 4ε)/(1 − 4ε)) ≤ 64ε² for 0 ≤ ε ≤ 1/8 (Proposition 3);
- `reduction`: (1/2 + 2ε)a + (1/2 − 2ε)b ≥ 1/2 + ε with a + b ≤ 1 and ε > 0 gives a − b ≥ 1/2 (Proposition 3).

`lean/axioms.txt` lists the axioms of every named theorem: only standard axioms. Not formalized: the shadow variance bounds of [3] and [2], the net and selection arguments, the free-fermion overlap formula and the information bounds of Proposition 5.

## Scope

- Theorems 1 and 2 bound copies. Their running time is exponential in mk, the running time of Corollary 4 is exponential in m², and [1] gives an algorithm with running time m^{poly(n,1/ε)}. The remark keeps that running time and improves only the selection step.
- The variance bounds are taken from [3] and [2]. The bound b(m) of [2] is checked exactly here for m = 3.
- For adaptive single-copy algorithms and for joint measurements, the gap between Proposition 5 and Theorem 1 in m and n remains open. Among non-adaptive single-copy algorithms, a factor k log(k/ε) remains.
- The statements are Claims with the listed checks.

## References

1. N. Paul, H. Zhao, D. D. Dai. Learning the closest Slater determinant. arXiv:2607.20623 (2026).
2. K. Wan, W. J. Huggins, J. Lee, R. Babbush. Matchgate shadows for fermionic quantum simulation. Communications in Mathematical Physics 404, 629 (2023). arXiv:2207.13723.
3. H.-Y. Huang, R. Kueng, J. Preskill. Predicting many properties of a quantum system from very few measurements. Nature Physics 16, 1050-1057 (2020).

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
