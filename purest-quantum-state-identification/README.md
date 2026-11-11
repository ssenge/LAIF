# Purest quantum state identification with fixed confidence and single-copy measurements

2026-11-12

## Problem

K unknown quantum states ρ_1, …, ρ_K of dimension d ≥ 2 can be copied, and the task is to find the state of largest purity P = tr ρ² [1]. The purest state is unique. Its gap to state i is Δ_i = P_max − P_i, and for the purest state itself Δ is the smallest of the other gaps. Each copy is measured on its own, with a measurement that may depend on all earlier outcomes (incoherent or single-copy measurements, no quantum memory). In the fixed-confidence version the learner decides when to stop. It must output the purest state with probability at least 1 − δ, using as few copies as possible.

For the fixed-budget version, [1] gives an algorithm that measures copies in random bases and counts identical outcomes. With N copies its error probability is exp(−Ω(√c N H₁/(d log K))) when all gaps are at least a known c > 1/d² [1, Theorem 4.1], and exp(−Ω(min{N H₂, N H₁/d²}/log K)) in general [1, Lemma 4.2], where H₁ = min_i Δ_(i)/i and H₂ = min_i Δ_(i)²/i over the sorted gaps. The fixed-confidence version is left open in [1, Section 7].

## Results

Write h(Δ) = √d/Δ + 1/Δ².

**Theorem 1.** The elimination algorithm below needs no knowledge of the gaps. With probability at least 1 − δ it outputs the purest state, and it then uses at most

N ≤ Σ_i (4616 √d/Δ_i + 73734/Δ_i²) · ⌈8 ln(4K log₂²(2/Δ_i)/δ)⌉ = O( Σ_i h(Δ_i) · log(K log(2/Δ_i)/δ) )

copies. Inside each epoch the measurements are nonadaptive, and the random bases may come from any unitary 4-design.

The cost √d/Δ + 1/Δ² per state is the copy count of the additive purity estimator of [3], which uses the same statistic; its variance appears in [3, Lemma 16] and [1, Lemma B.2]. Theorem 1 runs this estimator inside an elimination over accuracy levels, so that no gap needs to be known, and gives explicit constants. Lemmas 1 and 2 below give a short proof of the variance bound for every state.

**Comparison.** Since Σ_i h(Δ_i) ≤ (1 + ln K) max_i i·h(Δ_(i)), Theorem 1 reaches error δ with O(log K · max_i i·h(Δ_(i)) · log(K log(2/Δ_(2))/δ)) copies. To reach error δ, the bounds of [1] need N of order log K · log(K/δ) times max_i i·d/(√c Δ_(i)) [1, Theorem 4.1] or max_i i·(d²/Δ_(i) + 1/Δ_(i)²) [1, Lemma 4.2], with N fixed in advance. Per state this replaces d/(√c Δ) and d²/Δ + 1/Δ² by √d/Δ + 1/Δ². For gaps of constant size the cost per state drops from order d to order √d.

**Proposition 2 (lower bounds).**

- (a) Let K = 2, let d = 2ⁿ be large enough, and let 0 < Δ ≤ 1/4 with 1/(2Δ) a power of 2. Every single-copy algorithm, adaptive or not, that errs with probability at most 1/12 and stops within T copies with probability at least 11/12, on every instance with gap at least Δ/3, has T = Ω(√(d/Δ)). This is implied by [4, Theorem 6].
- (b) Let d ≥ 2, K = 2, Δ ≤ 3/32 and δ < 1/8. Every single-copy algorithm that errs with probability at most δ and stops within T copies with probability at least 1 − δ, on the instances below with gap Δ, has T ≥ ln(1/(8δ))/(12 Δ²).

For K = 2 the upper bound of Theorem 1 and the lower bounds agree up to constants and logarithmic factors at constant gap and for Δ ≤ 1/√d. In between they differ by at most a factor d^{1/6}, attained near Δ = d^{−1/3}. For constant gaps the Ω(√d) of part (a) goes back to [2, Theorem 5.11].

## Algorithm

**Block.** Draw a random unitary U and measure m ≥ 2 copies of a state ρ in the basis U†|x⟩. With c_x the number of outcomes x, the block statistic is

g = Σ_x c_x(c_x − 1) / (m(m − 1)),

the fraction of pairs of copies with the same outcome. Its mean is μ = (1 + P)/(d + 1).

**Group.** For an accuracy ε ∈ (0, 1], set m(ε) = min(d, max(2, ⌈√d/ε⌉)) and B(ε) = ⌈64 (d + 1)² V_m/ε²⌉ with V_m = 64/d³ + 24/(m d²) + 8/(m² d). A group is the mean of B(ε) blocks with m(ε) copies each.

**Elimination.** In epoch ℓ = 1, 2, …, set ε_ℓ = 2^{−ℓ} and G_ℓ = ⌈8 ln(4Kℓ²/δ)⌉. For every active state, take G_ℓ fresh groups at accuracy ε_ℓ and let w_i be their median. Keep state i if w_i ≥ max_j w_j − ε_ℓ/(2(d + 1)). Stop when one state is left and output it.

Large gaps let the algorithm put up to √d/ε copies into a single basis. Small gaps need many bases with d copies each, since the outcome distribution depends on the basis.

## Proof

**Moments.** For a uniformly random unit vector ψ, E[⟨ψ|A|ψ⟩⟨ψ|B|ψ⟩⟨ψ|C|ψ⟩] is the sum over the six permutations of the products of traces, divided by d(d + 1)(d + 2), and similarly for two factors. Let p_x = ⟨x|UρU†|x⟩ and S(U) = Σ_x p_x². Then E[g | U] = S, E S = (1 + P)/(d + 1) and E Σ_x p_x³ = (1 + 3P + 2 tr ρ³)/((d + 1)(d + 2)) ≤ 6/((d + 1)(d + 2)).

**Lemma 1 (basis variance).** Var_U S ≤ 48d/((d² − 1)(d + 1)(d + 2)) ≤ 64/d³.

*Proof.* S does not change under U ↦ e^{iθ}U, so its variance is the same under the uniform measure on SU(d). With the metric ⟨X, Y⟩ = tr(X†Y), the uniform measure on SU(d) has spectral gap d − 1/d: the smallest nonzero eigenvalue of the invariant second-order differential operator is its value on the matrix entries of the defining representation. So Var f ≤ E|∇f|²/(d − 1/d) for every smooth f. Moving U to e^{itH}U changes S at the rate tr(HG), with G = 2i[σ, D], σ = UρU† and D = diag(p). G is traceless and self-adjoint, so |∇S|² = ‖G‖²₂ = 8 tr(σ²D²) − 8 tr(σDσD) ≤ 8 tr(σ²D²), since tr(σDσD) = tr((σ^{1/2}Dσ^{1/2})²) ≥ 0. By the moment formula, E tr(σ²D²) = Σ_x E[⟨ψ_x|ρ|ψ_x⟩²⟨ψ_x|ρ²|ψ_x⟩] = (P + P² + 2 tr ρ³ + 2 tr ρ⁴)/((d + 1)(d + 2)) ≤ 6/((d + 1)(d + 2)), with ψ_x = U†|x⟩. ∎

E S² is a polynomial of degree 4 in the entries of U and of degree 4 in those of U†, so Var S, and with it the bound, is the same for every unitary 4-design.

**Lemma 2 (block variance).** Var g ≤ V_m.

*Proof.* Given U, g is a U-statistic of order 2 with kernel 1{x = y}, so Var(g | U) = 2(2(m − 2)ζ₁ + ζ₂)/(m(m − 1)) with ζ₁ = Σp³ − S² ≤ Σp³ and ζ₂ = S − S² ≤ S. Hence Var(g | U) ≤ (4/m)Σp³ + 2S/(m(m − 1)). Its mean is at most 24/(m d²) + 8/(m² d). Adding Var_U S from Lemma 1 gives V_m. ∎

**Groups.** By Lemma 2 and the inequality for the second moment, a group misses μ by at least ε/(4(d + 1)) with probability at most 16(d + 1)²V_m/(Bε²) ≤ 1/4. The median of G independent groups misses by that much only if at least half of them do, which has probability at most exp(−G/8). A group uses B·m copies. If m = ⌈√d/ε⌉ ≤ d, then m/d ≤ 1 and d/m ≤ √d ε, so B·m ≤ m + 144(64m/d + 24 + 8d/m)/ε² ≤ 1154 √d/ε + 12673/ε². If m = d, then ε < 1/√d and B·m ≤ d + 13824/ε² ≤ 13825/ε².

**Elimination.** Let E be the event that every median is within ε_ℓ/(4(d + 1)) of its mean in every epoch. Then P(E fails) ≤ Σ_ℓ K · δ/(4Kℓ²) < δ. On E the purest state is never dropped, since its median exceeds every other median minus ε_ℓ/(2(d + 1)). A state with Δ_i > ε_ℓ is dropped in epoch ℓ: its median is below μ_max − (Δ_i − ε_ℓ/4)/(d + 1), and the largest median is above μ_max − ε_ℓ/(4(d + 1)). So state i leaves by the epoch ℓ_i = ⌊log₂(1/Δ_i)⌋ + 1, where 2^{ℓ_i} ≤ 2/Δ_i, and the purest state by the epoch of the smallest gap. Summing the group cost over the epochs up to ℓ_i, a geometric sum, gives the bound of Theorem 1.

**Proposition 2 (a).** Let ε = 2Δ. Let arm 1 be an unknown state ρ, and let arm 2 be a fixed state σ of purity 1/d + Δ, such as a mixture of |0⟩⟨0| and I/d, which the learner prepares itself. If ρ = I/d, arm 2 is purest with gap Δ. If ρ is drawn from the random induced states of [4, Definition 6] with parameter ε, its purity is at least 1/d + 2ε/3 = 1/d + 4Δ/3 except with probability O(d^{−2}) [4, proof of Lemma 4], and then arm 1 is purest with gap at least Δ/3. Cut the algorithm off after T copies. It then errs with probability at most 1/6 on each instance, so it tells I/d from a random induced state with probability at least 7/12 from T single-copy measurements of ρ. By [4, Theorem 6] with no quantum memory, this needs T = Ω(min{√(d/ε), d/ε²}) = Ω(√(d/Δ)).

**Proposition 2 (b).** Let ρ_a = diag(1 − a, a, 0, …, 0) with a = 1/4 and b = 1/4 + η, η ≤ 1/8, so that the purity gap is Δ = 2η(1/2 − η) ∈ [3η/4, η]. A measurement of a diagonal state is a random function of one sample of the coin with bias a. Compare the instances (ρ_a, ρ_b) and (ρ_b, ρ_a). Cut the algorithm off after T copies; it then errs with probability at most 2δ on both instances and uses at most T copies. The relative entropy between the two laws of all outcomes is at most T · max(KL(a‖b), KL(b‖a)) ≤ T · η²/(a(1 − a)) ≤ 11.4 T Δ². The two errors sum to at most 4δ, and their sum is at least exp(−KL)/2, which gives the bound.

## Check

`sim/purest.py` samples random bases and outcomes and checks with asserts:

- the moment formulas for E S and E Σp³;
- Lemma 1 for d from 2 to 32 and Lemma 2 for d up to 64, on pure, rank-two, rank-four, random and maximally mixed states;
- the elimination algorithm with the number of blocks per group reduced by a factor 16 and the number of groups by a factor 4, on one pure state against three states of purity 1/2, for d = 16, 64, 256 and 1024: it returns the pure state in every run, and the copies grow by a factor of about 2 from d = 16 to d = 1024, against 64 for a cost proportional to d (at these sizes the term 1/Δ² dominates);
- the term √d/Δ: the number of copies in a single random basis that ranks a pure state above a state of purity 1/2 with probability 0.9 grows like √d, with m/√d = 9.06, 8.88 and 8.67 for d = 1024, 4096 and 16384 (m = 290, 568 and 1110). For smaller d the copies saturate the basis (m = 148 > d at d = 64).

Output in `sim/purest_out.txt`.

## Scope

- **Assuming:** the spectral gap d − 1/d of the uniform measure on SU(d) (a classical fact of harmonic analysis on compact groups), and [4, Theorem 6] with the properties of random induced states from [4, Lemma 4] for Proposition 2 (a).
- **Not formalized:** the results have no Lean proof.
- The constants are not optimized. The purest state is assumed unique, as in [1]. The lower bounds are for K = 2.
- Theorem 1 is a fixed-confidence result. The bounds of [1] are for a fixed budget, so the comparison counts the copies each needs to reach error δ.

## References

[1] Y. Yu, H. Chen, J. Wu, W. Xie, X. Li. Purest quantum state identification. arXiv:2502.14334.
[2] S. Chen, J. Cotler, H.-Y. Huang, J. Li. Exponential separations between learning with and without quantum memory. FOCS 2021, arXiv:2111.05881.
[3] A. Anshu, Z. Landau, Y. Liu. Distributed quantum inner product estimation. arXiv:2111.03273.
[4] W. Gong, J. Haferkamp, Q. Ye, Z. Zhang. On the sample complexity of purity and inner product estimation. arXiv:2410.12712.

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
