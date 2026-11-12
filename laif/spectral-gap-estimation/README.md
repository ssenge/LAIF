# Spectral gap estimation of random walks for every relative error

2026-11-12

## Problem

Let A be an N × N matrix with largest singular value σ_1 = 1, given by a unitary block-encoding U_A: either the symmetrized discriminant Π^{1/2}PΠ^{−1/2} of a reversible random walk P with stationary distribution π, or the transition matrix of a doubly stochastic walk [1]. The singular gap is γ = 1 − σ_2. Two tasks are considered:

- *Thresholding*: for 0 < L < 1 and ε ∈ (0, 1], output 1 if σ_2 ≥ 1 − L(1 − ε) and 0 if σ_2 ≤ 1 − L(1 + ε), with failure probability at most p_f.
- *Estimation*: output γ̂ with (1 − ε)γ̂ ≤ γ ≤ (1 + ε)γ̂, with failure probability at most p_f.

Cost is the number of uses of U_A, U_A† and their controlled versions.

Previous best bound [1, Theorems 43 and 47]: thresholding with O(√N log N log(1/p_f)/(εL)) uses for every ε, and with O(√(N/L) log N log(1/p_f)) uses only for ε above a critical value that depends on N and tends to 1 as N grows; estimation with Õ(√N/(εγ)) and Õ(√N/√γ) under the same restriction. Lower bounds Ω(√N) and Ω(1/√(Lε)) [1, Propositions 48 and 49]. A filter with the 1/√L scaling for every ε is stated as open problem 2 of [1].

## Results

**Lemma 1 (filter).** For 0 < Δ < 1, t ∈ (0, 1] with Δ(1 + t) ≤ 1 and α ∈ (0, 1/4], there is a real even polynomial f of degree at most 2⌈2 ln(4/α)/w⌉ with w ≥ t√(2Δ), so of degree at most 2√2 ln(4/α)/(t√Δ) + 2, such that |f(x)| ≤ 1 on [−1, 1], |f(x)| ≤ α for |x| ≤ 1 − Δ(1 + t), and f(x) ≥ 1 − α for |x| ≥ 1 − Δ(1 − t). Its coefficients are explicit.

**Theorem 2 (thresholding).** For every 0 < L < 1 and ε ∈ (0, 1] with L(1 + ε) ≤ 1, thresholding uses

O( √N log N log(1/p_f) / (ε√L) )

applications of U_A and U_A†, with no condition on N and no random input states.

**Theorem 3 (estimation).** The singular gap can be estimated to relative error ε ∈ (0, 1/2] with

O( √N log N log(log(2/(εγ))/p_f) / (ε√γ) )

uses.

**Theorem 4 (lower bound).** For every N ≥ 4 even, L(1 + ε) ≤ 1/2 and ε ∈ (0, 1], every algorithm for thresholding with failure probability at most 1/3 uses at least

√N / (12√2 ε√L)

queries, already for symmetric doubly stochastic walks (for which the transition matrix equals the symmetrized discriminant) with a fixed block-encoding. In particular, estimation to relative error ε/3 needs Ω(√N/(ε√γ)) queries.

So both tasks cost Θ(√N/(ε√γ)) up to the factors log N and log(1/p_f), for every relative error. Against the previous bounds, the upper bound gains a factor 1/√L for every ε, and the lower bound combines the factors √N, 1/ε and 1/√L.

**Remark (random input states).** The thresholding test of [1] applies the filter to a random state ψ from a unitary 2-design and compares the weight Σ_i f(σ_i)²|⟨u_i|ψ⟩|² with a fixed threshold. For a uniformly random ψ, N|⟨u|ψ⟩|² converges in law to an exponential variable with mean 1, so Pr(N|⟨u|ψ⟩|² ≥ 1 − k) tends to e^{−(1−k)} < 1. This hints at a possible gap in Remark 34 of [1], which states that this probability exceeds any p < 1 for large N, and in the step of Theorem 43 that relies on it: a "no" instance, whose weight is f(1)²|⟨u_1|ψ⟩|² + O(α²), exceeds a threshold that half of the "yes" runs exceed with probability about 0.47 per trial. Theorem 2 uses the purified maximally mixed input instead, for which the weight is the deterministic value Σ_i f(σ_i)²/N.

## Proofs

*Lemma 1.* Write x = cos θ with θ ∈ [0, π]. Let θ_p = arccos(1 − Δ(1 − t)), θ_b = arccos(1 − Δ(1 + t)) ≤ π/2, w = θ_b − θ_p and θ_c = (θ_p + θ_b)/2. Since d/dy arccos(1 − y) = (2y − y²)^{−1/2} ≥ (2y)^{−1/2},

w ≥ √2 (√(Δ(1 + t)) − √(Δ(1 − t))) = √(2Δ) · 2t/(√(1 + t) + √(1 − t)) ≥ t√(2Δ).

Let Z be normal with mean 0 and variance σ² = w²/(8 ln(2/α)), and h(θ) = Pr(θ + Z ∈ ∪_{m∈ℤ} [mπ − θ_c, mπ + θ_c]). Then 0 ≤ h ≤ 1, h has period π and h(−θ) = h(θ), so h(θ) = a_0 + Σ_{k≥1} a_k cos(2kθ) with

a_0 = 2θ_c/π, a_k = (2 sin(2kθ_c)/(πk)) e^{−2k²σ²},

since the indicator of [−θ_c, θ_c] has cosine coefficients 2 sin(2kθ_c)/(πk) for period π and E cos(2kZ) = e^{−2k²σ²}. For θ ≤ θ_p the event contains |Z| ≤ w/2, and for θ_b ≤ θ ≤ π/2 it is contained in |Z| ≥ w/2, because θ_c + w/2 = θ_b ≤ π/2. With Pr(|Z| ≥ w/2) ≤ e^{−w²/(8σ²)} = α/2, h ≥ 1 − α/2 on [0, θ_p] and h ≤ α/2 on [θ_b, π/2], and by h(π − θ) = h(θ) the same holds on the mirrored intervals. Truncate at D = ⌈2√(ln(4/α) ln(2/α))/w⌉ ≤ ⌈2 ln(4/α)/w⌉. With s = 2D²σ² ≥ ln(4/α) ≥ 1/π,

Σ_{k>D} |a_k| ≤ (2/π) ∫_D^∞ e^{−2u²σ²} du/u = (1/π) E_1(s) ≤ e^{−s}/(πs) ≤ α/4.

Since cos(2kθ) = T_{2k}(cos θ) for the polynomials T_n defined by T_n(cos θ) = cos(nθ), f(x) = (a_0 + Σ_{k=1}^{D} a_k T_{2k}(x))/(1 + α/4) is a real even polynomial of degree 2D with |f| ≤ 1, |f| ≤ (3α/4)/(1 + α/4) ≤ α on the blocked set and f ≥ (1 − 3α/4)/(1 + α/4) ≥ 1 − α on the passed set. ∎

*Theorem 2.* Take f from Lemma 1 with Δ = L, t = ε and α = 1/(8√N). Since f is real, even and bounded by 1, singular value transformation [2, Corollary 10] gives a block-encoding of f(√(A†A)) with 2D uses of U_A and U_A† and one extra qubit. Apply it to the first half of |Φ⟩ = N^{−1/2} Σ_i |i⟩|i⟩. The probability of the flag outcome is

W = ‖(f(√(A†A)) ⊗ 1)|Φ⟩‖² = Σ_i f(σ_i)²/N.

The value f_1 = f(1) ∈ [3/4, 1] is computable from the coefficients. If σ_2 ≤ 1 − L(1 + ε), then W ≤ (f_1² + (N − 1)α²)/N ≤ (f_1² + 1/64)/N =: W_0. If σ_2 ≥ 1 − L(1 − ε), then W ≥ (f_1² + (1 − α)²)/N ≥ (f_1² + 9/16)/N =: W_1. Amplitude estimation with M uses of the flag circuit returns W̃ with |W̃ − W| ≤ 2π√(W(1 − W))/M + π²/M² with probability at least 8/π² [3, Theorem 12]. For M = ⌈34√N⌉ and W ≤ 2/N this error is at most (2π√2/34 + π²/34²)/N < (W_1 − W_0)/2 = 35/(128N); for W ≥ W_1 the lower deviation W − 2π√W/M − π²/M² is increasing in W, so W̃ > (W_0 + W_1)/2 still holds. Output 1 if W̃ > (W_0 + W_1)/2. The median of O(log(1/p_f)) runs fails with probability at most p_f. Total uses: O(D√N log(1/p_f)) = O(√N log N log(1/p_f)/(ε√L)). ∎

*Theorem 3.* Write Test(L, ε) for Theorem 2: output 1 implies γ ≤ L(1 + ε), output 0 implies γ ≥ L(1 − ε). Phase 1: for k = 1, 2, … run Test(2^{−k}, 1/2) until the first output 0. Then γ ≥ 2^{−k−1}, and γ ≤ min{1, 3 · 2^{−k}} from the output at k − 1 (or from γ ≤ 1 for k = 1). This ends after k ≤ log_2(2/γ) + 1 rounds and costs O(√N log N/√γ) in total, since the costs grow geometrically. Phase 2: keep an interval [a, b] ∋ γ with b ≤ 1, set h = (b − a)/2, L = a + h, ε′ = h/(2L), and run Test(L, ε′). Output 1 gives γ ≤ L + h/2 and output 0 gives γ ≥ L − h/2, so the interval shrinks to length 3h/2 = 3(b − a)/4. Stop when b − a ≤ 2εa and output γ̂ = (a + b)/2, for which |γ̂ − γ| ≤ εa ≤ εγ̂. Each test costs O(√N log N √L/h · log(1/p′)), and h shrinks geometrically to Θ(εa) with a ≥ γ/6, so phase 2 costs O(√N log N/(ε√γ) · log(1/p′)) over O(log(1/ε)) tests. With p′ = p_f/(log_2(2/γ) + 1 + O(log(1/ε))) and a union bound, the total failure probability is at most p_f. All tests satisfy L(1 + ε′) ≤ b ≤ 1 and ε′ ≤ 1. ∎

*Theorem 4.* Pair the states as {2i, 2i + 1}, let S swap the two states of each pair and J be the all-ones matrix. For c = 1 − 2L(1 + ε) ≥ 0 let

P_0 = c·1 + (1 − c)(S/2 + J/(2N)).

It is symmetric, nonnegative and doubly stochastic, with eigenvalues 1 (on the constant vector), λ_s = c + (1 − c)/2 = 1 − L(1 + ε) on the vectors that are constant on pairs and orthogonal to the constant vector (dimension N/2 − 1), and c − (1 − c)/2 on the vectors antisymmetric on pairs, of modulus at most λ_s. So σ_2(P_0) = 1 − L(1 + ε). For a pair j let w_j be its indicator vector, Π = 1 − J/N and u_j = Πw_j/‖Πw_j‖, a unit eigenvector of P_0 for λ_s. Let

P_j = P_0 + 2Lε u_j u_jᵀ.

Then P_j is symmetric with unchanged row and column sums (u_j ⊥ 1), and its only changed eigenvalue is λ_s + 2Lε = 1 − L(1 − ε) on u_j, so σ_2(P_j) = 1 − L(1 − ε). Its entries stay nonnegative: the only decreasing entries are those between pair j and the other states, by 2Lε/N, while P_0 has L(1 + ε)/N there. Use the block-encoding U(P) = [[P, √(1 − P²)], [√(1 − P²), −P]], which is unitary and self-inverse. Since P_j and P_0 commute and differ only on u_j,

U(P_j) − U(P_0) = (R(θ′) − R(θ)) ⊗ u_ju_jᵀ, R(θ) = [[cos θ, sin θ], [sin θ, −cos θ]],

with cos θ = 1 − L(1 + ε), cos θ′ = 1 − L(1 − ε), so ‖U(P_j) − U(P_0)‖ = 2 sin(|θ − θ′|/2) ≤ |θ − θ′| ≤ ∫_{L(1−ε)}^{L(1+ε)} y^{−1/2} dy ≤ 2√2 ε√L =: δ. The same bound holds for the controlled versions. Further Σ_j u_ju_jᵀ = (N/(N − 2)) Π_sym, with Π_sym the projector onto the vectors constant on pairs and orthogonal to 1, so for every state φ of the algorithm Σ_j ‖((U(P_j) − U(P_0)) ⊗ 1)φ‖² ≤ δ² N/(N − 2) ≤ 2δ². By the hybrid argument [4], if ψ_T^j and ψ_T^0 are the final states after T queries,

Σ_j ‖ψ_T^j − ψ_T^0‖ ≤ Σ_{s<T} Σ_j ‖((U(P_j) − U(P_0)) ⊗ 1)ψ_s^0‖ ≤ T √(N/2) √(2δ²) = Tδ√N.

An algorithm with failure probability at most 1/3 needs ‖ψ_T^j − ψ_T^0‖ ≥ 1/3 for each of the N/2 pairs, so T ≥ √N/(6δ) = √N/(12√2 ε√L). For estimation, the instances have γ = L(1 ± ε), and an estimate with relative error ε/3 separates them. ∎

## Check

- `sim/filter.py` builds the polynomial of Lemma 1 from its coefficients for Δ from 10⁻¹ to 10⁻⁴, t from 0.9 to 0.03 and α ∈ {10⁻², 10⁻⁴}, evaluates it on a grid of at least 16 points per degree in θ and at the band edges, and asserts the three conditions and the degree bound. The degree times t√Δ/ln(4/α) lies between 2.25 and 2.74, against the proven 2√2 ≈ 2.83.
- `sim/lower.py` builds the instances of Theorem 4 for N up to 64 and asserts symmetry, nonnegativity, double stochasticity, the second singular values, the frame identity, unitarity of the block-encoding and ‖U(P_j) − U(P_0)‖ ≤ 2√2 ε√L. It also evaluates the weights W of Theorem 2 on these instances: "no" below W_0 and "yes" above W_1.
- `sim/overlap.py` samples random states for N = 2⁶, 2¹⁰, 2¹⁴ and asserts that Pr(N|⟨u|ψ⟩|² ≥ 1 − k) is close to e^{−(1−k)}, not close to 1, and that a threshold accepting half of the "yes" runs accepts about 0.47 of the "no" runs.

Output in `sim/out.txt`.

## Scope

- Written proofs with numerical checks. Singular value transformation [2] and amplitude estimation [3] are used as stated there. Constructing the block-encoding U_A is not covered.
- The upper bounds carry the factors log N (from α = 1/(8√N)) and log(1/p_f), which the lower bound does not have.
- The lower bound counts queries to one fixed block-encoding of each instance; it holds for every algorithm that uses U_A, U_A† and their controlled versions with fixed gates in between.

## References

[1] A. Connolly, S. Herbert, J. Sorci. Quasi-optimal quantum Markov chain spectral gap estimation. arXiv:2601.07601.

[2] A. Gilyén, Y. Su, G. H. Low, N. Wiebe. Quantum singular value transformation and beyond: exponential improvements for quantum matrix arithmetics. STOC 2019. arXiv:1806.01838.

[3] G. Brassard, P. Høyer, M. Mosca, A. Tapp. Quantum amplitude amplification and estimation. Contemporary Mathematics 305 (2002). arXiv:quant-ph/0005055.

[4] C. H. Bennett, E. Bernstein, G. Brassard, U. Vazirani. Strengths and weaknesses of quantum computing. SIAM Journal on Computing 26, 1510-1523 (1997). arXiv:quant-ph/9701001.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
