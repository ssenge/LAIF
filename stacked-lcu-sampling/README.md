# Sampling the loss of stacked linear combinations of unitaries

Written 5 Nov 2026.

## Setting

A stacked linear combination of unitaries [1] on n qubits is

A = L_l ⋯ L_1, with L_j = Σ_{i=1}^k a^j_i U_{ji}, a^j_i ≥ 0 and Σ_i a^j_i = 1 for every layer j.

The quantity studied in [1] is the unnormalized loss

m = tr(A ρ₀ A† O), with ρ₀ = |0⟩⟨0|.

Its normalization is p_s = tr(A ρ₀ A†), the probability of postselection.

In the free fermion case, each U_{ji} is a fermionic Gaussian unitary. We take it as given, like a circuit, by a phase e^{iα_{ji}} and a product of g generators exp(ϑ c_p c_q/2), where c_1, …, c_{2n} are the Majorana operators. A general Gaussian unitary needs g = O(n²).

The observable is O = Σ_t h_t Q_t. Each Q_t is a product of at most r Majorana operators, with r even, and we write ‖h‖₁ = Σ_t |h_t|. For example, Z₁ = −i c₁c₂ has r = 2 and ‖h‖₁ = 1. A traceless quadratic O with tr(O²) = 2^n has r = 2 and ‖h‖₁² ≤ n(2n − 1), since its at most n(2n − 1) coefficients have squares that sum to 1.

[1] proves Var[m] = Ω(1/(n k^{3l})) at random initialization. It states two costs:

- O(k^{2l} n³) for the best classical method known to its authors. This method expands A into k^l Gaussian terms and evaluates all pairs.
- O(lkn²) quantum gates.

For one layer, [2] gives the analogous cost O(k² n³).

## Results

**Theorem 1 (sampling the loss).** Let ε, δ ∈ (0, 1) and N = ⌈2‖h‖₁² ln(2/δ)/ε²⌉. A classical randomized algorithm outputs m̂ with |m̂ − m| ≤ ε with probability at least 1 − δ. It runs in time

O(N (lg + r) n³) = O((lg + r) n³ ‖h‖₁² log(1/δ)/ε²),

after O(kl) time to read the input. The time does not depend on k. For O = Z₁ and general Gaussian unitaries, it is O(l n⁵ log(1/δ)/ε²).

**Theorem 2 (sampling the gradient).** The same algorithm, with N multiplied by 4, estimates each of the following partial derivatives to within ε with probability at least 1 − δ:

- ∂m/∂a^j_i, with the coefficients taken as free variables, so that any parametrization follows by the chain rule;
- ∂m/∂ϑ, for the angle ϑ of any generator of any U_{ji}.

**Corollary 3 (comparison).** Estimating m to within ε on a quantum computer takes the following numbers of runs of a circuit with O(lkn²) gates:

- Θ(1/ε²) runs from shots of the circuit;
- O(1/ε) runs with amplitude estimation [5]. For black-box estimation this is optimal [6].

Write C_cl for the classical time of Theorem 1 and C_sh for the quantum gate count with shots. For every l,

C_cl / C_sh = O(g n ‖h‖₁² / k),

which for O = Z₁ and g = O(n²) is O(n³/k). Against amplitude estimation, the classical time is at most quadratic in the quantum gate count, up to a factor polynomial in n. To resolve m at the scale σ = √Var[m] of [1], both sides need precision about σ, so these ratios hold there as well.

**Proposition 4 (postselection).** Suppose the U_{ji} carry independent uniform phases, as in the ensemble U(1) × Spin(2n) of [1], and the a^j are uniform Dirichlet. Then

E[p_s] = (2/(k + 1))^l.

## Proof of Theorem 1

For a path a = (a_1, …, a_l) ∈ [k]^l, let U_a = U_{l,a_l} ⋯ U_{1,a_1} and c_a = ∏_j a^j_{a_j}. Then A = Σ_a c_a U_a. The weights c_a are nonnegative and sum to ∏_j Σ_i a^j_i = 1, so c is the product distribution that draws each a_j from a^j independently. Hence

m = Σ_{a,b} c_a c_b ⟨0|U_b† O U_a|0⟩ = E_{a,b ∼ c} ⟨0|U_b† O U_a|0⟩.

The estimator does the following, N times:

1. It draws two independent paths a and b. Each takes l draws from distributions on [k], in time O(l log k) after O(kl) preprocessing.
2. It draws t with probability |h_t|/‖h‖₁.
3. It sets Y = ‖h‖₁ Re((h_t/|h_t|) ⟨0|U_b† Q_t U_a|0⟩).

Then E[Y] = Re m = m, since O is Hermitian. Each Q_t is unitary and the states are normalized, so |Y| ≤ ‖h‖₁. By Hoeffding's inequality, the mean of N independent copies is within ε of m with probability at least 1 − 2e^{−Nε²/(2‖h‖₁²)} ≥ 1 − δ.

For one sample, the description of a Gaussian state tracks its global phase [3]:

- Starting from |0⟩, the algorithm applies the lg generators of U_a, each by the routine evolve of Theorem 3.2 of [3] in time O(n³), and multiplies the phases e^{iα}.
- Since (c_p c_q)² = −1, c_p c_q = exp(π c_p c_q/2) is itself a generator. So Q_t is a product of r/2 generators, applied in time O(r n³).
- It does the same for U_b.
- It computes the overlap ⟨U_b 0, Q_t U_a 0⟩ by the routine overlap of the same theorem, in time O(n³).

This gives O((lg + r) n³) per sample. ∎

The method is the standard sampling estimator for linear combinations with an ℓ₁ bound on the weights [4, 7]. The point here is that the weights of the stacked construction sum to exactly 1 for every k and l, so the term count k^l does not enter.

## Proof of Theorem 2

**Coefficients.** As m = ⟨0|A† O A|0⟩ with A linear in each a^j_i, we have ∂m/∂a^j_i = 2 Re ⟨0|A† O (∂A/∂a^j_i)|0⟩. Here

∂A/∂a^j_i = Σ_{a: a_j = i} (c_a / a^j_i) U_a.

So ∂m/∂a^j_i = 2 E[Re ⟨0|U_b† O U_{a′}|0⟩], where b ∼ c and a′ ∼ c is conditioned on a′_j = i. The sampled values are bounded by 2‖h‖₁.

**Angles.** Write U_{ji} = e^{iα} G_g ⋯ G_1. If ϑ is the angle of G_s, then ∂U_{ji}/∂ϑ = e^{iα} G_g ⋯ G_{s+1} (c_p c_q/2) G_s ⋯ G_1. The inserted factor c_p c_q/2 is half a generator. The same computation gives

∂m/∂ϑ = 2 a^j_i E[Re ⟨0|U_b† O U′_{a′}|0⟩],

where U′_{a′} has U_{ji} replaced by its derivative. The sampled values are bounded by a^j_i ‖h‖₁ ≤ ‖h‖₁.

In both cases the bound on the sampled values is at most 2‖h‖₁, so Hoeffding's inequality with 4N samples gives precision ε. Each sample costs at most one more generator than in Theorem 1. ∎

## Proof of Corollary 3

**Quantum side.** A shot of a circuit for m (postselection, or a Hadamard test on a block encoding of A) gives a random variable with mean m, bounded by ‖O‖. Its standard deviation is of order ‖O‖ for generic instances, so Θ(1/ε²) shots are needed and suffice. Amplitude estimation needs O(1/ε) uses [5], which is optimal for black-box estimation of a mean [6].

**Classical side.** Theorem 1 takes O(l g n³ ‖h‖₁²/ε²) time, against Θ(lkn²/ε²) gates with shots. The ratio is O(g n ‖h‖₁²/k). ∎

## Proof of Proposition 4

We have p_s = Σ_{a,b} c_a c_b ⟨0|U_b† U_a|0⟩. If a ≠ b, some layer has a_j ≠ b_j. There, the independent uniform phases of U_{j,a_j} and U_{j,b_j} enter as e^{i(α − α′)}, whose mean is 0. Conditioning on everything else, these terms have mean zero. So

E[p_s] = E Σ_a c_a² = ∏_j E Σ_i (a^j_i)² = (k · 2/(k(k + 1)))^l = (2/(k + 1))^l,

using E[(a^j_i)²] = 2/(k(k + 1)) for the uniform Dirichlet distribution [1]. ∎

## Remarks

- **Normalized loss.** The normalized loss m/p_s needs m and p_s to relative precision. The two methods then scale as follows:
  - Theorem 1 then costs O(‖h‖₁²/(ε² p_s²)) samples.
  - Postselected shots need about 1/(ε² p_s).
  - Amplitude amplification and estimation need about 1/(ε √p_s).

  By Proposition 4, the typical scale is 1/p_s ≈ ((k + 1)/2)^l. So for the normalized loss, the separation is polynomial in 1/p_s, and the postselection probability, not the term count k^{2l}, sets its size.
- **Other unitaries.** Theorems 1 and 2 hold for any stacked construction whose unitaries allow the amplitudes ⟨0|U_b† Q U_a|0⟩, with their phases, to be computed classically. Examples are Clifford unitaries with Pauli observables, and matchgate circuits.
- **Scope.**
  - The results give additive precision and do not change the exact cost O(k^{2l} n³).
  - The variance bound of [1] is not affected. Theorem 1 concerns the cost of evaluating the loss, not the flatness of the landscape.
  - [1] lists classical algorithms that exploit the stacked structure as an open point. For the unnormalized loss of its Theorem 1, sampling removes the dependence on k.

## Simulation

[sim/sampling_check.py](sim/sampling_check.py) builds instances with n = 4, k = 3, l = 3 and dense matrices in place of the phased Gaussian routines. It checks four things:

- the estimator of Theorem 1 is unbiased, using 2·10⁵ samples;
- the Hoeffding sample size gives precision 0.05 in 200 of 200 runs;
- the gradient estimators of Theorem 2 agree with finite differences;
- E[p_s] = (2/(k + 1))^l holds for k = 3, l = 2.

## References

1. N. Khatri, S. Zohren, G. Matos. Stacking the Deck: Tunable Trainability in Stacked LCUs. arXiv:2607.24686, Theorem 1, Eq. (56) and Sec. V.
2. N. Khatri, S. Zohren, G. Matos. Trainability of Parametrised Linear Combinations of Unitaries. arXiv:2506.22310.
3. B. Dias, R. König. Classical simulation of non-Gaussian fermionic circuits. Quantum 8, 1350 (2024), arXiv:2307.12912, Theorem 3.2.
4. H. Pashayan, J. J. Wallman, S. D. Bartlett. Estimating outcome probabilities of quantum circuits using quasiprobabilities. Physical Review Letters 115, 070501 (2015), arXiv:1503.07525.
5. G. Brassard, P. Høyer, M. Mosca, A. Tapp. Quantum amplitude amplification and estimation. Contemporary Mathematics 305 (2002), arXiv:quant-ph/0005055.
6. A. Nayak, F. Wu. The quantum query complexity of approximating the median and related statistics. STOC 1999, arXiv:quant-ph/9804066.
7. S. Bravyi, D. Browne, P. Calpin, E. Campbell, D. Gosset, M. Howard. Simulation of quantum circuits by low-rank stabilizer decompositions. Quantum 3, 181 (2019), arXiv:1808.00128.
