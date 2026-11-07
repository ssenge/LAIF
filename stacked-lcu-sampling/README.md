# Sampling the loss of stacked linear combinations of unitaries

Written 5 Nov 2026.

## Setting

A stacked linear combination of unitaries [1] on n qubits is

A = L_l ⋯ L_1, with L_j = Σ_{i=1}^k a^j_i U_{ji}, a^j_i ≥ 0 and Σ_i a^j_i = 1 for every layer j.

The quantity studied in [1] is the unnormalized loss

m = tr(A ρ₀ A† O), with ρ₀ = |0⟩⟨0|.

Its normalization is p_s = tr(A ρ₀ A†), the probability of postselection.

**free-fermion unitaries.** In the free fermion case, each U_{ji} is a free-fermion unitary. It is given, like a circuit, by a phase e^{iα_{ji}} and a product of g generators exp(ϑ c_p c_q/2), where c_1, …, c_{2n} are the mode operators, self-adjoint with c_p c_q = −c_q c_p for p ≠ q and c_p² = I. A general free-fermion unitary needs g = O(n²). This covers the ensemble U(1) × Spin(2n) of [1]: a rotation R ∈ SO(2n) decomposes into at most n(2n − 1) generators in time O(n³) [3, Sec. 2.2], and the sign of the lift to Spin(2n) is absorbed into α.

**Observables.** The observable is O = Σ_t h_t Q_t with h_t ∈ ℂ, where each Q_t is a product of at most r distinct mode operators. We write ‖h‖₁ = Σ_t |h_t|. For example:

- In the convention of [1], Z₁ = −i c₁c₂, with r = 2 and ‖h‖₁ = 1.
- A traceless quadratic O with tr(O²) = 2^n has r = 2 and ‖h‖₁² ≤ n(2n − 1), since its at most n(2n − 1) coefficients have squares that sum to 1.

**What [1] proves.** For a traceless quadratic O with tr(O²) = 2^n, ρ₀ = |0⟩⟨0| and n ≥ 3, [1] proves Var[m] = Ω(1/(n k^{3l})) at random initialization. It states two costs:

- O(k^{2l} n³) for the best classical method known to its authors. This method expands A into k^l free-fermion terms and evaluates all pairs.
- O(lkn²) quantum gates, before postselection or amplitude amplification.

For one layer, [2] gives the analogous cost O(k² n³).

## Results

**Theorem 1 (sampling the loss).** Let ε, δ ∈ (0, 1) and N = ⌈2‖h‖₁² ln(2/δ)/ε²⌉. A classical randomized algorithm outputs m̂ with |m̂ − m| ≤ ε with probability at least 1 − δ. It runs in time

O(N (lg + r) n³) = O((lg + r) n³ ‖h‖₁² log(1/δ)/ε²),

after O(kl) preprocessing of the coefficients, given random access to the descriptions of the U_{ji}. For fixed ε the time does not depend on k. For O = Z₁ and general free-fermion unitaries it is O(l n⁵ log(1/δ)/ε²).

**Theorem 2 (sampling the gradient).** For any one of the following partial derivatives, the same algorithm with N multiplied by 4 estimates it to within ε with probability at least 1 − δ. The full gradient over P parameters takes P such runs, with δ replaced by δ/P.

- ∂m/∂a^j_i, with the coefficients taken as free variables. For a parameter θ of the coefficients of layer j, drawing i with probability proportional to |∂a^j_i/∂θ| gives an estimator of ∂m/∂θ with values bounded by 2‖h‖₁ Σ_i |∂a^j_i/∂θ|. For a softmax this sum is at most 1/2.
- ∂m/∂ϑ, for the angle ϑ of any generator of any U_{ji}.

**Proposition 4 (postselection).** If the unitaries of each layer are independent with E[U] = 0, and the a^j are uniform on the simplex, then

E[p_s] = (2/(k + 1))^l.

This is the case O = I of Result 1 of [1]. We include a direct proof.

**Proposition 5 (variance of the estimator).** Let φ_u = U_u|0⟩ and σ = Σ_u c_u |φ_u⟩⟨φ_u|, with paths u and weights c_u as in the proof of Theorem 1. The value Y of one sample of Theorem 1 satisfies

E[Y²] ≤ ‖h‖₁² tr(σ²), with tr(σ²) = Σ_{u,v} c_u c_v |⟨φ_u|φ_v⟩|².

On the uniform ensemble on U(1) × Spin(2n) with coefficients uniform on the simplex, as in [1], with ρ₀ = |0⟩⟨0|,

E[tr(σ²)] = E[p_s] + (1 − E[p_s]) 2^{1−n}.

**Corollary 3 (comparison).** Estimating m to within ε on a quantum computer takes the following numbers of runs of a circuit with O(lkn²) gates:

- **Shots:** O(‖O‖²/ε²) runs from shots. With postselection the variance of a shot is at most p_s‖O‖², so O(p_s‖O‖²/ε² + ‖O‖/ε) runs suffice.
- **Amplitude estimation:** O(1/ε) runs with amplitude estimation [5], and O(√p_s/ε + 1/√ε) for O with eigenvalues ±1. Both are optimal for black-box estimation [6].

On the classical side, compare the time of Theorem 1, C_cl, with the quantum gate count C_sh for O(‖O‖²/ε²) shots:

- **Worst case.** For every l, C_cl/C_sh = O((g + r/l) n ‖h‖₁²/(k‖O‖²)), which for O = Z₁ and g = O(n²) is O(n³/k).
- **Variance-adaptive.** With variance bounds in place of the worst-case ones (the tail bound that uses the variance), the two sides need O(V/ε² + B/ε) samples. Empirical variance bounds give the same order up to logarithmic factors, with V estimated from the samples [10]:
  - shots: V = p_s‖O‖² and B = ‖O‖;
  - sampling: V = ‖h‖₁² tr(σ²) and B = ‖h‖₁.

  On the ensemble of [1], Proposition 5 gives E[tr(σ²)] ≤ E[p_s] + 2^{1−n}. So, on average, the classical sample count matches the shot count up to the floor 2^{1−n} and the factor ‖h‖₁²/‖O‖².
- **At the scale of the variance.** At precision ε = σ_m = √Var[m], with the bound of [1], the counts are at most:
  - Bounded range: (2n − 1)((k + 1)(k + 2)(k + 3)/24)^l samples;
  - variance-adaptive: about (2n − 1)((k + 2)(k + 3)/12)^l samples or shots, while E[p_s] ≫ 2^{−n}.

  So neither side is then independent of k. For k ≥ 18 the bounded-range count grows faster in l than the exact cost O(k^{2l} n³).

## Proof of Theorem 1

**The expansion.** For a path u = (u_1, …, u_l) ∈ [k]^l, let U_u = U_{l,u_l} ⋯ U_{1,u_1} and c_u = ∏_j a^j_{u_j}. Then A = Σ_u c_u U_u. The weights c_u are nonnegative and sum to ∏_j Σ_i a^j_i = 1, so c is the product distribution that draws each u_j from a^j independently. Hence

m = Σ_{u,v} c_u c_v ⟨0|U_v† O U_u|0⟩ = E_{u,v ∼ c} ⟨0|U_v† O U_u|0⟩.

**The estimator.** It repeats the following N times:

1. It draws two independent paths u and v, each by l draws from distributions on [k].
2. It draws t with probability |h_t|/‖h‖₁.
3. It sets Y = ‖h‖₁ Re((h_t/|h_t|) ⟨0|U_v† Q_t U_u|0⟩).

Then E[Y] = Re m = m, since O is self-adjoint. Each Q_t is unitary and the states are normalized, so |Y| ≤ ‖h‖₁. By the tail bound for bounded independent variables, the mean of N independent copies is within ε of m with probability at least 1 − 2e^{−Nε²/(2‖h‖₁²)} ≥ 1 − δ.

**Cost per sample.** The description of a free-fermion state tracks its global phase [3]. For one sample:

- Starting from |0⟩, the algorithm applies the lg generators of U_u, each by the routine evolve of Theorem 3.2 of [3] in time O(n³), and multiplies the phases e^{iα}.
- It applies Q_t. Since (c_p c_q)² = −1, exp(ϑ c_p c_q/2) = cos(ϑ/2) + sin(ϑ/2) c_p c_q. So for p < q, c_p c_q is the generator with ϑ = π in the parameterization of [3], and c_q c_p = −c_p c_q. The single mode operators c_j are generators of [3] as well. Up to a sign, Q_t is therefore a product of at most r generators, applied in time O(r n³).
- It does the same for U_v.
- It computes the overlap ⟨U_v 0, Q_t U_u 0⟩ by the routine overlap of the same theorem, in time O(n³).

This gives O((lg + r) n³) per sample. ∎

**Credit.** The method is the standard sampling estimator for linear combinations with an ℓ₁ bound on the weights [4, 7]. The same pair estimator, with an interference test on one ancilla in place of a classical overlap, is the single-ancilla LCU method [8]. [3, Sec. 4.2] notes that the squared ℓ₁ norm of a free-fermion decomposition controls the cost of simulation for any dictionary. The point here is that the weights of the stacked construction sum to exactly 1 for every k and l, so at fixed ε the term count k^l does not enter.

## Proof of Theorem 2

**Coefficients.** As m = ⟨0|A† O A|0⟩ with A linear in each a^j_i, we have ∂m/∂a^j_i = 2 Re ⟨0|A† O (∂A/∂a^j_i)|0⟩. Here

∂A/∂a^j_i = Σ_{u: u_j = i} (c_u / a^j_i) U_u,

and the weights c_u/a^j_i sum to 1 over that set. So ∂m/∂a^j_i = 2 E[Re ⟨0|U_v† O U_{u′}|0⟩], where v ∼ c and u′ ∼ c is conditioned on u′_j = i. The sampled values are bounded by 2‖h‖₁.

For a parameter θ, ∂m/∂θ = Σ_i (∂a^j_i/∂θ) ∂m/∂a^j_i. Drawing i with probability proportional to |∂a^j_i/∂θ|, and then one sample of ∂m/∂a^j_i, gives values bounded by 2‖h‖₁ Σ_i |∂a^j_i/∂θ|. For a softmax a_i = e^{θ_i}/Σ_s e^{θ_s} and θ = θ_s, the sum is 2a_s(1 − a_s) ≤ 1/2.

**Angles.** Write U_{ji} = e^{iα} G_g ⋯ G_1. If ϑ is the angle of G_s, then ∂U_{ji}/∂ϑ = e^{iα} G_g ⋯ G_{s+1} (c_p c_q/2) G_s ⋯ G_1. The same computation gives

∂m/∂ϑ = 2 a^j_i E[Re ⟨0|U_v† O U′_{u′}|0⟩],

where U′_{u′} has U_{ji} replaced by its derivative. The sampled values are bounded by a^j_i ‖h‖₁ ≤ ‖h‖₁.

**Sample count.** The bound on the sampled values is at most 2‖h‖₁ in all cases, so the tail bound for bounded independent variables with 4N samples gives precision ε. Each sample costs at most one more generator than in Theorem 1. The conditioned path differs between derivatives, so each derivative needs its own run. ∎

## Proof of Proposition 4

We have p_s = Σ_{u,v} c_u c_v ⟨0|U_v† U_u|0⟩. If u ≠ v, some layer j has u_j ≠ v_j, and the term contains U_{j,u_j} and U_{j,v_j}† once each. These two unitaries are independent of each other and of the rest, with mean 0, so the term has mean zero. Hence

E[p_s] = E Σ_u c_u² = ∏_j E Σ_i (a^j_i)² = (k · 2/(k(k + 1)))^l = (2/(k + 1))^l,

using E[(a^j_i)²] = 2/(k(k + 1)) for the uniform distribution on the simplex [1]. ∎

## Proof of Proposition 5

**The bound.** For one sample with given t, |Y| ≤ ‖h‖₁ |⟨φ_v|Q_t|φ_u⟩|. Then

E_{u,v} |⟨φ_v|Q_t|φ_u⟩|² = Σ_{u,v} c_u c_v ⟨φ_u|Q_t†|φ_v⟩⟨φ_v|Q_t|φ_u⟩ = tr(Q_t σ Q_t† σ) ≤ tr(σ²),

by the inequality |tr(A†B)|² ≤ tr(A†A) tr(B†B), as Q_t σ Q_t† and σ have the same norm. Averaging over t, with weights |h_t|/‖h‖₁, gives E[Y²] ≤ ‖h‖₁² tr(σ²).

**The mean.** Take two different paths u ≠ v, and let j be the highest layer with u_j ≠ v_j. The layers above j are the same unitary W on both sides, so ⟨φ_u|φ_v⟩ = ⟨χ|U† V|χ′⟩. Here:

- U = U_{j,u_j} and V = U_{j,v_j} are independent uniformly random elements;
- χ and χ′ are the states from the lower layers, independent of U and V.

The first-order commutant of the free-fermion unitaries is spanned by I and the parity P [1]. So E_U[U|χ⟩⟨χ|U†] = (I + ⟨χ|P|χ⟩ P)/2^n. Since V commutes with P and all states are even,

E|⟨χ|U† V|χ′⟩|² = (1 + ⟨χ|P|χ⟩⟨χ′|P|χ′⟩)/2^n = 2^{1−n}.

The coefficients are independent of the unitaries, and E Σ_{u≠v} c_u c_v = 1 − E Σ_u c_u² = 1 − E[p_s]. The diagonal terms give E Σ_u c_u² = E[p_s]. ∎

## Proof of Corollary 3

**Quantum side.** A shot gives o·1[success], where o is the measured eigenvalue of O, with mean m. Its variance is p_s⟨O²⟩_post − m² ≤ p_s‖O‖². So O(p_s‖O‖²/ε² + ‖O‖/ε) shots suffice by the tail bound that uses the variance, and O(‖O‖²/ε²) always suffice. For O with eigenvalues ±1, m = p₊ − p₋ with p_± ≤ p_s. The error of amplitude estimation after M uses is O(√(p(1 − p))/M + 1/M²) [5, Theorem 12], which gives O(√p_s/ε + 1/√ε) uses. The lower bound for counting in [6] has the same form, so both bounds are optimal for black-box access.

**Classical side.** Theorem 1 takes O(N(lg + r)n³) time, against Θ(lkn²‖O‖²/ε²) gates with shots, which gives the worst-case ratio. With the tail bound that uses the variance and the variance bound of Proposition 5, the classical count is O(‖h‖₁² tr(σ²)/ε² + ‖h‖₁/ε), and the mean of tr(σ²) is given there.

**At the scale of the variance.** At ε = σ_m, the bound Var[m] ≥ (24/((k + 1)(k + 2)(k + 3)))^l/(2n − 1) of [1] turns 1/ε² into at most (2n − 1)((k + 1)(k + 2)(k + 3)/24)^l. Multiplying by E[p_s] = (2/(k + 1))^l gives (2n − 1)((k + 2)(k + 3)/12)^l for the variance-adaptive counts.

Divided by the exact k^{2l}, the bounded-range count grows like b(k)^l, up to factors polynomial in n and l, with b(k) = (k + 1)(k + 2)(k + 3)/(24k²). Here b(k) < 1 exactly for k ≤ 17. ∎

## Remarks

- **Normalized loss.** The normalized loss m/p_s needs m and p_s to relative precision. The worst-case counts are:
  - O(‖h‖₁²/(ε² p_s²)) samples for Theorem 1;
  - about 1/(ε² p_s) postselected shots;
  - about 1/(ε √p_s) uses with amplitude amplification and estimation.

  By Proposition 4, E[p_s] = (2/(k + 1))^l. So for the normalized loss, these worst-case bounds differ by factors polynomial in 1/p_s, and the postselection probability, not the term count k^{2l}, sets the size of the gap between them. With variance-adaptive counts, the classical cost for p_s is of order tr(σ²)/(ε² p_s²), so by Proposition 5 it is close to the shot count on average when p_s ≫ 2^{−n}.
- **Other unitaries.** Theorems 1 and 2 hold for any stacked construction whose unitaries allow the amplitudes ⟨0|U_v† Q U_u|0⟩, with their phases, to be computed classically. Examples are stabilizer circuits, which map tensor products of I, X, Y, Z to such products under conjugation, with such products as observables, and matchgate circuits.
- **Per-sample cost.**
  - The cost per sample can be lowered. A general free-fermion unitary given by R ∈ SO(2n) can be applied in time O(n⁴) [9, as noted in 3], which gives O(l n⁴) per sample.
  - Rotating a quadratic O to normal form reduces ‖h‖₁² to at most n.
- **Scope.**
  - The results give additive precision and do not change the exact cost O(k^{2l} n³).
  - The variance bound of [1] is not affected. Theorem 1 concerns the cost of evaluating the loss, not the flatness of the landscape.
  - [1] lists classical algorithms that exploit the stacked structure as an open point. For the unnormalized loss of its Theorem 1, sampling removes the dependence on k at fixed additive precision ε. At the precision σ_m of its variance bound, the sample count grows like k^{3l} with the bounded-range bound, and like k^{2l} with variance-adaptive counts.

## Simulation

[sim/sampling_check.py](sim/sampling_check.py) uses dense matrices in place of the phased free-fermion routines. It checks:

- on instances with n = 4, k = 3, l = 3 and products of random generators: that the estimator of Theorem 1 is unbiased (2·10⁵ samples), that the bounded-range sample size gives precision 0.05 in 200 of 200 runs, and that the gradient estimators of Theorem 2 agree with finite differences;
- E[p_s] = (2/(k + 1))^l for k = 3, l = 2;
- on 400 instances with exactly uniform random elements of U(1) × Spin(2n), n = 4, k = 4, l = 2: the bound E[Y²] ≤ tr(σ²) on every instance, and the mean of tr(σ²) given by Proposition 5.

## References

1. N. Khatri, S. Zohren, G. Matos. Stacking the Deck: Tunable Trainability in Stacked LCUs. arXiv:2607.24686, Theorem 1, Result 1, Eq. (56) and Sec. V.
2. N. Khatri, S. Zohren, G. Matos. Trainability of Parametrised Linear Combinations of Unitaries. arXiv:2506.22310.
3. B. Dias, R. König. Classical simulation of non-Gaussian fermionic circuits. Quantum 8, 1350 (2024), arXiv:2307.12912, Theorem 3.2 and Sec. 4.2.
4. H. Pashayan, J. J. Wallman, S. D. Bartlett. Estimating outcome probabilities of quantum circuits using quasiprobabilities. Physical Review Letters 115, 070501 (2015), arXiv:1503.07525.
5. G. Brassard, P. Høyer, M. Mosca, A. Tapp. Quantum amplitude amplification and estimation. Contemporary Mathematics 305 (2002), arXiv:quant-ph/0005055.
6. A. Nayak, F. Wu. The quantum query complexity of approximating the median and related statistics. STOC 1999, arXiv:quant-ph/9804066.
7. S. Bravyi, D. Browne, P. Calpin, E. Campbell, D. Gosset, M. Howard. Simulation of quantum circuits by low-rank stabilizer decompositions. Quantum 3, 181 (2019), arXiv:1808.00128.
8. S. Chakraborty. Implementing any linear combination of unitaries on intermediate-term quantum computers. Quantum 8, 1496 (2024), arXiv:2302.13555.
9. O. Reardon-Smith, M. Oszmaniec, K. Korzekwa. Improved simulation of quantum circuits dominated by free fermionic operations. arXiv:2307.12702.
10. A. Maurer, M. Pontil. Empirical Bernstein bounds and sample variance penalization. COLT 2009, arXiv:0907.3740.
