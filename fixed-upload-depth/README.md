# Depth of fixed upload circuits

Written 5 Nov 2026.

## Setting

A single-qubit data re-uploading circuit on x ∈ [0, 1] with *tunable* upload gates uses e^{iwxσ_z} with a trainable frequency w. A *fixed upload* circuit allows only the gate e^{i(π/2)xσ_z}, interleaved with x-independent trainable SU(2) gates; its depth D is the number of fixed upload gates (Definition 3 of [1]). Write w = Kπ/2 + η with K ∈ Z and |η| ≤ π/4. To approximate e^{iwxσ_z} on [0, 1] within ε in Frobenius norm, [1] gives D = O_σ(|K| + (log(C_σ/ε))^σ) for every σ > 1 (Theorem 11 of [1]), and a lower bound Ω(log(1/ε)) for w ∉ (π/2)Z (Theorem 15 of [1]). Closing this gap is the main open question of [1].

## Results

**Theorem 1 (upper bound).** For every real w and ε ∈ (0, 1) there is a fixed upload circuit U(x) of depth

D ≤ (2/π)|w| + (32/π) ln(1/ε) + 17

with sup_{x∈[0,1]} ‖U(x) − e^{iwxσ_z}‖_F ≤ ε.

**Theorem 2 (lower bound on the frequency term).** Every fixed upload circuit of depth D with sup_{x∈[0,1]} ‖U(x) − e^{iwxσ_z}‖_F ≤ ε < √2 satisfies

D ≥ (2/π)(1 − ε')(|w| − 2 arcsin ε'),  ε' = ε/√2.

So the coefficient 2/π of |w| is optimal as ε → 0. Theorem 15 of [1] applies to every frequency w ∉ (π/2)Z, so with it, for fixed such w and ε small enough,

D = Θ(log(1/ε)).

That is σ = 1 in Theorem 11 of [1], with explicit constants. For w ∈ (π/2)Z the gate is a power of the fixed gate, and D = |K| is exact with error 0.

**Corollary 3 (whole circuits).** Let U_L^w be an m-variable tunable upload circuit with L layers and frequencies w_jk, so with Lm tunable upload gates (Definition 2 of [1]). Replacing each tunable gate by the circuit of Theorem 1 at error ε/(Lm) gives a fixed upload circuit with sup_x ‖U_L^w(x) − U(x)‖_op ≤ ε and

D ≤ Σ_{j,k} (2/π)|w_jk| + Lm((32/π) ln(Lm/ε) + 17).

The operator norm is at most the Frobenius norm, and the errors add up by the telescoping identity for products of unitaries, as in the proof of Theorem 12 of [1]. Definition 3 of [1] gives every block the same number of fixed gates; shorter blocks can be padded with the identity X e^{i(π/2)xσ_z} X e^{i(π/2)xσ_z} = I, which replaces the sum over k by m times the maximum over k for m ≥ 2. For m = 1 nothing changes. Corollaries 13 and 14 of [1], for dense fixed upload circuits and for continuous targets, are derived from Theorem 12 of [1] through its error bound and gate count, so they hold with the count O(Σ_{j,k}|K_jk| + Lm log(2Lm/ε)), that is with σ = 1.

## Proof of Theorem 1

**Realization.** By Theorem 5 of [1] and the gate count stated after it, every Laurent polynomial P(z) = Σ_{n=−N}^{N} p_n z^n with |P| ≤ 1 on the unit circle is the upper left entry of a circuit of the form [[P, −Q*], [Q, P*]] at z = e^{iπx}, with |P|² + |Q|² = 1, using 2N fixed upload gates. For g(x) = e^{iwx},

‖R(x) − e^{iwxσ_z}‖_F² = 2|P − g|² + 2(1 − |P|²).

So it suffices to find P with |P| ≤ 1 everywhere and |P − g| ≤ a on [0, 1], since then 1 − |P|² ≤ 2a and the error is at most (2a² + 4a)^{1/2}.

**Window.** The construction follows the smoothed-window idea of [2]. Let δ = ε²/2, Λ = ln(1/δ) + 2, s = 1/(4√Λ), I = [−1/4, 5/4] and

W(x) = ½[erf((x + 1/4)/s) − erf((x − 5/4)/s)],

the indicator of I smoothed by a Gaussian of variance s²/2. Its Fourier transform is Ŵ(ξ) = 1̂_I(ξ) e^{−ξ²s²/4}, with |1̂_I(ξ)| = |2 sin(3ξ/4)/ξ| ≤ 2/|ξ|. Let

P̃(x) = Σ_{j∈Z} e^{iw(x+2j)} W(x + 2j),

a 2-periodic function with Fourier coefficients c_k = ½ Ŵ(πk − w) at e^{iπkx}.

- *Bounded.* |P̃(x)| ≤ Σ_j W(x + 2j) ≤ 1, since W(y) is the probability that y minus a Gaussian lies in I, and the translates I + 2j are disjoint.
- *Close on [0, 1].* For x ∈ [0, 1], x is at distance at least 1/4 = s√Λ from the ends of I, and x + 2j for j ≠ 0 is at distance at least 3/4 from I. So |P̃ − g| ≤ (1 − W(x)) + Σ_{j≠0} W(x + 2j) ≤ erfc(√Λ) + erfc(3√Λ) ≤ 2e^{−Λ} = 2e^{−2}δ ≤ 0.271δ.

**Truncation.** Let k₀ be the integer nearest to w/π and N′ = ⌈8Λ/π⌉, and let P₀ keep the coefficients with |k − k₀| ≤ N′. For n = |k − k₀|, |πk − w| ≥ π(n − ½), and s²/4 = 1/(64Λ), so |c_k| ≤ e^{−a_n²/(64Λ)}/a_n with a_n = π(n − ½). For n ≥ N′ + 1, a_n ≥ 8Λ + π/2, so the first omitted term is at most e^{−Λ−π/8}/(8Λ), and consecutive terms shrink by at least e^{−π(2a_n+π)/(64Λ)} ≤ e^{−π/4}. Both sides together give

|P̃ − P₀| ≤ 2e^{−Λ−π/8}/(8Λ(1 − e^{−π/4})) ≤ 0.311 e^{−Λ}/Λ ≤ 0.016δ,

using Λ ≥ 2 + ln 2. Put P = P₀/(1 + 0.022δ). Then |P| ≤ 1 everywhere, and on [0, 1], |P − g| ≤ (0.271 + 0.016 + 0.022)δ = a with a ≤ 0.309δ. The error is at most (2a² + 4a)^{1/2} ≤ (1.34δ)^{1/2} ≤ ε, since δ = ε²/2 ≤ 1/2.

**Count.** P has powers e^{iπkx} with |k| ≤ |k₀| + N′ = N, and |k₀| ≤ |w|/π + ½, N′ ≤ 8Λ/π + 1. So D = 2N ≤ (2/π)|w| + 3 + (16/π)(2 ln(1/ε) + ln 2 + 2) ≤ (2/π)|w| + (32/π) ln(1/ε) + 17. ∎

## Proof of Theorem 2

All gates of the circuit lie in SU(2), so U(x) = [[P, −Q*], [Q, P*]] with P(x) = Σ_{|n|≤D} p_n e^{iπnx/2}, a trigonometric polynomial of degree D in πx/2. As U(x) is unitary for all real x, |P| ≤ 1 on R, and the derivative inequality for trigonometric polynomials [3] gives |P′(x)| ≤ (π/2)D on R.

The error bound gives 2|P − g|² ≤ ε², so |P − g| ≤ ε′ < 1 on [0, 1], with g = e^{iwx}. Then |P| ≥ 1 − ε′ > 0 there, and P has a continuous argument ψ with |ψ(x) − wx| ≤ arcsin ε′. Hence |ψ(1) − ψ(0)| ≥ |w| − 2 arcsin ε′, while |ψ′| ≤ |P′|/|P| ≤ (π/2)D/(1 − ε′). Integrating over [0, 1] gives the claim. ∎

## Simulation

`sim/window_check.py` needs Python 3 with NumPy and SciPy. For w in {0, 0.5, 1, π/2, 3.3, 40.7, 400.1} and ε from 0.3 to 10⁻⁵, where the bounds stay above double-precision rounding, it builds P on a grid of 20,001 points of [−1, 1] and checks each bound of the proof of Theorem 1: |P̃| ≤ 1, the window error, the truncation error, |P| ≤ 1, the final Frobenius error and the count. At w = 0.5 it prints D = 38, 62, 86, 108, 132, 156 for ε = 10⁻¹, …, 10⁻⁶, with errors close to a quarter of ε.

## References

1. A. Y. Liu, L. Pira. The Cost of Removing Tunability in Quantum Data Re-Uploading. arXiv:2606.25598.
2. T. L. Silva, L. Borges, L. Aolita. Fourier-based quantum signal processing. arXiv:2206.02826.
3. P. Borwein, T. Erdélyi. Polynomials and Polynomial Inequalities. Springer, 1995.
