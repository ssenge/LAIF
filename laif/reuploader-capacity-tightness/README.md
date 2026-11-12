# The spectral capacity bound is tight for single-qubit reuploaders

Written 6 Nov 2026.

## Problem

A single-qubit data reuploader with R uploads is

U(x) = W_R e^{−ixZ} W_{R−1} ⋯ e^{−ixZ} W_0,  f(x) = ⟨0|U(x)† M U(x)|0⟩,

with trainable blocks W_l ∈ SU(2) and an observable M with ‖M‖ ≤ B. Its frequency set is K_R = {−2R, −2R + 2, …, 2R}, so |K_R| = 2R + 1 [1, Example 1], [2]. Let F_R be the class of all such f. For points x_1, …, x_n and independent uniform signs σ_i ∈ {−1, 1}, the empirical random-sign complexity is

R̂_n(F_R) = E_σ sup_{f ∈ F_R} (1/n) Σ_i σ_i f(x_i).

**The known bound.** For any points x_1, …, x_n [1, Proposition 1],

R̂_n(F_R) ≤ B √(|K_R|/n).

The bound holds for all multivariate encodings with commensurate spectra. It is stated as an upper bound only, and [1] does not claim that it is tight.

## Result

**Theorem 1.** Let n be a multiple of R + 1. Take the R + 1 points x_a = πa/(R + 1), a = 0, …, R, each repeated n/(R + 1) times. Then

R̂_n(F_R) ≥ B √((R + 1)/(2n)) ≥ (1/2) B √(|K_R|/n).

So for single-qubit reuploaders, as a bound over all point sets, the bound of [1] is tight up to a factor of 2, for every R and every such n. The point set here has repeated points. As n grows, the exact value at these points tends to √(2/π)·√((R + 1)/(2R + 1)) ≥ 0.56 times the upper bound. For n ≤ R + 1 points chosen among the x_a without repetition, the complexity is B, the largest possible. The lower bound is the standard kernel interpolation argument for trigonometric polynomials. What makes it apply here is that single-qubit reuploaders realize that whole class.

**Lemma 1 (realizability).** Every real trigonometric polynomial F(x) = Σ_{|j|≤R} c_j e^{2ijx} with |F| ≤ 1 is f/B for the model with M = BZ and suitable blocks W_0, …, W_R.

Conversely, every model is a real trigonometric polynomial in 2x of degree at most R [1, Lemma 1], [2], with |f| ≤ ‖M‖ ≤ B. So F_R is exactly the set of real trigonometric polynomials in 2x of degree at most R with sup norm at most B. The inclusion of the model class in such a set is used in [7]; Lemma 1 makes it an equality for one qubit. So for one qubit, the reachable coefficients discussed in [1, Section 2.3] carry no constraint beyond |f| ≤ ‖M‖. Lemma 1 is known from quantum signal processing [4, 5, Lemma 3]. It is included here because the lower bound uses it.

## Proof

*Proof of Lemma 1.* Write y = 2x and w = e^{iy}. It suffices to treat |F| < 1. The realized functions are the image of the compact set SU(2)^{R+1} under a continuous map, so they form a closed set, and the case |F| ≤ 1 follows by taking limits of (1 − 1/k)F.

- **Factorization.** The trigonometric polynomials (1 + F)/2 and (1 − F)/2 are positive and have degree at most R. By the factorization theorem for nonnegative trigonometric polynomials [3], there are polynomials p and q of degree at most R with |p(w)|² = (1 + F)/2 and |q(w)|² = (1 − F)/2 on |w| = 1.
- **A unitary.** Put z = e^{ix}. Let U(z) be the matrix with columns (z^{−R}p(z²), z^{−R}q(z²)) and (−z^{R}q̄(z^{−2}), z^{R}p̄(z^{−2})), where p̄ has the conjugated coefficients. On |z| = 1 it has the form [[a, −b̄], [b, ā]] with |a|² + |b|² = |p|² + |q|² = 1, so it lies in SU(2). Its entries are polynomials in z and z^{−1} with powers from −R to R, all of the parity of R.
- **Layer stripping.** Write U(z) = Σ_{k=−R}^{R} C_k z^k with R ≥ 1.
  - Since det U = 1 has no z^{±2R} terms, det C_R = det C_{−R} = 0. Since U†U = I has no z^{2R} term on the circle, C_{−R}†C_R = 0.
  - Choose W ∈ SU(2) whose first column is orthogonal to the range of C_R and whose second column is orthogonal to the range of C_{−R}. This is possible because the two ranges are orthogonal and each has dimension at most one.
  - Then the first row of W†U has no z^R term and the second row has no z^{−R} term. So W†U = D(z)U′ with D(z) = diag(z^{−1}, z) = e^{−ixZ} and U′ of the same form with R − 1 in place of R.
  - Repeating R times gives U = W_R D(z) W_{R−1} ⋯ D(z) W_0 with W_l ∈ SU(2) [4], [5, Lemma 3].
- **The output.** The first column of U(x) is z^{−R}(p(z²), q(z²)), so f/B = |p|² − |q|² = F. □

*Proof of Theorem 1.*

- **The kernel.** Let φ(y) = (1/(R + 1)) Σ_{|k|≤R} (1 − |k|/(R + 1)) e^{iky} = (sin((R + 1)y/2)/((R + 1) sin(y/2)))². It satisfies φ ≥ 0 and φ(0) = 1, and it vanishes at 2πj/(R + 1) for j ≢ 0 mod R + 1.
- **A partition of unity.** Put y_a = 2x_a = 2πa/(R + 1). Summing over the nodes keeps only the frequencies k divisible by R + 1, and the only such k with |k| ≤ R is k = 0. So Σ_a φ(y − y_a) = 1 for every y.
- **Every sign pattern.** For signs s ∈ {−1, 1}^{R+1} let F_s(x) = Σ_a s_a φ(2x − y_a). This is a real trigonometric polynomial in 2x of degree R. It satisfies |F_s| ≤ Σ_a φ(2x − y_a) = 1 and F_s(x_a) = s_a. By Lemma 1, B·F_s lies in F_R.
- **The complexity.** Let S_a be the sum of the n/(R + 1) signs at the copies of x_a. Every f ∈ F_R has |f| ≤ B, so (1/n) Σ_i σ_i f(x_i) ≤ (B/n) Σ_a |S_a|. The function B·F_s with s_a = sign(S_a) attains this. Therefore R̂_n(F_R) = (B/n) Σ_a E|S_a| exactly.
- **The first absolute moment.** A sum of m independent uniform signs has E|S| ≥ √(m/2) [6]. With m = n/(R + 1) this gives R̂_n(F_R) ≥ B √((R + 1)/(2n)). Finally R + 1 = (|K_R| + 1)/2 ≥ |K_R|/2. The limit statement follows from E|S| ~ √(2m/π). □

## Remarks

1. **Other single-qubit encodings.** Take an encoding e^{−ixH} on one qubit, where H has eigenvalues λ₁ > λ₂ and gap ω = λ₁ − λ₂. Up to a global phase and a change of basis absorbed in the blocks, it equals e^{−i(ωx/2)Z}. So Theorem 1 holds for it with the nodes x_a = 2πa/(ω(R + 1)).
2. **Scope.**
   - The tightness is for one input variable on one qubit, where |K_R| = 2R + 1.
   - For d variables and several qubits, the frequency count of [1] grows like R^m. Whether bounded models of that size reach every sign pattern on a grid of that size is not treated here. In that setting the factorization theorem of [3] has no direct multivariate analogue.
3. **Parameters.** Here P = 3(R + 1) parameters exceed |K_R| = 2R + 1, as noted in [1]. So the spectral count, not the parameter count, sets the capacity in this setting.

## Check

`sim/capacity_check.py` checks Lemma 1 and Theorem 1.

- **Lemma 1.** It factors random F with |F| < 1 and strips the layers, for R ∈ {1, 2, 3, 5, 8}. It then evaluates the circuit and compares it with F at random points.
- **Theorem 1, the interpolants.** For R ∈ {1, 2, 3, 5, 8, 20, 50} it checks that the kernel interpolates exactly on the R + 1 nodes and sums to one.
- **Theorem 1, the circuits.** For R ≤ 8 it builds circuits for 0.99 times the interpolant of random sign patterns and evaluates them at the nodes; amplitude 1 follows from Lemma 1 by the limit argument. With 4 copies per node it estimates the complexity by random sampling over these circuits and compares it with 0.99 times the exact value.
- **Theorem 1, the bound.** From the exact formula of the proof, at 1, 4 and 25 copies per node, it asserts the bound of Theorem 1 and the factor of 2. This value depends only on the number of copies per node, so it is the same for every R.

```
realizability: random |F| < 1 of degree R = 1..8 reproduced by R uploads, error < 1e-6
R = 1: kernel interpolation exact on 2 nodes; circuits at 4 copies per node: 0.3583 vs 0.99 x exact 0.3712; at n = 50: complexity = 0.1612, lower bound sqrt((R+1)/2n) = 0.1414, spectral upper bound sqrt(|K_R|/n) = 0.2449
R = 2: kernel interpolation exact on 3 nodes; circuits at 4 copies per node: 0.3580 vs 0.99 x exact 0.3712; at n = 75: complexity = 0.1612, lower bound sqrt((R+1)/2n) = 0.1414, spectral upper bound sqrt(|K_R|/n) = 0.2582
R = 3: kernel interpolation exact on 4 nodes; circuits at 4 copies per node: 0.3672 vs 0.99 x exact 0.3712; at n = 100: complexity = 0.1612, lower bound sqrt((R+1)/2n) = 0.1414, spectral upper bound sqrt(|K_R|/n) = 0.2646
R = 5: kernel interpolation exact on 6 nodes; circuits at 4 copies per node: 0.3715 vs 0.99 x exact 0.3712; at n = 150: complexity = 0.1612, lower bound sqrt((R+1)/2n) = 0.1414, spectral upper bound sqrt(|K_R|/n) = 0.2708
R = 8: kernel interpolation exact on 9 nodes; circuits at 4 copies per node: 0.3675 vs 0.99 x exact 0.3712; at n = 225: complexity = 0.1612, lower bound sqrt((R+1)/2n) = 0.1414, spectral upper bound sqrt(|K_R|/n) = 0.2749
R = 20: kernel interpolation exact on 21 nodes; at n = 525: complexity = 0.1612, lower bound sqrt((R+1)/2n) = 0.1414, spectral upper bound sqrt(|K_R|/n) = 0.2795
R = 50: kernel interpolation exact on 51 nodes; at n = 1275: complexity = 0.1612, lower bound sqrt((R+1)/2n) = 0.1414, spectral upper bound sqrt(|K_R|/n) = 0.2815
capacity tightness checks pass
```

## References

1. L. Sen, S. Mukherjee. On the expressive power and capacity of quantum data reuploaders. arXiv:2610.09947 (2026).
2. M. Schuld, R. Sweke, J. J. Meyer. Effect of data encoding on the expressive power of variational quantum machine learning models. Physical Review A 103, 032430 (2021), arXiv:2008.08605.
3. F. Riesz. Über ein Problem des Herrn Carathéodory. Journal für die reine und angewandte Mathematik 146, 83 (1916); L. Fejér. Über trigonometrische Polynome. Same journal, 53 (1916).
4. J. Haah. Product decomposition of periodic functions in quantum signal processing. Quantum 3, 190 (2019), arXiv:1806.10236.
5. Z. Yu, H. Yao, M. Li, X. Wang. Power and limitations of single-qubit native quantum neural networks. NeurIPS 2022, arXiv:2205.07848.
6. S. J. Szarek. On the best constants in the Khinchin inequality. Studia Mathematica 58, 197 (1976).
7. M. C. Caro, E. Gil-Fuster, J. J. Meyer, J. Eisert, R. Sweke. Encoding-dependent generalization bounds for parametrized quantum circuits. Quantum 5, 582 (2021), arXiv:2106.03880.
