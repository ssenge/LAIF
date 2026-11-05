# Generalization lower bounds for quantum neural networks

Written 5 Nov 2026.

## Setting

A quantum model has T trainable gates with parameters θ = (θ₁, …, θ_T), each gate acting on at most two qubits and used at most M times, together with any number of fixed gates. On input x it outputs f(x; θ), the expectation of an observable of operator norm at most 1. For N training examples, [1] proves that with high probability the generalization error of every θ is O(√(T log T / N)) when each gate is used once (Theorem 1 of [1]), and O(√(T log(MT) / N)) with reuse (Theorem 2 of [1]).

Inputs x₁, …, x_m are *shattered at margin γ* if for every sign pattern p ∈ {±1}^m some θ has p_j f(x_j; θ) ≥ γ for all j.

## Results

Let γ ∈ [0, 1), w = arccos(γ)/(2π) and ℓ = log₂(1/w). For γ = 1/2, w = 1/6 and ℓ = log₂ 6 ≈ 2.585.

**Theorem 1 (shattering).** There is a family of models as above, on T + 1 qubits for M = 1, with observable X on one qubit and two-qubit controlled rotations as trainable gates, that shatters m inputs at margin γ, where

- m = ⌊T log₂(M + 1) / ℓ⌋ for all T and M, and
- m = ⌊T log₂T / (4ℓ)⌋ for all T ≥ T₀(γ), with T₀(1/2) = 200.

So m ≥ T log₂((M + 1)T) / (8ℓ) − 1 for T ≥ T₀(γ).

**Theorem 2 (generalization gap).** Let x₁, …, x_m be shattered at margin γ by any model class with outputs in [−1, 1]. Let the data distribution be uniform on {x₁, …, x_m}, with label y a fair ±1 coin independent of x, and let the loss be (1 − y f)/2 ∈ [0, 1]. Then every θ has risk exactly 1/2, and for N ≥ m samples every empirical risk minimizer θ̂ satisfies

E[R(θ̂) − R̂(θ̂)] ≥ (γ/4) √(m/N).

**Corollary 3.** For the models of Theorem 1, T ≥ T₀(γ) and N ≥ m, the expected generalization gap of empirical risk minimization is at least (γ/4)√(m/N) = Ω_γ(√(T log((M + 1)T) / N)). So the bounds of [1] are tight up to a factor that depends only on γ, and the logarithmic factor in them is needed for worst-case data.

In the other direction, the covering argument of [1] nets each gate at scale γ/(MT), so a class with T gates used at most M times has at most O(T log(MT/γ)) inputs shattered at margin γ (two different sign patterns give functions at sup-distance at least 2γ). With Theorem 1, the largest size of a set shattered at a fixed margin is Θ(T log(MT)).

## The model

Inputs are vectors s ∈ {0, …, M}^T, held in a register in the computational basis, together with a target qubit in |+⟩. For each gate i and each r = 1, …, M, a rotation diag(1, e^{iθ_i}) is applied to the target, controlled by the predicate s_i ≥ r. For M = 1 the control is qubit i of the register, so each trainable gate is a two-qubit controlled rotation used once. For M > 1 the predicate is computed into an ancilla by fixed gates and uncomputed afterwards. The target ends in (|0⟩ + e^{i⟨s, θ⟩}|1⟩)/√2, so measuring X gives

f_s(θ) = cos⟨s, θ⟩.

## Proof of Theorem 1

Write e(x) = e^{2πix} and ‖x‖ for the distance of x to the nearest integer. Let A be the m × T integer matrix with rows s₁, …, s_m.

**Lemma 4 (bump).** Let h(x) = max(0, 1 − ‖x‖/w) on R/Z. Then h(x) = Σ_{k∈Z} w ρ(k) e(kx) with ρ(0) = 1 and ρ(k) = (sin(πkw)/(πkw))². All ρ(k) are nonnegative and Σ_k ρ(k) = h(0)/w = 1/w. Write τ = 1/w − 1 for the sum over k ≠ 0.

*Proof.* The Fourier coefficient of the triangle of height 1 and half-width w is w ρ(k), and since the series converges absolutely, it sums to h(0) = 1 at x = 0. ∎

**Lemma 5 (all patterns).** Let S(A) = Σ_{k ∈ Z^m \ {0}, Aᵀk = 0} Π_j ρ(k_j). If S(A) < 1, the rows of A are shattered at margin γ.

*Proof.* Fix p ∈ {±1}^m and put t_j = 0 if p_j = 1 and t_j = 1/2 if p_j = −1. For φ uniform on (R/Z)^T, let G(φ) = Π_j h((Aφ)_j − t_j). Expanding each factor by Lemma 4 and using E e(⟨Aᵀk, φ⟩) = [Aᵀk = 0],

E G = w^m Σ_{Aᵀk = 0} Π_j ρ(k_j) e(−k_j t_j) ≥ w^m (1 − S(A)) > 0.

So some φ has G(φ) > 0, that is ‖(Aφ)_j − t_j‖ < w for all j. With θ = 2πφ, cos⟨s_j, θ⟩ = cos(2π(Aφ)_j) is at least cos(2πw) = γ when t_j = 0, and at most −γ when t_j = 1/2. ∎

The condition S(A) < 1 also excludes zero rows and equal rows, since those give a kernel vector with one or two nonzero entries.

Now draw A at random and bound E S(A) = Σ_{k ≠ 0} Π_j ρ(k_j) Pr[Aᵀk = 0]. The T columns of A are independent, so Pr[Aᵀk = 0] = Π_i Pr[Σ_j k_j A_ji = 0].

**Reuse (first bound).** Let the entries of A be uniform on {0, …, M}. For k ≠ 0 pick j with k_j ≠ 0. Given the other entries of column i, at most one value of A_ji solves the equation, so Pr[Aᵀk = 0] ≤ (M + 1)^{−T}. Hence

E S(A) ≤ ((1/w)^m − 1)(M + 1)^{−T} < 2^{mℓ − T log₂(M + 1)} ≤ 1

for m = ⌊T log₂(M + 1)/ℓ⌋. So some A has S(A) < 1.

**Binary inputs (second bound).** Let the entries of A be fair bits. If k has v nonzero entries, then by the anti-concentration bound of [2] each column gives probability at most q(v) = C(v, ⌊v/2⌋)/2^v. Here q(v) ≤ 1/2 for v ≥ 1, and q(v) ≤ √(2/(π(v − 1))) for v ≥ 2, from C(2n, n)/4^n ≤ 1/√(πn). Grouping k by its support,

E S(A) ≤ Σ_{v=1}^{m} C(m, v) τ^v q(v)^T.

Let m = ⌊T log₂T/(4ℓ)⌋ and u = ⌈(4/π)√T⌉. Terms with v ≥ u + 1 have q(v)^T ≤ (2/(πu))^{T/2} ≤ (2√T)^{−T/2}, and C(m, v)τ^v summed over all v is at most (1 + τ)^m = 2^{mℓ} ≤ T^{T/4}. So they add up to at most 2^{−T/2}. Terms with v ≤ u are each at most (mτ)^v 2^{−T}, so they add up to at most u(mτ)^u 2^{−T}. Hence E S(A) < 1 as soon as

u (mτ)^u ≤ 2^{T−1}.

For each γ this holds for all large T, since the left side is 2^{O(√T log T)}. For γ = 1/2 (τ = 5) the script `sim/lower_bound_sum.py` checks it for every T from 200 to 10⁴. For T ≥ 10⁴ it follows from u ≤ 1.28√T + 1 and 5m ≤ T², which give 2 log₂T (1.28√T + 1) + log₂(1.28√T + 1) ≤ T − 1, an inequality that holds at T = 10⁴ and whose slack increases with T. ∎

The two bounds hold for all M ≥ 1, since binary inputs use each gate at most once. Then max(a/4, b) ≥ (a + b)/8 with a = T log₂T and b = T log₂(M + 1) gives the combined form.

## Proof of Theorem 2

The loss of θ on (x, y) is (1 − y f(x; θ))/2, and E[y | x] = 0, so R(θ) = 1/2 for every θ. Given a sample (x^{(1)}, y^{(1)}), …, (x^{(N)}, y^{(N)}), let n_j be the number of samples at x_j and Y_j the sum of their labels. Then

R̂(θ) = 1/2 − (1/(2N)) Σ_j Y_j f(x_j; θ).

Choose θ with sign f(x_j; θ) = sign Y_j and |f(x_j; θ)| ≥ γ for all j, which shattering allows. This gives min_θ R̂ ≤ 1/2 − (γ/(2N)) Σ_j |Y_j|, and every minimizer θ̂ has the same empirical risk. Given n_j, Y_j is a sum of n_j independent fair signs, and E|Y_j| ≥ √(n_j/2) by the first-moment inequality for such sums with its optimal constant [3]. Each n_j is binomial with mean λ = N/m ≥ 1 and E n_j² ≤ λ² + λ ≤ 2λ². By Hölder's inequality, E√n ≥ (E n)^{3/2}/(E n²)^{1/2} ≥ √(λ/2). So

E[R(θ̂) − R̂(θ̂)] ≥ (γ/(2N)) · m · √(1/2) · √(λ/2) = (γ/4)√(m/N). ∎

## Remarks

**Scope.** The lower bounds are for worst-case data and for empirical risk minimization. They do not concern the error on a fixed target function, and for structured data the generalization error can be much smaller. The constant depends on γ through 1/ℓ = 1/log₂(2π/arccos γ).

**On a gate-independent bound.** [4] states a generalization bound of order 1/√N for quantum models of any size, with constants that depend on the observable norm and the loss but not on the number of gates. For the loss of Theorem 2 that bound reads 1/√N + 3√(log(2/δ)/(2N)) with probability 1 − δ, which gives an expected gap below 3.8/√N. For γ = 1/2 and T = 2000, Theorem 1 gives m = 2121, and Corollary 3 gives an expected gap of at least 5.7/√N for N ≥ 2121. The gap of Corollary 3 grows like √(T log T). This hints at a possible gap in the proof of Theorem B.1 of [4], where the cross terms E[σ_m σ_n (w*)ᵀx^{(m)} (w*)ᵀx^{(n)}] are bounded as if w* did not depend on σ. In the linear class of that theorem, the inputs x^{(m)} = √M e_m force w = ±(1, …, 1)/√M with free signs, so the empirical Rademacher complexity is 1 there.

## Simulations

The scripts in `sim/` need Python 3 with NumPy.

- `lower_bound_sum.py` checks the Fourier identity of Lemma 5 against Monte Carlo on a three-row example, prints the largest m for which the binary sum is below 1 (for γ = 1/2 it gives m = 2,218 at T = 1,000), and checks the explicit choice of Theorem 1.
- `cos_family.py` looks for shattered sets of the family f_s(θ) = cos⟨s, θ⟩ for small T by sampling θ, so each m it prints is a lower bound.
- `gen_gap.py` takes a shattered set for T = 5 and checks Theorem 2 against sampled empirical risk minimization for N from m to 1000m.

## References

1. M. C. Caro, H.-Y. Huang, M. Cerezo, K. Sharma, A. Sornborger, L. Cincio, P. J. Coles. Generalization in quantum machine learning from few training data. Nature Communications 13, 4919 (2022). arXiv:2111.05292.
2. P. Erdős. On a lemma of Littlewood and Offord. Bulletin of the AMS 51 (1945), 898-902.
3. S. J. Szarek. On the best constants in the Khinchin inequality. Studia Mathematica 58 (1976), 197-208.
4. X. Wang, R. Wu. Tight Generalization Bound for Supervised Quantum Machine Learning. arXiv:2510.24348.
