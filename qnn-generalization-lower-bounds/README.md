# Generalization lower bounds for quantum neural networks

Written 5 Nov 2026.

## Setting

A quantum model has T trainable gates with parameters θ = (θ₁, …, θ_T), each gate acting on at most two qubits and used at most M times, together with any number of fixed gates. On input x it outputs f(x; θ), the expectation of an observable of operator norm at most 1. For N training examples, [1] proves that with high probability the generalization error of every θ is O(√(T log T / N)) when each gate is used once (Theorem 1 of [1]), and O(√(T log(MT) / N)) with reuse (Theorem 2 of [1]).

Inputs x₁, …, x_m are *shattered at margin γ* if for every sign pattern p ∈ {±1}^m some θ has p_j f(x_j; θ) ≥ γ for all j.

## Results

Let γ ∈ (0, 1), w = arccos(γ)/(2π) < 1/4 and ℓ = log₂(1/w). For γ = 1/2, w = 1/6 and ℓ = log₂ 6 ≈ 2.585.

**Theorem 1 (shattering).** There is a family of models as above, on TM + 1 qubits, with observable X on one qubit and two-qubit controlled rotations as trainable gates, that shatters m inputs at margin γ, where

- m = ⌊T log₂(M + 1) / ℓ⌋ for all T and M, and
- m = ⌊T log₂T / (4ℓ)⌋ for all T ≥ T₀(γ), with T₀(1/2) = 200.

So m ≥ T log₂((M + 1)T) / (8ℓ) − 1 for T ≥ T₀(γ).

**Theorem 2 (generalization gap).** Let x₁, …, x_m be shattered at margin γ by a model class with outputs in [−1, 1], on which the empirical risk attains its infimum (for the models of Theorem 1 it does, by compactness). Let the data distribution be uniform on {x₁, …, x_m}, with label y a fair ±1 coin independent of x, and let the loss be (1 − y f)/2 ∈ [0, 1]. Then every θ has risk exactly 1/2, and for N ≥ m samples every empirical risk minimizer θ̂ satisfies

E[R(θ̂) − R̂(θ̂)] ≥ (γ/4) √(m/N).

**Corollary 3.** For the models of Theorem 1, T ≥ T₀(γ) and N ≥ m, the expected generalization gap of empirical risk minimization is at least (γ/4)√(m/N) = Ω_γ(√(T log((M + 1)T) / N)). With γ = 1/2, the bounds of [1] are tight up to a constant factor, and the logarithmic factor in them is needed for worst-case data and architecture. Here the loss is bounded by 1, as in [1], whose bounds hold with high probability and give the same order in expectation after integrating their tail.

In the other direction, the covering bound of Theorem C.3 of [1], at scale γ/(2MT) per gate, implies that a class with T gates used at most M times has at most O(T log(MT/γ)) inputs shattered at margin γ, since two different sign patterns give functions at sup-distance at least 2γ. With Theorem 1, the largest size of a set shattered at a fixed margin is Θ(T log((M + 1)T)) for T ≥ 2.

## The model

Inputs are vectors s ∈ {0, …, M}^T, held in unary in a register of TM qubits: qubit (i, r) is 1 exactly when s_i ≥ r. A target qubit starts in |+⟩. For each gate i and each r = 1, …, M, a rotation diag(1, e^{iθ_i}) is applied to the target, controlled by qubit (i, r). So each trainable gate is a two-qubit controlled rotation used M times, and for M = 1 there are T + 1 qubits. The target ends in (|0⟩ + e^{i⟨s, θ⟩}|1⟩)/√2, so measuring X gives

f_s(θ) = cos⟨s, θ⟩.

## Proof of Theorem 1

Write e(x) = e^{2πix} and ‖x‖ for the distance of x to the nearest integer. Let A be the m × T integer matrix with rows s₁, …, s_m.

**Lemma 4 (bump).** Let h(x) = max(0, 1 − ‖x‖/w) on R/Z. Then h(x) = Σ_{k∈Z} w ρ(k) e(kx) with ρ(0) = 1 and ρ(k) = (sin(πkw)/(πkw))². All ρ(k) are nonnegative and Σ_k ρ(k) = h(0)/w = 1/w. Write τ = 1/w − 1 for the sum over k ≠ 0.

*Proof.* As w < 1/2, the triangle of height 1 and half-width w does not wrap around R/Z, and its Fourier coefficient is w ρ(k). The series converges absolutely and uniformly, so it sums to h(0) = 1 at x = 0. ∎

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

For each γ this holds for all large T, since the left side is 2^{O(√T log T)}. For γ = 1/2 (τ = 5) the script `sim/lower_bound_sum.py` checks it for every T from 200 to 10⁴. For T ≥ 10⁴ it follows from u ≤ 1.28√T + 1 and 5m ≤ T², which give 2 log₂T (1.28√T + 1) + log₂(1.28√T + 1) ≤ T − 1, an inequality that holds at T = 10⁴, while the derivative of its left side is below 1/4 for T ≥ 10⁴. ∎

The two bounds hold for all M ≥ 1, since binary inputs use each gate at most once. Then max(a/4, b) ≥ (a + b)/8 with a = T log₂T and b = T log₂(M + 1) gives the combined form.

## Proof of Theorem 2

The loss of θ on (x, y) is (1 − y f(x; θ))/2, and E[y | x] = 0, so R(θ) = 1/2 for every θ. Given a sample (x^{(1)}, y^{(1)}), …, (x^{(N)}, y^{(N)}), let n_j be the number of samples at x_j and Y_j the sum of their labels. Then

R̂(θ) = 1/2 − (1/(2N)) Σ_j Y_j f(x_j; θ).

Choose θ with sign f(x_j; θ) = sign Y_j and |f(x_j; θ)| ≥ γ for all j, which shattering allows. This gives min_θ R̂ ≤ 1/2 − (γ/(2N)) Σ_j |Y_j|, and every minimizer θ̂ attains this minimum. Given n_j, Y_j is a sum of n_j independent fair signs, and E|Y_j| ≥ √(n_j/2) by the first-moment inequality for such sums with its optimal constant [3]. Each n_j is binomial with mean λ = N/m ≥ 1 and E n_j² ≤ λ² + λ ≤ 2λ². From (E n)² = (E[n^{1/4} n^{3/4}])² ≤ E√n · E n^{3/2} and (E n^{3/2})² ≤ E n · E n², we get E√n ≥ (E n)^{3/2}/(E n²)^{1/2} ≥ √(λ/2). So

E[R(θ̂) − R̂(θ̂)] ≥ (γ/(2N)) · m · √(1/2) · √(λ/2) = (γ/4)√(m/N). ∎

## Remarks

**Scope.** The lower bounds are for worst-case data and for empirical risk minimization. They do not concern the error on a fixed target function, and for structured data the generalization error can be much smaller. With the combined form of Theorem 1, the constant in Corollary 3 is about γ/(8√(2ℓ)), so it depends on γ through γ/√ℓ, with ℓ = log₂(2π/arccos γ).

**On a gate-independent bound.** [4] states a generalization bound of order 1/√N for quantum models of any size, with constants that depend on the observable norm and the loss but not on the number of gates. For the loss of Theorem 2 that bound reads 1/√N + 3√(log(2/δ)/(2N)) with probability 1 − δ, which gives an expected gap below 3.8/√N. For γ = 1/2 and T = 2000, Theorem 1 gives m = 2121, and Corollary 3 gives an expected gap of at least 5.7/√N for N ≥ 2121. The gap of Corollary 3 grows like √(T log T). The models of Theorem 1 meet the hypotheses of [4]: bounded loss, Lipschitz in the output, and an observable of norm 1. This hints at a possible gap in the proof of Theorem B.1 of [4], where the cross terms E[σ_m σ_n (w*)ᵀx^{(m)} (w*)ᵀx^{(n)}] are bounded as if w* did not depend on σ. A small example in the linear class of that theorem: for n inputs √n e_1, …, √n e_n, the constraint set is the set of vectors whose coordinates are all ±1/√n, with free signs, so the empirical Rademacher complexity is 1, against the stated √(1/n).

## Lean

The folder [lean/](lean/) checks the combinatorial core of Theorem 1 in Lean 4 with Mathlib, with no `sorry` and only the standard axioms. Build it with `lake build`. Running `lake env lean QNNShatter/Axioms.lean` prints the axioms of the main theorems.

**Checked:**

- **Anti-concentration** (`AntiConcentration.lean`): for nonzero integer weights k, at most C(v, ⌊v/2⌋) vectors in {0, 1}^v solve Σ_j k_j b_j = c. If some weight is nonzero, at most (M + 1)^{v−1} vectors in {0, …, M}^v do. The proof goes through antichains.
- **Averaging** (`Average.lean`): the bounds on the mean of S(A) over all matrices, for weights ρ with ρ(0) = 1 and Σ_{z ≠ 0} ρ(z) = τ:
  - ((1 + τ)^m − 1)/(M + 1)^T for entries in {0, …, M};
  - Σ_{v=1}^m C(m, v) τ^v q(v)^T for entries in {0, 1}.

  In each case some A has S(A) < 1 when the bound is below 1.
- **Lemma 5** (`Bump.lean`, `Bump.shatters`): if S(A) < 1, every sign pattern p has some θ with γ ≤ p_j cos⟨s_j, θ⟩ for all j. It averages over a finite grid in place of the torus.
- **End-to-end statements:** `exists_shattered_reuse_of_pow_le` gives a shattered m × T matrix with entries in {0, …, M} whenever (1 + τ)^m ≤ (M + 1)^T. This is the first bound of Theorem 1, with 1 + τ = 1/w. `exists_shattered_binary` gives a 0/1 matrix whenever the binary sum is below 1.

**Hypotheses and gaps:**

- **Lemma 4 as a hypothesis:** the Fourier expansion of the bump is a hypothesis (the structure `Bump`). It asks for nonnegative ρ with ρ(0) = 1, an expansion h(x) = Σ_z w ρ(z) e(zx), and h(x) ≠ 0 only where cos(2πx) ≥ γ.
- **Not covered:**
  - the circuit itself, since the class is taken as cos⟨s, θ⟩;
  - the numeric analysis of the binary sum: q(v) ≤ √(2/(π(v − 1))), u(mτ)^u ≤ 2^{T−1}, and the choice m = ⌊T log₂T/(4ℓ)⌋;
  - Theorem 2;
  - Corollary 3.

## Simulations

The scripts in `sim/` need Python 3 with NumPy.

- `lower_bound_sum.py` checks the Fourier identity of Lemma 5 against Monte Carlo on a three-row example, prints the largest m for which the binary sum is below 1 (for γ = 1/2 it gives m = 2,218 at T = 1,000), and checks the explicit choice of Theorem 1.
- `cos_family.py TMAX SAMPLES TRIES` looks for shattered sets of the family f_s(θ) = cos⟨s, θ⟩ at margin 1/4 for T up to TMAX by sampling θ, so each m it prints is a lower bound (for example `cos_family.py 5 1500000 150`).
- `gen_gap.py` takes a set shattered at margin 1/4 for T = 5 and checks Theorem 2 against sampled empirical risk minimization for N from m to 1000m.

## References

1. M. C. Caro, H.-Y. Huang, M. Cerezo, K. Sharma, A. Sornborger, L. Cincio, P. J. Coles. Generalization in quantum machine learning from few training data. Nature Communications 13, 4919 (2022). arXiv:2111.05292.
2. P. Erdős. On a lemma of Littlewood and Offord. Bulletin of the AMS 51 (1945), 898-902.
3. S. J. Szarek. On the best constants in the Khinchin inequality. Studia Mathematica 58 (1976), 197-208.
4. X. Wang, R. Wu. Tight Generalization Bound for Supervised Quantum Machine Learning. arXiv:2510.24348.
