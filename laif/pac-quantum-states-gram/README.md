# PAC learning of functions on quantum states: the dimension term needs the factor 1/λ_min

2026-11-22

## Problem

The model is the one of [1]. The domain X is a set of pure states. A concept class C consists of functions c : X → {0, 1}. One example is a pair (|ϕ⟩, c(|ϕ⟩)): one copy of a state |ϕ⟩ drawn from a distribution D on X, together with its classical label. A learner receives t independent examples, may apply any joint measurement to them, and outputs any hypothesis h : X → {0, 1}; h need not lie in C. It is an (ε, δ)-learner if for every c ∈ C and every distribution D the error P_{ψ∼D}(h(ψ) ≠ c(ψ)) is at most ε with probability at least 1 − δ. The sample complexity t_{Q,C}(ε, δ) is the least such t.

For linearly independent states X = {|ψ_i⟩}, let G_{ij} = ⟨ψ_i|ψ_j⟩ be the matrix of inner products and λ_min(G) its smallest eigenvalue. In [1, Theorem 2] every C ⊆ 2^X with VC dimension d is shown to be learnable with

t_{Q,C}(ε, δ) ≤ c_U (d + ln(1/δ)) / (ε λ_min(G)),

and in [1, Theorem 1] every class needs c_L(d/ε + ln(1/δ)(1/ε + 1/Λ_C(3ε))) examples, with a function Λ_C defined by a divergence between the example states of two concepts. For two states the answer has the form Θ(ln(1/δ)(1/ε + 1/(−ln F))) [1, Proposition 2], with F the largest squared overlap. In [1, Section 3] it is left open which parameters characterize the sample complexity.

| | dependence on d of t_{Q,C}(ε, δ), linearly independent states |
|---|---|
| Previous upper bound [1, Theorem 2] | O(d/(ε λ_min(G))) |
| Previous lower bound [1, Theorem 1] | Ω(d/ε) |
| Theorem 1, a class for every d and every λ_min(G) = λ ∈ [1/d, 1] | Ω(d/(ε λ)) |

## Results

**The instance.** Let d ≥ 8 and 0 < λ ≤ 1. Take orthonormal vectors e_0, e_1, …, e_d, u and the states

|ψ_0⟩ = e_0,  |ψ_i⟩ = √(1 − λ) u + √λ e_i  (1 ≤ i ≤ d).

Then ⟨ψ_i|ψ_j⟩ = 1 − λ + λ δ_{ij} for i, j ≥ 1, and ψ_0 is orthogonal to the others. The matrix G of all d + 1 states has eigenvalues 1, λ (multiplicity d − 1) and λ + (1 − λ)d, so the states are linearly independent and λ_min(G) = λ. The class is C = {c : c(ψ_0) = 0}, all labellings of ψ_1, …, ψ_d, with VC dimension d.

**Theorem 1.** For this instance, every 0 < ε < 1/9 and 0 < δ ≤ 1/2,

t_{Q,C}(ε, δ) ≥ ((1 − δ)(1 − h(1/8)) d − 1) / (8ε K),  K = 1/d + (1 + log₂ e) λ + (λ/d) log₂(d/(4λ)),

where h is the binary entropy and 1 − h(1/8) > 0.456. For λ ≥ 1/d one has K ≤ 1/d + 3.45λ, so t_{Q,C}(ε, δ) = Ω(d/(ε λ)).

So for λ_min(G) ≥ 1/d the dependence on d in [1, Theorem 2] is tight up to constants for this class: the factor 1/λ_min(G) multiplies d. A bound of the form A(λ) d/ε + g(λ, ε, δ) for all linearly independent domains needs A(λ) = Ω(1/λ) on [1/d, 1]; in particular no bound A d/ε + g(λ, ε, δ) with a constant A holds.

## Proof

Fix D with mass 1 − 8ε on ψ_0 and 8ε/d on each ψ_i, i ≥ 1, and let c be uniform on C. Logarithms are base 2 and S is the von Neumann entropy. One example is in the state

ρ_c = (1 − 8ε) |ψ_0⟩⟨ψ_0| ⊗ |0⟩⟨0| + (8ε/d) Σ_{i≥1} |ψ_i⟩⟨ψ_i| ⊗ |c_i⟩⟨c_i|.

**Spectrum.** For s ≥ 1 let ω_s be the average of |ψ_i⟩⟨ψ_i| over a set of s indices i ≥ 1. On the span of u and the normalized sum w of the s vectors e_i, ω_s is the rank-one matrix v v* with v = (√(1 − λ), √(λ/s)), and on the rest of the span of those e_i it is λ/s times the identity. So ω_s has eigenvalues 1 − λ + λ/s once and λ/s with multiplicity s − 1, and its entropy is

φ(s) = η(1 − x_s) + x_s log(s/λ),  x_s = λ(1 − 1/s),  η(y) = −y log y.

**Information per example.** Let k = |{i : c_i = 1}| and f = k/d. The part on ψ_0 and the rest have orthogonal supports, and so do the two label values, so S(ρ_c) = h(8ε) + 8ε(h(f) + f φ(k) + (1 − f) φ(d − k)). The average over c is E ρ_c = (1 − 8ε)|ψ_0⟩⟨ψ_0| ⊗ |0⟩⟨0| + 8ε ω_d ⊗ I/2, with entropy h(8ε) + 8ε(φ(d) + 1). Hence

χ = S(E ρ_c) − E S(ρ_c) = 8ε E[1 − h(f) + Δ(f)],  Δ(f) = φ(d) − f φ(fd) − (1 − f) φ((1 − f)d).

For f ∈ {0, 1}, Δ(f) = 0. Otherwise split φ into its three parts. The part λ(1 − 1/s) log s contributes λ h(f) + (λ/d) log(f(1 − f)d), the part −x_s log λ contributes (λ/d) log(1/λ), and the part η(1 − x_s) contributes at most η(1 − x_d) ≤ x_d log e ≤ λ log e, since η ≥ 0 on [0, 1] and −ln(1 − x) ≤ x/(1 − x). With f(1 − f) ≤ 1/4 this gives Δ(f) ≤ λ h(f) + λ log e + (λ/d) log(d/(4λ)). Finally h(f) ≤ 1 and, by h(p) ≥ 4p(1 − p) = 1 − (1 − 2p)² and E(1 − 2f)² = 1/d, E[1 − h(f)] ≤ 1/d. So χ ≤ 8εK. For λ ≥ 1/d the last term of K is at most λ · 2 log(d/2)/d ≤ 0.53λ.

**Many examples.** The t examples are in the state ρ_c^{⊗t}. The marginals of E ρ_c^{⊗t} are all E ρ_c, so by subadditivity of entropy the quantity χ_t of the t examples is at most tχ. The information that any measurement on them gives about c is at most χ_t, by the bound of accessible information by the entropy difference χ [2].

**Guessing.** Since ε < 1 − 8ε, a hypothesis with error at most ε labels ψ_0 correctly and mislabels at most ε/(8ε/d) = d/8 of the states ψ_1, …, ψ_d. So with probability at least 1 − δ its labels on them differ from c in at most r = ⌊d/8⌋ places. For c uniform on {0, 1}^d, the converse inequality for guessing from limited information gives P(at most r disagreements) ≤ (I + 1)/(d − log V_r), with I the information about c and V_r ≤ 2^{d h(1/8)} the number of words within r disagreements of a fixed word. Hence (1 − δ)(1 − h(1/8))d − 1 ≤ I ≤ tχ ≤ 8εtK, which is Theorem 1.

The method, information about the concept bounded through the entropy of the average example state, is the one used for quantum PAC lower bounds in [3]. Here the domain is not orthogonal, and the bound on Δ(f) uses the overlaps: the label carries little information about which near-parallel state it belongs to.

## Check

`sim/holevo.py`, output in `sim/out_holevo.txt`:

- For d = 2, …, 10 and λ ∈ {1, 0.5, 0.1, 0.01}: the smallest eigenvalue of G is λ, and the spectrum of ω_s matches the formula for every s.
- For the same d and λ and ε ∈ {0.01, 0.1}: χ computed exactly, by enumerating all 2^d labellings with the states in ℝ^{d+2} ⊗ ℝ², equals the closed form 8ε E[1 − h(f) + Δ(f)] to 10⁻⁹, and χ ≤ 8εK for d ≥ 4.
- For d ∈ {16, 64, 256, 1024, 4096} and λ ∈ {1, 0.1, 0.01, 1/d}: the closed form satisfies χ ≤ 8εK, and the lower bound of Theorem 1 (with the exact count V_r) is compared with (d + ln(1/δ))/(ελ). At ε = δ = 0.01 the ratio lies between 43 and 62.

## Scope

- Theorem 1 is a lower bound for one family of classes, with one fixed spectrum of G. It does not determine the sample complexity of every class with linearly independent states.
- For λ < 1/d the bound is Ω(d²/ε), below the upper bound O(d/(ελ)).
- The dependence on δ is not addressed.
- The lower bound holds for every learner, proper or not, with any joint measurement on the t examples.
- The statements are Claims with the listed checks.

## References

1. J. Pérez-Guijarro. Analysis of the sample complexity for PAC-learning functions defined over quantum states. arXiv:2607.07572 (2026).
2. A. S. Holevo. Bounds for the quantity of information transmitted by a quantum communication channel. Problems of Information Transmission 9 (1973).
3. S. Bab Hadiashar, A. Nayak, P. Sinha. Optimal lower bounds for quantum learning via information theory. arXiv:2301.02227.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
