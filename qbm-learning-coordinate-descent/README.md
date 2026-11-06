# Quantum Boltzmann machine learning in O(δ₀/ε²) iterations by multiplicative weights

Written 6 Nov 2026.

## Problem

A quantum Boltzmann machine (QBM) without hidden units is the Gibbs state

ρ_θ = e^{H_θ}/Z(θ),  H_θ = Σ_{i=1}^m θ_i H_i,

of a Hamiltonian ansatz with terms H_i satisfying ‖H_i‖ ≤ 1, for example n-qubit Pauli operators. Given an n-qubit target η, the QBM learning problem of [1, Definition 1] asks for θ with

|⟨H_i⟩_{ρ_θ} − ⟨H_i⟩_η| ≤ ε for all i.

**The training method of [1].** The method minimises the relative entropy

S(η‖ρ_θ) = log Z(θ) − Σ_i θ_i ⟨H_i⟩_η − S(η),

whose gradient is ⟨H_i⟩_{ρ_θ} − ⟨H_i⟩_η. It runs stochastic gradient descent with model expectations estimated from Gibbs states, to precision κ, and data expectations to precision ξ.

**Its guarantee.** Write δ₀ = S(η‖ρ_{θ₀}) − inf_θ S(η‖ρ_θ). This equals δ₀ of [1] when a minimiser exists; the infimum also covers targets whose moments lie on the boundary, such as pure states. By [1, Theorem 1], T = 48δ₀m²(κ² + ξ²)/ε⁴ iterations give min_t E|⟨H_i⟩_{ρ_{θ_t}} − ⟨H_i⟩_η| ≤ ε for all i. This assumes κ² + ξ² ≥ ε/(2m). Each iteration uses N = O(log(mT/λ)/κ⁴) Gibbs states, or N = O(3^k log(mT/λ)/κ²) for k-local Pauli terms [1, Eqs. (10), (11)]. Here and below λ is a failure probability; in [1], λ denotes the success probability.

For k-local terms the total is T·N = 48δ₀m²3^k log(mT/λ)(κ² + ξ²)/(κ²ε⁴) ≥ 48δ₀m²3^k log(mT/λ)/ε⁴ Gibbs states, up to constants in N. [1, Theorem 2] improves the iteration count to 18m²(κ² + ξ²)/(α²ε²) when S is α-strongly convex.

**The method used here.** Learning all m expectations to ε is the feasibility problem that matrix multiplicative weights solves with a violated-constraint oracle [6, 7]. Its iterates are Gibbs states of the measured operators, so for Pauli terms they lie in the QBM ansatz. For θ₀ = 0 this gives O(n/ε²) iterations, free of m, by [7, Appendix E]. Below, that argument is written for the QBM learning problem of [1], with δ₀ in place of n ln 2 and explicit constants, and compared with [1].

## Result

**Algorithm (greedy coordinate descent).** Fix in advance a known D ≥ δ₀ and T_max = ⌈18D/ε²⌉. For θ₀ = 0, or for the pre-trained start of [1, Theorem 3], D = n ln 2 works. For a general θ₀, D = n ln 2 + 2‖θ₀‖₁ works. Estimate every data expectation h_i = ⟨H_i⟩_η once, to precision ε/6; call the estimates ĥ_i. Start from θ = θ₀. Repeat at most T_max times:

1. **Estimate.** Estimate every model expectation g_i = ⟨H_i⟩_{ρ_θ} to precision ε/6. Call the estimates ĝ_i.
2. **Stop.** If |ĝ_i − ĥ_i| ≤ 2ε/3 for all i, stop and output θ.
3. **Step.** Otherwise pick any i with |ĝ_i − ĥ_i| > 2ε/3, put s = sign(ĝ_i − ĥ_i), and set θ_i ← θ_i − (ε/3)s.

**Theorem A.** Suppose all estimates are within ε/6. Then:

- the algorithm stops after at most 18δ₀/ε² steps, so before the cap;
- its output solves the QBM learning problem: |⟨H_i⟩_{ρ_θ} − ⟨H_i⟩_η| ≤ ε for all i, for the final θ.

**Gibbs states.** Each round uses O(log(mT_max/λ)/ε⁴) Gibbs states for Pauli terms with the two-copy Bell-measurement protocol of [2], or O(3^k log(mT_max/λ)/ε²) for k-local Pauli terms with the randomized measurements of [3]. With probability 1 − λ, all estimates are then within ε/6. The data estimates use O(3^k log(m/λ)/ε²) copies of η for k-local terms, or O(log(m/λ)/ε⁴) for Pauli terms. With L = log(mD/(ελ)), the totals are:

| terms | Gibbs states, Theorem A | Gibbs states, [1, Theorem 1], best choice of κ and ξ |
|---|---|---|
| k-local Pauli | O(3^k (1 + δ₀/ε²) L/ε²) | O(δ₀ m² 3^k log(mT/λ)/ε⁴) |
| Pauli | O((1 + δ₀/ε²) L/ε⁴) | Õ(δ₀ m²/ε⁴) |

So the iteration count is free of m and needs no strong convexity; the Gibbs-state count depends on m only through log m. For k-local terms the bound is smaller by a factor Θ(m²) than the bound of [1, Theorem 1], for every choice of κ and ξ allowed there, since there T·N = 48δ₀m²3^k log(mT/λ)(κ² + ξ²)/(κ²ε⁴). For general Pauli terms the bound is smaller than that of [1] when m > 1/ε, up to logarithmic factors. Since δ₀ ≤ S(η‖I/2^n) ≤ n ln 2 for θ₀ = 0, the k-local total is O(3^k n log(mn/(ελ))/ε⁴) Gibbs states for every target. The pre-training of [1, Theorem 3] lowers δ₀ and so carries over unchanged.

The guarantee also differs in form. It holds for the output itself with probability 1 − λ, rather than for min_t E. It needs only estimates with bounded error, not unbiased ones.

## Proof

**Descent lemma.** Let ‖H_i‖ ≤ 1, s ∈ {−1, 1}, and s(g_i − h_i) ≥ ε′. Put θ′ = θ − ε′ s e_i. Then

S(η‖ρ_{θ′}) ≤ S(η‖ρ_θ) − ε′²/2.

*Proof.* The change is S(η‖ρ_{θ′}) − S(η‖ρ_θ) = log(Z(θ′)/Z(θ)) + ε′ s h_i.

- **Golden-Thompson.** By tr e^{A+B} ≤ tr(e^A e^B) for Hermitian A and B [4],
  Z(θ′)/Z(θ) ≤ tr(e^{H_θ} e^{−ε′ s H_i})/Z(θ) = ⟨e^{−ε′ s H_i}⟩_{ρ_θ}.
- **Hoeffding.** Measuring H_i on ρ_θ gives a random variable X with values in [−1, 1] and mean g_i, and ⟨e^{−ε′ s H_i}⟩_{ρ_θ} = E e^{−ε′ s X}. By Hoeffding's lemma, log E e^{−ε′ s X} ≤ −ε′ s g_i + ε′²/2.
- **Together.** The change is at most −ε′ s(g_i − h_i) + ε′²/2 ≤ −ε′² + ε′²/2. □

*Proof of Theorem A.*

- **Each step lowers S.** When the algorithm steps on i, the true gap satisfies s(g_i − h_i) ≥ |ĝ_i − ĥ_i| − ε/3 > ε/3. So the descent lemma applies with ε′ = ε/3, and S(η‖ρ_θ) drops by at least ε²/18.
- **So the steps are few.** S(η‖ρ_θ) never goes below inf_θ S(η‖ρ_θ), so at most 18δ₀/ε² ≤ T_max steps occur.
- **The output is accurate.** At the stop, |g_i − h_i| ≤ |ĝ_i − ĥ_i| + ε/3 ≤ ε for all i.
- **Gibbs states.** The sample counts follow from the measurement bounds with a union bound over the m terms and the T_max rounds. The bound D for a general θ₀ follows from log Z(θ₀) ≤ n ln 2 + ‖θ₀‖₁ and −θ₀·h ≤ ‖θ₀‖₁. □

## Remarks

1. **Related methods.** Classically, the algorithm is a fixed-step variant of the sequential update of maximum entropy estimation [5]. The same relative-entropy potential with Golden-Thompson appears in matrix exponentiated gradient updates [8] and in online learning of quantum states [9]. A sequential one-coordinate quantum iterative scaling with a convergence proof is in [10]. The argument needs no assumption on commutation of the terms.
2. **Scope.**
   - As in [1], the count is in Gibbs state preparations. The cost of preparing each Gibbs state is not treated.
   - The ε^{−6} for general Pauli terms comes from estimating all m terms to ε/6 in every round with the ε^{−4} of [2]. [1] can use a larger κ because stochastic gradient descent averages its noise.
   - Strongly convex instances [1, Theorem 2] are not treated separately.

## Check

`sim/qbm_check.py` runs the algorithm on random ansätze of k-local Pauli terms, for n = 3 to 5 qubits, k = 2 and 3, and m = 8 to 30 terms. The targets are Gibbs states of Hamiltonians that contain terms outside the ansatz, and one pure target.

- **Random noise.** The estimates carry noise drawn uniformly from [−ε/6, ε/6], and the step is on the largest estimated gap. The check asserts that each step lowers S(η‖ρ_θ) by at least (ε/3)²/2, that the number of steps is at most 18 S(η‖I/2^n)/ε², and that the last iterate is within ε on every term.
- **Worst case.** The step is on the violated coordinate with the smallest true gap above ε/3, which the estimates allow. δ₀ is computed by convex minimisation. The check asserts the per-step drop and at most 18δ₀/ε² steps.

```
n = 3, k = 2, m = 8, eps = 0.1: 130 steps <= 18 S0/eps^2 = 3020; every step lowered S by >= 0.00159 >= (eps/3)^2/2 = 0.00056; last iterate within eps on all 8 terms
n = 4, k = 2, m = 12, eps = 0.08: 198 steps <= 18 S0/eps^2 = 5200; every step lowered S by >= 0.00100 >= (eps/3)^2/2 = 0.00036; last iterate within eps on all 12 terms
n = 5, k = 2, m = 20, eps = 0.1: 215 steps <= 18 S0/eps^2 = 4806; every step lowered S by >= 0.00101 >= (eps/3)^2/2 = 0.00056; last iterate within eps on all 20 terms
n = 5, k = 3, m = 30, eps = 0.15: 125 steps <= 18 S0/eps^2 = 1826; every step lowered S by >= 0.00214 >= (eps/3)^2/2 = 0.00125; last iterate within eps on all 30 terms
worst case, n = 3, k = 2, m = 8, eps = 0.1: 86 steps <= 18 delta0/eps^2 = 1093; smallest drop 1.146 (eps/3)^2/2
worst case, n = 4, k = 2, m = 12, eps = 0.08: 242 steps <= 18 delta0/eps^2 = 3509; smallest drop 1.114 (eps/3)^2/2
worst case, n = 5, k = 2, m = 20, eps = 0.1: 417 steps <= 18 delta0/eps^2 = 4420; smallest drop 1.145 (eps/3)^2/2
worst case, n = 5, k = 3, m = 30, eps = 0.15: 208 steps <= 18 delta0/eps^2 = 1372; smallest drop 1.059 (eps/3)^2/2
worst case, n = 4, k = 2, m = 12, eps = 0.1, pure target: 89 steps <= 18 delta0/eps^2 = 859; smallest drop 1.012 (eps/3)^2/2
greedy coordinate descent checks pass
```

## References

1. L. Coopmans, M. Benedetti. On the sample complexity of quantum Boltzmann machine learning. Communications Physics (2024), arXiv:2306.14969.
2. H.-Y. Huang, R. Kueng, J. Preskill. Information-theoretic bounds on quantum advantage in machine learning. Physical Review Letters 126, 190505 (2021), arXiv:2101.02464.
3. H.-Y. Huang, R. Kueng, J. Preskill. Predicting many properties of a quantum system from very few measurements. Nature Physics 16, 1050 (2020), arXiv:2002.08907.
4. S. Golden. Lower bounds for the Helmholtz function. Physical Review 137, B1127 (1965); C. J. Thompson. Inequality with applications in statistical mechanics. Journal of Mathematical Physics 6, 1812 (1965).
5. M. Dudík, S. J. Phillips, R. E. Schapire. Maximum entropy density estimation with generalized regularization and an application to species distribution modeling. Journal of Machine Learning Research 8, 1217 (2007).
6. S. Arora, S. Kale. A combinatorial, primal-dual approach to semidefinite programs. STOC 2007; Journal of the ACM 63, 12 (2016).
7. F. G. S. L. Brandão, A. Kalev, T. Li, C. Y.-Y. Lin, K. M. Svore, X. Wu. Quantum SDP solvers: large speed-ups, optimality, and applications to quantum learning. ICALP 2019, arXiv:1710.02581.
8. K. Tsuda, G. Rätsch, M. K. Warmuth. Matrix exponentiated gradient updates for on-line learning and Bregman projection. Journal of Machine Learning Research 6, 995 (2005).
9. S. Aaronson, X. Chen, E. Hazan, S. Kale, A. Nayak. Online learning of quantum states. NeurIPS 2018, arXiv:1802.09025.
10. Z. Ji. Classical and quantum iterative optimization algorithms based on matrix Legendre-Bregman projections. arXiv:2209.14185 (2022).
