# Measurement budgets for binary quantum classifiers: tight sample term and the rate 1/√B

Written 7 Nov 2026.

## Problem

[1] studies binary classifiers on d-dimensional states with score p_M(ρ) = Tr(Mρ), where M ranges over the class H of all operators 0 ≤ M ≤ I. A learning experiment has a budget of B = nS measurements: n labelled training states, each measured S times. The loss ℓ: [0,1] × {0,1} → [0,1] has slope at most L in p, |ℓ(p, y) − ℓ(p′, y)| ≤ L|p − p′|. For M chosen independently of the shot outcomes, [1, Theorem 3.1] shows that with probability 1 − δ

R(M) ≤ R̂_{n,S}(M) + 2L√(d/n) + L√(log(4n/δ)/(2S)) + √(log(2/δ)/(2n)),

where R̂_{n,S} is the training risk computed from the shot estimates p̂_i. The split that minimises a surrogate of this bound has n* of order √(dB/log B) and gives the rate (d log B/B)^{1/4} [1, Theorem 3.2]. [1] lists as open problems whether the sample term √(d/n) is tight (OP1) and whether the rate B^{−1/4} can be improved, for instance by adaptive measurements (OP4, L6).

## Results

Write R̂_n(H) = E_σ sup_M (1/n) Σ σ_i Tr(Mρ_i) for the random-sign complexity of H on states ρ_1, …, ρ_n.

**Theorem 1 (complexity, exact form).** For all states, R̂_n(H) = E_σ ‖Σ σ_i ρ_i‖₁/(2n) ≤ (1/2) min(1, √(d/n)). If n = md and the states run m times through an orthonormal basis, then R̂_n(H) = (d/(2n)) E|σ_1 + ⋯ + σ_m|, which lies between (1/(2√2))√(d/n) and (1/2)√(d/n), equals 1/2 at n = d and tends to √(d/n)/√(2π) ≈ 0.399√(d/n).

The order √(d/n), by the same trace-norm route, and the shattering of d orthogonal states are in [2]. What is added here is the exact form and the constant: the constant 1 in [1, Proposition 3.1] can be replaced by 1/2, which is reached at n = d, so the sample term of [1, Theorem 3.1] becomes L√(d/n). The repeated basis is not claimed to be the worst case for n > d; random pure states give about 0.42√(d/n) in the script.

**Theorem 2 (minimax lower bound, OP1).** Let n ≥ d and ℓ(p, y) = |p − y|. For every learner that sees n labelled examples, even with full classical descriptions of the states, there is a distribution on an orthonormal basis with labels such that the expected excess risk over the best M in H is at least 0.093√(d/n). In the model of [1], where every training example is measured at least once, n ≤ B, so for B ≥ d no allocation of a budget B, adaptive or not, gives excess risk below 0.093√(d/B) for this loss.

The order follows from the standard lower bound for agnostic learning of a class that shatters d points [3, 4]; Theorem 2 gives the explicit constant for the loss of the experiments of [1]. It also bounds every gap G that holds for all M in H at once with probability 1 − δ: empirical risk minimisation then has excess risk at most G + √(log(1/δ)/(2n)) with probability 1 − 2δ, so G ≥ 0.093√(d/n) − O(√(log(1/δ)/n)) − 2δ. In this sense the sample term √(d/n) of [1] is tight up to a constant factor. (For one fixed M the gap does not depend on d.)

**Proposition 3 (the loss of the experiments of [1] is linear).** The rescaled hinge loss of the experiments of [1], ℓ(p, y) = max{0, 1 − (2y − 1)(2p − 1)}/2, equals |p − y| = y + (1 − 2y)p on [0,1] × {0,1}. It is affine in p for each label.

**Theorem 4 (polynomial losses, rate 1/√B).** Let ℓ(·, y) be a polynomial of degree at most r for each y, and let [β_min, β_max] contain its coefficients in the binomial basis C(r, j)p^j(1 − p)^{r−j} of degree r, with Δ = β_max − β_min. Take S ≥ r shots per state and estimate ℓ(p_i, y_i) by the average of β_{K(T)} over all r-subsets T of the S shots, where K(T) counts the outcomes 1 in T. This is the classical unbiased estimate from binomial samples; for gradients of variational circuits it is used in [5]. It is unbiased, and for M chosen independently of the shot outcomes, with probability 1 − δ,

R(M) ≤ R̂^U_{n,S}(M) + L√(d/n) + √(log(2/δ)/(2n)) + Δ min(1, r√(n/B)) √(log(2/δ)/(2n)).

At S = r and n = B/r the gap is O(L√(dr/B) + (1 + Δ)√(r log(1/δ)/B)), so the rate is B^{−1/2}. For r = 1 it is tight up to constant factors by Theorem 2; for r ≥ 2 Theorem 2 does not apply (for the squared loss the excess risk on its hard instance is of order d/n). For the loss |p − y| of the experiments of [1] (r = 1, Δ = 1, L = 1) the bound reads

R(M) ≤ R̂_{n,S}(M) + √(d/n) + √(log(2/δ)/(2n)) + √(log(2/δ)/(2B)),

with the ordinary shot average R̂_{n,S}. It decreases in n at fixed B, so the best split is S = 1 and n = B: every measurement goes to a fresh training state. For the squared loss (p − y)² (r = 2, Δ = 1, L = 2) the best split is S = 2, n = B/2.

**Theorem 5 (losses with slope at most L, no log n).** For every loss with slope at most L the shot term L√(log(4n/δ)/(2S)) of [1, Theorem 3.1] can be replaced by L/(2√S) + L√(log(2/δ)/(2B)). With the sample term L√(d/n) of Theorem 1, the surrogate split is n* = 2√(dB), S* = B/n* (for B ≥ 4d), and the gap at this split is √2 L (d/B)^{1/4} plus terms of order √(log(1/δ)/n*), with no factor log B.

| Gap terms, d = 16, δ = 0.05, L = 1 | B = 10⁴ | B = 10⁶ | B = 10⁸ |
|---|---|---|---|
| Previous best bound [1, Theorem 3.1], best split | 0.923 | 0.306 | 0.101 |
| Theorem 5 with the constant of Theorem 1, best split | 0.341 | 0.105 | 0.033 |
| Theorem 4 for the loss of [1], S = 1 | 0.067 | 0.0067 | 0.0007 |

## Proofs

**Theorem 1.** For fixed σ put A = Σ σ_i ρ_i. Then sup_{0≤M≤I} Tr(MA) = Tr(A₊) = (Tr A + ‖A‖₁)/2, and E_σ Tr A = 0. So R̂_n(H) = E‖A‖₁/(2n). Further ‖A‖₁ ≤ Σ‖ρ_i‖₁ = n, and ‖A‖₁ ≤ √d ‖A‖₂ with E‖A‖₂ ≤ (E Tr A²)^{1/2} = (Σ Tr ρ_i²)^{1/2} ≤ √n. For the repeated basis, A is diagonal with entries the partial sums S_j of m signs each, so ‖A‖₁ = Σ_j |S_j|. Exactly, E|S_m| = m C(m, m/2)/2^m for even m, and E|S_{m}| = E|S_{m+1}| for odd m. With C(m, m/2)/2^m ≥ 1/√(2m) this gives E|S_m| ≥ √(m/2), and the limit is the mean of a centred normal variable. The script checks E|S_m|² ≥ m/2 for m < 60 exactly and the bound (1/2)√(d/n) on random pure and mixed states.

**Theorem 2.** Fix an orthonormal basis e_1, …, e_d and ε = (1/8)√(d/n) ≤ 1/8. For τ ∈ {±1}^d let the state be e_j with j uniform, and let y = 1 with probability 1/2 + ετ_j. A predictor with values p_j at e_j has risk (1/d)Σ_j (1/2 + ετ_j − 2ετ_j p_j), the best M in H (the projector onto the e_j with τ_j = 1) has risk 1/2 − ε, and the excess is (2ε/d) Σ_j err_j with err_j = 1 − p_j if τ_j = 1 and p_j otherwise. For each j, flipping τ_j changes the law of the data only at the examples at e_j, of which there are n/d on average, so the relative entropy is (n/d)·2ε log((1 + 2ε)/(1 − 2ε)) ≤ 0.128 for n ≥ d, and the total variation is at most √(0.128/2) ≤ 0.253. Since err_j ∈ [0, 1], its average over the two values of τ_j is at least (1 − 0.253)/2. Averaging over a uniform τ (the hypercube argument) gives an excess risk of at least ε(1 − 0.253) ≥ 0.093√(d/n) for some τ. The states are known basis vectors, so extra copies carry no information. In the model of [1] each example used costs at least one measurement, so n ≤ B. The script also runs the plug-in learner that votes at each basis state; its excess is about 0.10√(d/n), close to the bound.

**Theorem 4.** Every polynomial q of degree r has a unique expansion q(p) = Σ_j β_j C(r, j)p^j(1 − p)^{r−j}. For r independent shots with mean p the count K has P(K = j) = C(r, j)p^j(1 − p)^{r−j}, so E β_K = q(p), and averaging over r-subsets of S ≥ r shots keeps this. Each estimate lies in [β_min, β_max]. The states are independent of each other, so the additive tail bound over the n states gives the deviation Δ√(log(2/δ)/(2n)) from the exact training risk R̂_n(M). Changing one of the B shots changes the average over r-subsets of its state by at most Δr/S, hence the training risk by Δr/(nS), and the bounded-difference inequality gives Δr√(log(2/δ)/(2B)) instead. For the population risk, the standard uniform bound with the contraction inequality for losses of slope at most L gives R(M) ≤ R̂_n(M) + 2L·(1/2)√(d/n) + √(log(2/δ)/(2n)) for all M simultaneously, by Theorem 1. A union of the two events gives the claim. For |p − y| the estimate with S shots is the plain shot average of |b − y| over the B shot outcomes b, so the shot deviation is √(log(2/δ)/(2B)).

**Theorem 5.** R̂_n(M) − R̂_{n,S}(M) ≤ (L/n)Σ_i |p̂_i − p_i|. Its mean is at most L·max_p √(p(1 − p)/S) = L/(2√S), and one shot changes it by at most L/(nS), so the bounded-difference inequality gives the deviation L√(log(2/δ)/(2B)). The split minimises L√(d/n) + L√(n/B)/2.

## Scope

- Theorems 4 and 5, like [1, Theorem 3.1], assume that M is chosen independently of the shots used for the training risk, for example a fixed trained M evaluated with fresh shots. Fully adaptive shot-noisy training is not covered.
- For losses of bounded slope that are not polynomial, such as a hinge loss whose kink lies inside (0, 1), the rate (d/B)^{1/4} of Theorem 5 is a property of this route. Whether the rate 1/√B extends to all losses of bounded slope is not settled here.
- The lower bound of Theorem 2 is for the full class H, as is the upper bound of [1]; subclasses given by small circuits can have smaller complexity.

## Check

`sim/check.py` (numpy, about 5 s) checks the exact values of Theorem 1 and the bound on random states, Proposition 3 on a grid, the unbiasedness of the estimates of Theorem 4 in exact arithmetic for degrees 2 and 3 and S = r, …, r + 3, the constants of Theorem 2 together with the vote learner, and the table above. Its output is in `sim/out.txt`.

## References

1. F. O. Catak. Measurement-Budget Allocation in Quantum Learning with Finite-Shot Generalization Guarantees. arXiv:2608.24891 (2026).
2. H.-C. Cheng, M.-H. Hsieh, P.-C. Yeh. The learnability of unknown quantum measurements. Quantum Information and Computation 16, 615-656 (2016), arXiv:1501.00559.
3. M. Anthony, P. L. Bartlett. Neural Network Learning: Theoretical Foundations. Cambridge University Press (1999), Theorem 5.2.
4. A. Magner, A. Padakandla. Fat shattering, joint measurability, and PAC learnability of POVM hypothesis classes. Quantum Information Processing 23, 337 (2024), arXiv:2308.12304.
5. R. Sweke, F. Wilde, J. Meyer, M. Schuld, P. K. Fährmann, B. Meynard-Piganeau, J. Eisert. Stochastic gradient descent for hybrid quantum-classical optimization. Quantum 4, 314 (2020), arXiv:1910.01155.
