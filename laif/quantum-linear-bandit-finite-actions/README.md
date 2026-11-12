# Quantum linear bandits with finite action sets: √(log K) in place of log K

2026-11-11

## Problem

In a quantum linear bandit [1] the learner picks an action x from a finite set A ⊂ R^d with |A| = K in each round. The action's mean reward is μ(x) = ⟨x, θ⟩ ∈ [0, 1] for an unknown θ, and the round consists of one query to the quantum reward oracle of x or its inverse. The regret after T rounds is Σ_t (max_x μ(x) − μ(x_t)).

For finite action sets [1] gives two elimination algorithms, with expected regret

O(d log T · log(KT) · log(dT) · log log(dT))  [1, Theorem 5.4]  and  O(d^{3/2} log T · log(dT))  [1, Corollary 5.7].

The first uses estimates with small variance but needs all K of them accurate at once, which costs log(KT). The second avoids the dependence on K but loses √d when errors spread through the prediction weights. The lower bound is Ω(d log(1 + T/d)) [1]. Whether the two advantages can be combined, for instance with a dependence on K of order √(log K) as in the classical case, is left open in [1, Section 6].

## Result

**Theorem 1.** For every finite action set A ⊂ R^d with K actions, every T ≥ 2 with dT ≥ 3, the elimination algorithm below has

E[Regret(T)] = O(d log T · log(dT) · √(log(KT))).

**Corollary 1.** Running this algorithm when log(KT) ≤ d, and the algorithm of [1, Corollary 5.7] otherwise, gives

E[Regret(T)] = O(d log T · log(dT) · √(min(log(KT), d))).

Previous best bound: the smaller of the two bounds of [1] above. Corollary 1 improves on [1, Theorem 5.4] by the factor √(log(KT)) · log log(dT) for every K, and on [1, Corollary 5.7] by the factor √(d / log(KT)) whenever log(KT) < d.

## Algorithm

The algorithm keeps the phase structure of [1]. Phase ℓ has target accuracy ε = 2^{−ℓ} and an active set A_ℓ of rank r. It computes the small-support design of [1, Lemma 5.1]: support S with |S| ≤ c_s r, weights π, and prediction weights α_a(x) with x = Σ_a α_a(x) a and Σ_a α_a(x)²/π(a) ≤ C_G r. It estimates the mean of each support action a, sets μ̃(x) = Σ_a α_a(x) Y_a, and drops every x with μ̃(x) < max μ̃ − 2ε.

What changes is the estimate Y_a of the support means. Through the rotation of [1, Lemma 2.4] the mean p = μ(a) is an amplitude, p = sin² φ, and the amplitude amplification operator has the eigenphases ±2φ. The algorithm runs the boosted phase estimation of [2, Theorem 28, Section 6.3] on this operator: 2m + 1 phase estimations, each with register size M, a fresh register and a uniformly random phase shift, and the midpoint of the shortest arc that contains m + 1 of the 2m + 1 results. All runs act on one prepared copy of the initial state. Its two eigenvector components are orthogonal, so the joint law of the results is a mixture over the sign of the eigenphase in which all runs share the sign. With Z the resulting point on the unit circle, the estimate is

Y = 1/2 − Re Z / (2λ),  λ = λ(M, m) = E[cos(error of the boosted estimate)].

By [2, Theorem 28] the error has a law that depends only on M and m and is symmetric, and it is at most 6/M with probability at least 1 − e^{−m/4}. This gives:

- E[Y] = p exactly, for either sign;
- 1 − λ ≤ 18/M² + 2e^{−m/4}, so λ ≥ 0.775 for M ≥ 12 and m ≥ 12;
- on the event G that the error is at most 6/M, Y − p lies in the interval c ± 3/(λM), where c = −(1 − λ) cos(2φ)/(2λ) is a constant of the action;
- |Y − p| ≤ 3;
- fewer than 2(2m + 1)M queries, since each controlled step costs one query to the oracle and one to its inverse [1].

λ is computed classically to any precision. An error η in λ adds a bias of at most η to each Y_a, and η ≤ ε/(16 √(C_G r)) keeps the resulting error of every μ̃(x) below ε/16. In phase ℓ the parameters are

M_a = the least power of two ≥ max(12, c₃ √(r π(a) ln(4K(L+1)/δ)) / ε),  m = ⌈4 ln(C r T (L+1)/ε)⌉,

with L = ⌈log₂ T⌉, δ = 1/T, c₃ = 7 √C_G and C = max(2c_s, 24 √C_G, e³).

## Proof

*Accuracy in one phase.* Write e_a = Y_a − μ(a) and let c_a be the constant of action a. The e_a are independent and E e_a = 0. Let G_a be the event that the boosted estimate of action a has error at most 6/M_a, and let e'_a = e_a on G_a and e'_a = c_a otherwise. On G = ∩_a G_a the error is μ̃(x) − μ(x) = Σ_a α_a(x) e'_a for every x.

- *Bias.* E e'_a = E[(c_a − e_a) 1_{G_a^c}], so |E e'_a| ≤ 3e^{−m/4}. Hence |Σ_a α_a(x) E e'_a| ≤ 3e^{−m/4} Σ_a |α_a(x)| ≤ 3e^{−m/4} √(C_G r) ≤ ε/8 by the choice of m.
- *Fluctuation.* The variables e'_a are independent and lie in intervals of length 6/(λ M_a) ≤ 7.75/M_a. The concentration inequality for sums of independent bounded variables gives

  P(|Σ_a α_a(x)(e'_a − E e'_a)| > u) ≤ 2 exp(−2u² / Σ_a α_a(x)² (7.75/M_a)²),

  and Σ_a α_a(x)²/M_a² ≤ ε² Σ_a α_a(x)²/(c₃² r π(a) ln(4K(L+1)/δ)) ≤ C_G ε²/(c₃² ln(4K(L+1)/δ)). With u = 13ε/16 and c₃ = 7√C_G the exponent is at least ln(4K(L+1)/δ), so a union bound over the K actions bounds the failure probability by δ/(2(L+1)).
- *Failure of the events G_a.* P(G^c) ≤ |S| e^{−m/4} ≤ δ/(2(L+1)).

So with probability at least 1 − δ/(L+1), |μ̃(x) − μ(x)| ≤ ε/8 + ε/16 + 13ε/16 = ε for all active x. The √(log K) appears because the union bound acts on a sum of bounded variables whose tail decays like exp(−c u²). Only the |S| = O(r) events G_a need a bound of exponential order, and they cost log r, not log K.

*Queries in one phase.* Σ_a 2(2m + 1) M_a = O(m (r + √(r ln(KT)) Σ_a √π(a) / ε)) = O(r log(dT) √(log(KT)) / ε), using Σ_a √π(a) ≤ √|S| and ε ≥ 1/(2T).

*Regret.* On the event that every phase is accurate, the elimination argument of [1, Theorem 5.4] applies unchanged. The best action stays active, and every action active in phase ℓ ≥ 1 has gap at most 8ε. Phase ℓ therefore costs regret O(r log(dT) √(log(KT))). There are at most log₂ T + 1 phases, and the failure probability δ = 1/T adds at most 1 to the expected regret. Corollary 1 follows by choosing the algorithm from d, K and T before the first round.

## Check

`sim/estimator.py` simulates the boosted estimator from the exact output law of phase estimation with a random phase shift, for (M, m) = (16, 12), (32, 12), (64, 16) and (128, 20). It checks unbiasedness for means from 0 to 1, the tail bound P(|Y − p| > 4/M) ≤ e^{−m/4}, the bound |Y| ≤ 2 and 1 − λ ≤ 18/M² + 2e^{−m/4}. `sim/uniform.py` runs one phase on random action sets in R^6 with K from 10 to 10⁴ and ε = 0.05, with a design of support 6 and G-value at most 12 found by the Frank-Wolfe method. The queries per phase grow like √(ln K): the ratio queries · ε/(d √(ln K)) stays between 150 and 152. In 200 runs for each K, no estimate μ̃(x) is off by more than ε (output in `sim/uniform_out.txt`).

## Scope

- **Assuming:** the error law of the boosted phase estimation of [2, Theorem 28, Section 6.3], with an exact uniformly random phase shift, and the small-support design of [1, Lemma 5.1].
- **Not formalized:** the theorem has no Lean proof.
- C_G and c_s are the constants of [1, Lemma 5.1], which are not explicit there.

## References

[1] M. Liu, Z. Li, J. C. S. Lui. Quantum Multi-Armed Bandits and Linear Bandits: Lower Bounds and Algorithms. arXiv:2608.14319.
[2] J. van Apeldoorn, A. Cornelissen, A. Gilyén, G. Nannicini. Quantum tomography using state-preparation unitaries. SODA 2023, arXiv:2207.08800.

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
