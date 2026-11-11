# Quantum linear bandits with finite action sets: √(log K) in place of log K

2026-11-11

## Problem

In a quantum linear bandit [1] the learner picks an action x from a finite set A ⊂ R^d with |A| = K in each round. The action's mean reward is μ(x) = ⟨x, θ⟩ ∈ [0, 1] for an unknown θ, and the round consists of one query to the quantum reward oracle of x or its inverse. The regret after T rounds is Σ_t (max_x μ(x) − μ(x_t)).

For finite action sets the elimination algorithm of [1, Theorem 5.4] has expected regret

O(d log T · log(KT) · log(dT) · log log(dT)),

and [1] proves the lower bound Ω(d log(1 + T/d)). The factor log(KT) comes from making all K estimates accurate at once. Whether it can be lowered toward √(log K), as in the classical case, is left open in [1, Section 6].

## Result

**Theorem 1.** The elimination algorithm below has, for every finite action set A ⊂ R^d with K actions and every T ≥ 2,

E[Regret(T)] = O(d log T · log(dT) · √(log(KT))).

Compared with [1, Theorem 5.4], the factor log(KT) log log(dT) becomes √(log(KT)). The bound also lies below the bound O(d^{3/2} log^{3/2} T log(dT)) for general action sets [1], by the factor √(log(KT)/(d log T)), whenever K < T^{d−1}.

## Algorithm

The algorithm keeps the phase structure of [1]. Phase ℓ has target accuracy ε = 2^{−ℓ} and an active set A_ℓ of rank r. It computes the small-support design of [1, Lemma 5.1]: support S with |S| = O(r), weights π, and prediction weights α_a(x) with x = Σ_a α_a(x) a and Σ_a α_a(x)²/π(a) = O(r). It estimates the mean of each support action a, sets μ̃(x) = Σ_a α_a(x) μ̂_a, and drops every x with μ̃(x) < max μ̃ − 2ε.

What changes is the estimate of the support means. The algorithm uses the unbiased phase estimation of [2, Theorem 28, Section 6.3]. A uniformly random phase is added before the inverse Fourier transform, and the shortest arc containing m + 1 of 2m + 1 runs is combined into one estimate. Applied to the amplitude amplification operator of the reward oracle, this gives an estimate Y of a mean p with:

- E[Y] = p exactly;
- |Y − p| ≤ 4/M with probability at least 1 − e^{−m/4};
- |Y| ≤ 2;
- fewer than 2(2m + 1)M queries.

Here M is the register size. The correction factor λ(M, m) that makes Y unbiased depends only on M and m and is computed classically. In phase ℓ the register sizes are

M_a = max(12, ⌈c √(r π(a) ln(4K(L+1)/δ)) / ε⌉),  m = ⌈4 ln(C r T/ε)⌉,

with L = ⌈log₂ T⌉, δ = 1/T and universal constants c and C.

## Proof

*Accuracy in one phase.* Write e_a = Y_a − μ(a). The e_a are independent, E e_a = 0 and |e_a| ≤ 2. Let G_a be the event |e_a| ≤ B_a := 4/M_a, and e'_a = e_a 1_{G_a}. Then |E e'_a| ≤ 2e^{−m/4}, and on G = ∩_a G_a the error is μ̃(x) − μ(x) = Σ_a α_a(x) e'_a for every x.

- *Bias.* |Σ_a α_a(x) E e'_a| ≤ 2e^{−m/4} Σ_a |α_a(x)| ≤ 2e^{−m/4} √(C_G r) ≤ ε/8 by the choice of m.
- *Fluctuation.* The centred variables e'_a − E e'_a are independent and lie in intervals of length at most 3B_a. The concentration inequality for sums of independent bounded variables gives

  P(|Σ_a α_a(x)(e'_a − E e'_a)| > u) ≤ 2 exp(−2u² / Σ_a 9 α_a(x)² B_a²),

  and Σ_a α_a(x)² B_a² ≤ 16 ε² Σ_a α_a(x)²/(c² r π(a) ln(4K(L+1)/δ)) ≤ 16 C_G ε²/(c² ln(4K(L+1)/δ)). With u = 7ε/8, c ≥ 10√C_G and a union bound over the K actions, all K errors are below 7ε/8 except with probability δ/(2(L+1)).
- *Failure of the events G_a.* P(G^c) ≤ |S| e^{−m/4} ≤ δ/(2(L+1)).

So with probability at least 1 − δ/(L+1), |μ̃(x) − μ(x)| ≤ ε for all active x. The √(log K) appears because the union bound acts on a sum of bounded variables whose tail decays like exp(−c u²). Only the |S| = O(r) events G_a need a bound of exponential order, which costs log r, not log K.

*Queries in one phase.* Σ_a 2(2m + 1) M_a = O(m (r + c √(r ln(KT)) Σ_a √π(a) / ε)) = O(r log(dT) √(log(KT)) / ε), using Σ_a √π(a) ≤ √|S|.

*Regret.* On the event that every phase is accurate, the elimination argument of [1, Theorem 5.4] applies unchanged. The best action stays active, and every action active in phase ℓ ≥ 1 has gap at most 8ε. Phase ℓ therefore costs regret O(r log(dT) √(log(KT))). There are at most log₂ T + 1 phases, and the failure probability δ = 1/T adds at most 1 to the expected regret.

## Check

`sim/estimator.py` simulates the estimator of [2] from its exact output law, for (M, m) = (16, 12), (32, 12), (64, 16) and (128, 20). It checks unbiasedness for means from 0 to 1, the tail bound P(|Y − p| > 4/M) ≤ e^{−m/4}, the bound |Y| ≤ 2 and 1 − λ ≤ 18/M² + 2e^{−m/4}. `sim/uniform.py` runs one phase on random action sets in R^6 with K from 10 to 10⁴ and ε = 0.05, with a design of support 6 and G-value at most 12. The queries per phase grow like √(ln K): the ratio queries · ε/(d √(ln K)) stays between 150 and 152. In 200 runs for each K, no estimate μ̃(x) is off by more than ε (output in `sim/uniform_out.txt`).

## Scope

- **Assuming:** the error bound and unbiasedness of the phase estimation of [2, Theorem 28, Section 6.3], and the small-support design of [1, Lemma 5.1].
- **Not formalized:** the theorem has no Lean proof.
- The constants are universal but not explicit, as in [1].

## References

[1] M. Liu, Z. Li, J. C. S. Lui. Quantum Multi-Armed Bandits and Linear Bandits: Lower Bounds and Algorithms. arXiv:2608.14319.
[2] J. van Apeldoorn, A. Cornelissen, A. Gilyén, G. Nannicini. Quantum tomography using state-preparation unitaries. SODA 2023, arXiv:2207.08800.

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
