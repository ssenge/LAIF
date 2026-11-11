# Low-regret tomography of pure qudit states: the dimension factor is d²

Written 11 Nov 2026.

## Problem

This is the model of [1]. An unknown pure state ψ ∈ C^d arrives as copies, one per round. In round t the learner picks a unit vector φ_t, which may depend on all earlier outcomes and on internal randomness. It measures the copy with the two-outcome projective measurement {|φ_t⟩⟨φ_t|, 1 − |φ_t⟩⟨φ_t|} and sees the outcome. The regret after T rounds is

Regret(T) = Σ_{t ≤ T} (1 − |⟨φ_t|ψ⟩|²),

the summed infidelity between the measured direction and the state, which also controls the disturbance of the measured copies [1, 2]. For qubits the regret can be kept polylogarithmic in T [2]. For every d, [1] gives an algorithm with E[Regret(T)] = O(d³ log² T) and asks for the optimal dependence on d. The lower bound it points to is Ω(d log(T/d)) from [2], which holds for arbitrary measurements, even collective ones.

## Results

**Theorem 1 (lower bound).** Let d ≥ 2 and T ≥ 1. There is a prior on pure states under which every learner in the model above has

E[Regret(T)] ≥ 0.4 (d − 1)² ln(1 + T / (4π² (d − 1)²)).

So sup_ψ E[Regret(T)] = Ω(d² log(T/d²)). By the same argument, any estimate built from t such measurements has average infidelity at least 0.4 · 4(d − 1)² / (4t + 16π²(d − 1)²), which is Ω(d²/t) for t ≥ d².

**Theorem 2 (algorithm).** The epoch algorithm below has, for every pure state ψ ∈ C^d, d ≥ 2 and T ≥ 2,

E[Regret(T)] ≤ 10⁵ d² ln T + 10⁴ d ln² T.

Let W ≤ 10⁵ d² ln T be the length of its warm-up. With probability at least 1 − 1/T, at every round t ≥ 2W its current base vector has infidelity at most 16(d − 1)(458(d − 1) + 71x)/t = O((d² + d log T)/t) with the state, where x ≤ 3 ln T is defined below. In expectation the same holds with 1/t added, for 2W ≤ t ≤ T. The online infidelity of [1] is O(d³ log T / t) in expectation.

**Theorem 3 (budgeted phases).** A variant of the epoch algorithm, in which each phase stops once it has seen a fixed number of outcomes 0, has, for every pure state ψ ∈ C^d, d ≥ 2 and 2 ≤ T ≤ 2^(10^50),

E[Regret(T)] ≤ 1420 d² ln T + 6000 d².

So in this model the regret is Θ(d² log T) for all T ≥ d³ (in this range of T), with constants about 3600 apart for large T. Previous best bounds: O(d³ log² T) [1] and Ω(d log(T/d)) [2]. In particular, with two-outcome measurements onto one vector, the regret of order d log T and the online infidelity of order d/t up to logarithms, hoped for in [1, Section 7], are out of reach; they would need richer measurements.

## Proof of Theorem 1

Write a ∈ C^{d−1} for the chart u_a = (1, a)/√(1 + |a|²), and θ ∈ R^m, m = 2(d − 1), for the real and imaginary parts of a.

**Lemma 1 (chart).** 1 − |⟨u_a|u_b⟩|² ≥ |a − b|² / ((1 + |a|²)(1 + |b|²)).

*Proof.* With v_a = (1, a), the numerator of 1 − |⟨u_a|u_b⟩|² over the common denominator (1 + |a|²)(1 + |b|²) is (1 + |a|²)(1 + |b|²) − |1 + ⟨a, b⟩|² = |a − b|² + (|a|²|b|² − |⟨a, b⟩|²), and the last bracket is nonnegative. ∎

**Lemma 2 (information of one measurement).** For a fixed unit vector φ let q(θ) = |⟨φ|u_a⟩|². Then |∇_θ q|² ≤ 4q(1 − q). So the information matrix of one outcome, ∇q ∇qᵀ / (q(1 − q)), has trace at most 4.

*Proof.* Let ψ = u_a and take a direction θ̇ with derivative ψ̇. Since |ψ| = 1, ψ̇ = iλψ + v with λ real and v ⊥ ψ. The derivative of q is 2 Re(conj⟨φ|ψ⟩ ⟨φ|ψ̇⟩). The term iλψ contributes 2 Re(iλ q) = 0, and |⟨φ|v⟩| ≤ |P_{ψ⊥}φ| · |v| = √(1 − q) |v|. So the derivative is at most 2√(q(1 − q)) |v| in absolute value. In the chart, |v|² = (|ȧ|²(1 + |a|²) − |⟨a, ȧ⟩|²)/(1 + |a|²)² ≤ |θ̇|². ∎

*Proof of Theorem 1.* Let h = 1/(2√m) and put on θ the product prior with density h^{−1} cos²(πθᵢ/(2h)) on [−h, h] in each coordinate. Then |θ| ≤ 1/2, and the prior's information matrix is (π²/h²) I, with trace J = 4π² m². The outcomes before round t come from t − 1 measurements, each chosen from the past. So the information matrix of these outcomes about θ is a sum of t − 1 expected one-step matrices, and by Lemma 2 its trace is at most 4(t − 1) at every θ. The Bayesian information inequality in matrix form [3] gives E[(θ̂ − θ)(θ̂ − θ)ᵀ] ⪰ (Ī + J_π)^{−1} for every estimator θ̂ of the data, where Ī is the prior average of the information matrix and J_π the prior's information matrix. Taking traces, and using tr(M^{−1}) ≥ m²/tr(M) for positive definite M,

E|θ̂ − θ|² ≥ m² / (4(t − 1) + 4π² m²).

Turn φ_t into an estimator: if φ_t = c(1, a) with |a| ≤ 1, set θ̂_t = a; otherwise θ̂_t = 0. Then 1 − |⟨φ_t|ψ⟩|² ≥ 0.4 |θ̂_t − θ|². For |a| ≤ 1 this is Lemma 1 with |θ| ≤ 1/2. For |a| > 1, Lemma 1 gives at least (|a| − 1/2)²/(1.25(1 + |a|²)) ≥ 0.1 ≥ 0.4 |θ|², since this fraction increases in |a| ≥ 1. If φ_t has first coordinate 0, the infidelity is 1/(1 + |θ|²) ≥ 0.8. Summing over t, and comparing the sum with an integral,

E[Regret(T)] ≥ 0.4 Σ_{t=0}^{T−1} m² / (4t + 4π² m²) ≥ 0.1 m² ln(1 + T/(π² m²)),

which is the bound. The estimate after t measurements is covered by the same display with t − 1 replaced by t. ∎

## The algorithm

Parameters: x = ln(T(log₂ T + 2)), ε₀ = 1/16, r = arcsin(1/4)/3, N₂ = 750d, L = ⌈8.1x⌉, and in epoch m, ε_m = ε₀ 2^{−m} and N_m = ⌈(458(d − 1) + 71x)/ε_m⌉. Every measurement is a projector onto one vector, and the algorithm stops when T copies are used.

**Warm-up run.** (a) Repeat up to 8d times: pick j uniformly and measure one copy with |j⟩. Stop at the first outcome 1. The accepted j has probability p_j = |ψ_j|². (b) Measure N₂ copies with |j⟩, and N₂ copies with each (|j⟩ + e^{iη}|l⟩)/√2 for l ≠ j and η ∈ {0, π/2, π, 3π/2}. With q̂ the observed frequencies, set ẑ_j = q̂(|j⟩) and ẑ_l = (q̂_0 − q̂_π)/2 + i(q̂_{π/2} − q̂_{3π/2})/2. The candidate is ẑ/|ẑ|.

**Warm-up.** Do L runs. Let ∠(a, b) = arccos|⟨a|b⟩|, a metric on pure states. Choose a candidate that has more than L/2 candidates within angle 2r. This is the first base vector c₀.

**Epoch m.** Let c = c_m and s = √ε_m. Take an orthonormal basis w_1, …, w_{d−1} of the complement of c and the 2(d − 1) directions u ∈ {w_j, i w_j}. For each u, measure N_m copies with cos s · c + sin s · u and N_m copies with cos s · c − sin s · u. With observed frequencies q̂₊ and q̂₋, let ŷ_u = (q̂₊ − q̂₋)/(2 sin 2s) and x̂ = Σ_j (ŷ_{w_j} + i ŷ_{i w_j}) w_j. The next base vector is c_{m+1} = (c + x̂)/|c + x̂|.

## Proof of Theorem 2

Fix ψ and write α = ⟨c|ψ⟩, β = ψ − αc, D = 1 − |α|² = |β|² for the infidelity of the base vector c.

**Lemma 3 (exact linear model).** For a unit vector u ⊥ c, q± = |⟨cos s · c ± sin s · u|ψ⟩|² satisfies q₊ − q₋ = 2 sin 2s · Re⟨u|ξ⟩ with ξ = conj(α) β. So E ŷ_u = Re⟨u|ξ⟩, and E x̂ = ξ.

*Proof.* ⟨cos s · c ± sin s · u|ψ⟩ = A ± B with A = α cos s and B = ⟨u|β⟩ sin s, and |A + B|² − |A − B|² = 4 Re(conj(A)B). For u = i w, Re⟨iw|ξ⟩ = Im⟨w|ξ⟩. ∎

**Lemma 4 (update).** If y ⊥ c and D < 1, the infidelity of (c + y)/|c + y| with ψ is at most |y − β/α|².

*Proof.* c + β/α = ψ/α, so c + y = ψ/α + (y − β/α). The part orthogonal to ψ has norm at most |y − β/α|, and |c + y|² = 1 + |y|² ≥ 1. ∎

Since ξ − β/α = β(|α|² − 1)/α, we have |ξ − β/α|² = D³/(1 − D).

**Lemma 5 (concentration).** Let Y_1, …, Y_M be independent with E e^{λY_i} ≤ e^{μλ²} for |λ| ≤ 1. If μ ≥ M ln 5 + x, then |Y|² ≤ 16μ(M ln 5 + x) with probability at least 1 − e^{−x}.

*Proof.* For a unit vector w, E e^{λ⟨w, Y⟩} ≤ e^{μλ²} for |λ| ≤ 1, so P(⟨w, Y⟩ > y) ≤ e^{−y²/(4μ)} for y ≤ 2μ. Take a 1/2-net of the unit sphere with at most 5^M points, so that |Y| ≤ 2 max over the net of ⟨w, Y⟩ [4, Sections 4.2 and 4.4], and y² = 4μ(M ln 5 + x) ≤ 4μ². A union bound over the net finishes the proof. ∎

A centred binomial Y = X − Np with X ~ Bin(N, p) satisfies E e^{λY} ≤ exp(Np(e^λ − 1 − λ)) ≤ e^{Npλ²} for |λ| ≤ 1, since e^λ − 1 − λ ≤ (e − 2)λ² there.

**One epoch.** Suppose D_m ≤ ε_m = ε ≤ 1/16.

- *Regret.* The angle from ψ to each measured vector is at most s + arcsin √D ≤ 2.011 √ε, so each copy costs at most κε with κ = 4.05.
- *Estimate.* Apply Lemma 5 to the counts of outcome 0 at the M = 4(d − 1) measured vectors: each has p ≤ κε, so μ = κεN_m ≥ M ln 5 + x. The error x̂ − ξ is (2 sin 2s)^{−1} N_m^{−1} times a ±1 combination of pairs of these Y, so |x̂ − ξ|² ≤ 2 (2 sin 2s)^{−2} N_m^{−2} |Y|². With sin 2s ≥ 2s · 23/24 for s ≤ 1/4 this gives, with probability at least 1 − e^{−x}, |x̂ − ξ|² ≤ 8.82(M ln 5 + x)/N_m ≤ ε/8.
- *Contraction.* By Lemma 4, D_{m+1} ≤ 2|x̂ − ξ|² + 2D³/(1 − D) ≤ ε/4 + 2ε³/(1 − ε) ≤ ε/2 = ε_{m+1}.

So the epoch keeps D_m ≤ ε_m with probability at least 1 − e^{−x}, and costs at most 4κ(d − 1)N_m ε ≤ 7420(d − 1)² + 1151(d − 1)x + 1.02(d − 1).

**One warm-up run** ends within angle r of ψ with probability at least 3/4. The rejection step fails with probability at most (1 − 1/d)^{8d} ≤ e^{−8}. Given j, write p* = p_j. Then z = conj(ψ_j) ψ has |z|² = p* and E ẑ = z, because the four phases cancel the cross terms. Each frequency has variance at most q/N₂, and the four probabilities for l sum to 2(p* + p_l). So E|ẑ − z|² ≤ ((d + 1)p* + 1)/(2N₂), and sin²∠(ẑ, z) ≤ |ẑ − z|²/|z|². Since E[1/p*] = Σ_j p_j/p_j ≤ d, the mean of sin²∠ is at most (2d + 1)/(2N₂). A run with ẑ = 0 counts as failed. By the first-moment bound, P(sin²∠ > sin² r) is at most this mean divided by sin² r. With N₂ = 750d and the rejection step, a run fails with probability at most 0.236.

**Warm-up.** If more than L/2 runs succeed, every chosen candidate lies within 2r of a successful one, so ∠(c₀, ψ) ≤ 3r and D₀ ≤ sin²(3r) = 1/16. By the exponential bound for sums of independent indicators, at least L/2 runs fail with probability at most e^{−2L(1/2 − 0.236)²} ≤ e^{−x}. If no candidate passes the majority test, which happens only then, take c₀ = |1⟩. One run uses at most 8d + N₂ + 4(d − 1)N₂ ≤ 3000d² copies.

**Total.** Epoch m needs at least 4 · 458 · 16 · 2^m copies, so at most log₂ T + 1 epochs start. By a union bound, the warm-up and all epochs succeed with probability at least 1 − (log₂ T + 2)e^{−x} = 1 − 1/T. On the remaining event the regret is at most T, which adds at most 1. With x ≤ 3 ln T, the warm-up costs at most (8.1x + 1) · 3000d² and the epochs at most (log₂ T + 1)(7420(d − 1)² + 1151(d − 1)x + 1.02(d − 1)). Together this is at most 10⁵ d² ln T + 10⁴ d ln² T. For the second claim, write P = 458(d − 1) + 71x and let t ≥ 2W lie in epoch m. Then t ≤ W + 4(d − 1)Σ_{k≤m} N_k, and ε_m Σ_{k≤m} N_k ≤ Σ_{k≤m} (P 2^{k−m} + ε_m) ≤ 2P, because (m + 1)ε_m ≤ 1/16 ≤ P 2^{−m}. With t − W ≥ t/2 this gives t/2 ≤ 8(d − 1)P/ε_m, so D_m ≤ ε_m ≤ 16(d − 1)P/t on the good event. The expected infidelity adds at most P(bad event) ≤ 1/T ≤ 1/t. ∎

## Budgeted phases and proof of Theorem 3

**The algorithm.** Let ε₀ = 1/128 and, for levels ℓ ≥ 0, ε_ℓ = 2^{−ℓ} ε₀, N_ℓ = ⌈40d/ε_ℓ⌉, n_ℓ = 4(d − 1)N_ℓ and B_ℓ = ⌈3.5 ε_ℓ n_ℓ⌉. A *warm-up* is one warm-up run with N₂ = 500d; if its rejection step fails or ẑ = 0, the base vector is |1⟩. The algorithm starts with a warm-up and then runs phases.

A *phase* at level ℓ with base vector c measures the same 4(d − 1) vectors as an epoch with ε = ε_ℓ and N = N_ℓ, but the two vectors cos s · c ± sin s · u of a pair alternate, one copy each, and the phase counts the outcomes 0.

- If the count reaches B_ℓ, after n′ copies of the phase, the phase *aborts*. Let ρ̂ = B_ℓ/n′. The new level is the largest k ≤ ℓ with ε_k ≥ 2ρ̂; if there is none, the next step is a warm-up. The base vector is kept.
- Otherwise the phase *completes*: c is updated as in an epoch, and the level becomes ℓ + 1.

**Regret is counted by outcomes 0.** Given the past, the round t outcome is 0 with probability 1 − |⟨φ_t|ψ⟩|². So E[Regret(T)] is the expected number of outcomes 0. A phase sees at most B_ℓ ≤ 560.4 d² of them, and a warm-up uses at most 8d + N₂(4d − 3) ≤ 2003 d² copies.

**Zero rates.** For a pair, (q₊ + q₋)/2 = cos²s (1 − D) + sin²s |⟨u|β⟩|² with |⟨u|β⟩|² ≤ D. So the average probability p̄ of outcome 0 over the two vectors satisfies λ(ε + D) ≤ p̄ ≤ ε + D, with λ = 1 − 2ε₀, for every u.

**Potential.** At the start of a phase at level ℓ, let g = log₂(D/ε_ℓ) if D > ε_ℓ and g = 0 otherwise, and Ψ = ℓ − 10g. Before a warm-up, Ψ = −4. Give a phase weight 1 and a warm-up weight 4.

**Lemma 6 (drift).** Let η = 0.5695. For every state with ℓ ≤ 10^50, the next phase or warm-up increases E Ψ by at least η times its weight.

*Proof.* Write ε = ε_ℓ, r = (ε + D)/ε, and note that εn_ℓ ≥ 4 · 40 · d(d − 1) ≥ 320 and B_ℓ ≥ 1120.

- *Completed phase.* If the phase starts with r ≤ r̄, Lemma 4 gives D′ ≤ 2|x̂ − ξ|² + 2D³/(1 − D). Summing the variances of the frequencies with the zero rates above gives E|x̂ − ξ|² ≤ rε/(160(1 − 2ε₀/3)²). With log₂ y ≤ y/(e ln 2) for y > 0, E[g′; completed] ≤ (4 · 0.2526 r̄/40 + 4K³ε₀²/(1 − Kε₀))/(e ln 2) with K = r̄ − 1.
- *Aborted phase.* Since ρ̂ ≥ B_ℓ/n_ℓ ≥ 3.5ε, the new level is at most ℓ − 3, and its ε_k is below 4ρ̂ (or a warm-up follows with ε₀ < 2ρ̂). With R = log₂(ρ̂/(ε + D)), Ψ drops by at most g + 6 + R in levels, and the new gap is at most (−1 − R)₊ because ε_k ≥ 2ρ̂. R ≥ k ≥ 1 needs B_ℓ outcomes 0 among the first B_ℓ 2^{−k}/(ε + D) copies, and −1 − R > k needs fewer than B_ℓ among the first B_ℓ 2^{k+1}/(ε + D). The two exponential bounds for sums of independent indicators give Σ_{k≥1} P(R ≥ k) ≤ 10^{−90} and Σ_{k≥0} P(−1 − R > k) ≤ 10^{−110}.
- *r ≤ 3.043*, i.e. D ≤ 2.043ε. The expected number of outcomes 0 of the whole phase is at most B_ℓ/1.15, so the phase aborts with probability at most 4 · 10^{−5}. The gain is at least 1 − 10 E[g′; completed] − (small terms) ≥ 0.580.
- *r > 3.043*, so g ≥ 1.031. A completed phase gains 1 + 10g − 10g′, and an aborted one gains at least 9g − 6 − R − 10(−1 − R)₊ ≥ 3.28 − R − 10(−1 − R)₊. For r ≤ 5.694 the bound on E[g′; completed] applies with r̄ = 5.694. For r > 5.694 the expected number of outcomes 0 of the whole phase is at least 1.6 B_ℓ, so the phase completes with probability at most 1.7 · 10^{−55}, and then g′ ≤ ℓ + 8. Together the gain is at least 1.377 − 0.25.
- *Warm-up.* After a warm-up, g₀ ≤ log₂(1/ε₀) = 7 always, and when its rejection step succeeds, E D₀ ≤ (2d + 1)/(2N₂) ≤ 1.25/500 as in the warm-up analysis above. So E g₀ ≤ 128 · 1.25/500/(e ln 2) + 7e^{−8}, and the gain 4 − 10 E g₀ is at least 4η. ∎

*Proof of Theorem 3.* Run the algorithm with unlimited copies and stop it at the first phase or warm-up that would need copy T + 1. A completed phase at level ℓ uses n_ℓ ≥ 512 · 40 · d(d − 1) · 2^ℓ copies, so every level reached before that point is at most log₂ T − 14, and Ψ ≤ max(0, log₂ T − 14) there. By Lemma 6 and optional stopping, the expected total weight of the phases and warm-ups before the last one is at most (max(0, log₂ T − 14) + 4)/η. Each unit of weight costs at most 560.4 d² outcomes 0, and the last step at most 2003 d². This gives E[Regret(T)] ≤ 983.8 d² (max(0, log₂ T − 14) + 4) + 2003 d² ≤ 1420 d² ln T + 6000 d². ∎

## Check

`python sim/checks.py` tests Lemma 2 at random charts and vectors, and Lemmas 3 and 4 on random instances. `python sim/consts.py` recomputes the constants above with asserts, including the online constant 16 and the bound on W. `python sim/regret.py 2,4,8 1e4,1e5,1e6 10` runs the algorithm with small constants. `python sim/regret.py 2,3,4,8 1e8,1e10,1e12 10 proof` runs it with the constants of the proof and asserts D_m ≤ ε_m in every epoch of every run. All three need numpy and take a few seconds. Their output is in `sim/out.txt`. For Theorem 3, `python sim/consts2.py` checks every inequality of Lemma 6 and the totals with asserts, and `python sim/regret2.py 2,3,4,8,16 1e8,1e12,1e16 10 proof` runs the budgeted algorithm with the constants of the proof; its regret stays below 180 d² ln T in these runs.

In the runs with small constants, the regret divided by d² ln T stays between 10 and 18 for d = 2, 4, 8 and T up to 10⁶.

## Scope

- Claim with written proofs, not formalized. The constants are not optimized.
- Theorem 2 gives high-probability guarantees and the online infidelity; Theorem 3 bounds the expected regret without the term d ln² T. Theorem 3 is stated for T ≤ 2^(10^50); the bound on the rare completions from a far state uses ℓ ≤ 10^50.
- Theorem 1 is for single copies and two-outcome measurements onto one vector, the model of [1]. For general measurements and for collective measurements, [2] gives Ω(d log(T/d)). Related lower bounds for tomography with few-outcome measurements are in [5, 6]; for rank one, [5] gives Ω(d²/ε²) copies for trace distance ε, so Ω(d²/δ) for infidelity δ, with nonadaptive constant-outcome measurements, the nonadaptive counterpart of the estimation bound in Theorem 1.

## References

1. J. Lumbreras, M. Tomamichel. Learning pure quantum states in any dimension (almost) without regret. arXiv:2605.09019 (2026).
2. J. Lumbreras, M. Terekhov, M. Tomamichel. Learning pure quantum states (almost) without regret. arXiv:2406.18370 (2024).
3. R. D. Gill, B. Y. Levit. Applications of the van Trees inequality: a Bayesian Cramér-Rao bound. Bernoulli 1 (1995), 59-79.
4. R. Vershynin. High-Dimensional Probability. Cambridge University Press (2018).
5. A. Lowe, A. Nayak. Lower bounds for learning quantum states with single-copy measurements. ACM Trans. Comput. Theory 17(1) (2025). arXiv:2207.14438.
6. J. Acharya, A. Dharmavarapu, Y. Liu, N. Yu. Pauli measurements are not optimal for single-copy tomography. arXiv:2502.18170 (2025).
