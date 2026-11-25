# Phase-space negativity against coherent-state entropies of order a: the bound fails for every order below 0.2887 and above 1/2

2026-11-25

## Problem

For a state ρ of one bosonic mode let W be its phase-space quasi-probability and Q(α) = ⟨α|ρ|α⟩/π its coherent-state function, so that ∫W d²α = ∫Q d²α = 1. For an order a ∈ (0, ∞], let

h_a(Q) = (1/(1 − a)) ln ∫Q^a d²α,  Δ_a(ρ) = h_a(Q) − h_a(Q_vac) ≥ 0,

with the limits h_1 = −∫Q ln Q and h_∞ = −ln max Q. Then Δ_a(ρ) = (1/(1 − a)) ln(a π^{a−1} ∫Q^a) for a ≠ 1. The conjecture of [1] is the order-1/2 inequality

ln‖W‖₁ ≤ Δ_{1/2}(ρ),  ‖W‖₁ = ∫|W| d²α,

and question (iv) of [1, Sec. VII] asks for which orders a the analogous inequality

ln‖W‖₁ ≤ Δ_a(ρ)  for all states ρ  (I_a)

can hold. In [1], (I_a) fails for a = 1, 2, ∞ at an explicit state. Two failure ranges are suggested heuristically there: every a > 1/2, from dilute superpositions, and roughly a ≲ 0.17, from large number states.

| orders a | status of (I_a) |
|---|---|
| a = 1, 2, ∞ [1] | fails at an explicit state |
| a ≲ 0.17 and a > 1/2 [1] | failure suggested heuristically |
| Theorem 1: 0 < a < a₁ = 0.288703… | fails, already at the number state |1⟩ |
| Theorem 2: every a ∈ (1/2, ∞] | fails, at superpositions of the vacuum and a distant coherent state |

So (I_a) can hold for all states only for orders a ∈ [a₁, 1/2], with a₁ = 0.2887033771….

## Results

**Theorem 1 (low orders).** Let a₁ ∈ (0, 1/2) be the unique zero of

h(a) = ln Γ(1 + a) − a ln a − (1 − a) ln(4e^{−1/2} − 1)

in (0, 1/2). Then a₁ = 0.28870337711563801763… and, for every 0 < a < a₁, the number state |1⟩ violates (I_a):

ln‖W_{|1⟩}‖₁ = ln(4e^{−1/2} − 1) = 0.354959… > Δ_a(|1⟩).

More generally, among orders a ∈ (0, 1/2], |n⟩ violates (I_a) exactly for a < a₁(n), where a₁(n) is the unique zero in (0, 1/2) of h_n(a) = ln Γ(an + 1) − a ln n! − an ln a − (1 − a) ln‖W_n‖₁.

**Theorem 2 (high orders).** For every a ∈ (1/2, ∞] there are t > 0 and β > 0 such that ψ = (|0⟩ + t|β⟩)/‖|0⟩ + t|β⟩‖ violates (I_a). As β → ∞,

- ‖W_ψ‖₁ → 1 + 4t/(π(1 + t²));
- Δ_a(ψ) → D_a(t) = (1/(1 − a)) ln((1 + t^{2a})/(1 + t²)^a) for a ≠ 1, the binary entropy of t²/(1 + t²) for a = 1, and ln(1 + t²) for a = ∞.

As t → 0, ln(1 + 4t/(π(1 + t²))) ∼ 4t/π, while D_a(t) is of order t^{2a} for 1/2 < a < 1, t² ln(1/t) for a = 1 and t² for a > 1, all o(t). At a = 1/2 the limit is D_{1/2}(t) = 2 ln((1 + t)/√(1 + t²)) ∼ 2t > 4t/π, so this family does not violate the order-1/2 inequality, in line with the conjecture of [1].

## Proof

**Number states.** W_n(α) = (2/π)(−1)^n e^{−2|α|²} L_n(4|α|²) and Q_n(α) = e^{−|α|²}|α|^{2n}/(π n!). Hence ‖W_n‖₁ = (1/2)∫₀^∞ e^{−x/2}|L_n(x)| dx, with ‖W_1‖₁ = (1/2)∫₀^∞ e^{−x/2}|1 − x| dx = 4e^{−1/2} − 1, and

∫Q_n^a = π^{1−a} Γ(an + 1)/((n!)^a a^{an+1}),  (1 − a)Δ_a(|n⟩) = ln Γ(an + 1) − a ln n! − an ln a.

So, for 0 < a < 1, (I_a) fails at |n⟩ exactly when h_n(a) < 0.

**Concavity.** h_n''(a) = n²ψ′(an + 1) − n/a, where ψ′ is the trigamma function. From ψ′(z) = Σ_{k≥0}(z + k)^{−2} < z^{−2} + ∫₀^∞(z + s)^{−2} ds = z^{−2} + z^{−1} and ψ′(z + 1) = ψ′(z) − z^{−2}, one gets ψ′(an + 1) < 1/(an), so h_n'' < 0 on (0, 1).

**Theorem 1.** h_n is concave with h_n(0+) = −ln‖W_n‖₁ < 0 and h_n(1/2) > 0, which holds for n = 1 (h(1/2) = 0.0483) and is checked numerically for the other listed n. So h_n has exactly one zero a₁(n) in (0, 1/2), with h_n'(a₁(n)) > 0. Concavity puts h_n below its tangent at a₁(n), so h_n < 0 on (0, a₁(n)). For n = 1, a₁ = 0.288703377… and h'(a₁) = 0.41523…, evaluated with 40 significant digits.

**Theorem 2, negativity.** Take β > 0 real and N² = 1 + t² + 2te^{−β²/2}. Then

N² W_ψ = W_0 + t² W_β + 2t Re X,  X(α) = ⟨β|Ŵ(α)|0⟩ = (2/π)⟨β|2α⟩ = (2/π) e^{−|2α − β|²/2} e^{2iβ Im α},

where W_0 and W_β are positive Gaussians of mass 1, centred at 0 and β. Let R be the disc of radius β/4 about β/2. Then

N²‖W_ψ‖₁ ≥ ∫_{R^c}(W_0 + t²W_β) − ∫_R (W_0 + t²W_β) + 2t∫_R |Re X| − 2t∫_{R^c}|X|.

As β → ∞ the first term tends to 1 + t² and the second and fourth tend to 0, by Gaussian tails. In the third, |Re X| = (2/π)e^{−|2α − β|²/2}|cos(2β Im α)|, and since |cos| has mean 2/π over a period, the integral tends to (2/π)∫X̃ = 2/π, where X̃ = (2/π)e^{−|2α−β|²/2} has mass 1. So liminf ‖W_ψ‖₁ ≥ 1 + 4t/(π(1 + t²)). The triangle inequality gives the matching upper bound.

**Theorem 2, entropies.** ⟨α|ψ⟩ = (u(α) + t v(α))/N with |u| = e^{−|α|²/2} and |v| = e^{−|α − β|²/2}. On the half-plane Re α < β/2, |v| tends to 0 with Gaussian domination, and symmetrically for u on the other half. Dominated convergence therefore gives ∫Q^a → π^{1−a}(1 + t^{2a})/(a(1 + t²)^a) for every finite a ≠ 1, the analogous limit of ∫Q ln Q, and max Q → 1/(π(1 + t²)) for t ≤ 1. This gives D_a(t).

**Conclusion.** For a > 1/2, choose t with ln(1 + 4t/(π(1 + t²))) > D_a(t), which is possible since D_a(t) = o(t). By the two limits, ψ violates (I_a) for all large β.

## Check

- `sim/threshold.py`, output in `sim/out_threshold.txt`, computes a₁ and h′(a₁) with 40 digits. It also checks ‖W_1‖₁ by quadrature and the sign of h at 288 points of (0, a₁) and at 0.2888.
- `sim/fockthr.py`, output in `sim/out_fockthr.txt`, computes ‖W_n‖₁ for n up to 3200 from the stable recurrence of the Laguerre functions (`sim/fockl1.py`).
  - The thresholds a₁(n) decrease with n: 0.2887 at n = 1, 0.1872 at n = 100, 0.1726 at n = 3200.
  - ln‖W_n‖₁ − (1/2) ln n approaches c = ln((2/π)^{3/2}Γ(3/4)²/Γ(3/2)) = −0.1500, the value of a semiclassical approximation, at rate n^{−1/2}.
  - With this c, a₁(n) tends to the limit 0.1693, the threshold suggested in [1].
- `sim/upper.py`, output in `sim/out_upper.txt`, finds t with a violation in the limit for a = 0.55, 0.6, 0.75, 1, 2, ∞.
  - It checks the limits on a grid at finite β. At t = 0.2, β = 3√2 it reproduces the values of [1].
  - At t = 0.05, β = 7 it gives ln‖W‖₁ = 0.0615 > Δ_{0.75} = 0.0370, an explicit violation at order 3/4.
- `sim/order.py`, output in `sim/out_order.txt`, maximizes ln‖W‖₁ − Δ_a over pure states in span{|0⟩, …, |3⟩} from random starts. The maximum is found at |1⟩ for a = 0.25 and 0.29. For a = 0.32 and 0.36 no state beats the vacuum.

## Scope

- Theorems 1 and 2 leave the orders a ∈ [a₁, 1/2) open. The numerical maximization covers pure states in span{|0⟩, …, |3⟩} on a grid with accuracy about 5·10⁻⁴.
- The limit of ln‖W_n‖₁ − (1/2) ln n is numerical, and Theorem 1 does not use it.
- The statements are Claims with the listed checks.

## References

1. Wigner negativity costs phase-space area: a conjectured refinement of the Lieb–Solovej inequality at Rényi order one half. arXiv:2611.30969 (2026).

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
