# Phase-space negativity and the coherent-state order-1/2 entropy: coherent states are local maximizers among pure states on every finite truncation

2026-11-25

## Problem

For a state ρ of one bosonic mode let W be its phase-space quasi-probability and Q(α) = ⟨α|ρ|α⟩/π its coherent-state function. In the units used here ∫W d²α = ∫Q d²α = 1, and a coherent state has ∫√Q d²α = 2√π. The conjecture of [1] reads

‖W‖₁ = ∫|W| d²α ≤ (∫√Q d²α)² / (4π),

with equality exactly for coherent states. In logarithmic form, the phase-space negativity ln‖W‖₁ is at most the excess of the coherent-state order-1/2 entropy 2 ln ∫√Q over its coherent-state value. In the units of [1] the constant is 8π instead of 4π. In [1] the bound is proved up to an additive ln 2, and it is shown that pure states suffice. Question (i) of [1, Sec. VII] asks whether coherent states are at least local maximizers of ‖W‖₁/(∫√Q)².

| | near a coherent state |
|---|---|
| Previous best bound [1, Prop. 2] | ‖W‖₁ ≤ (∫√Q)²/(2π) for all states |
| Theorem 1 | ‖W‖₁ < (∫√Q)²/(4π) along every direction of finite support, with the exact second-order gap t²(S/2 − 1) |
| Theorem 2 | ‖W‖₁ < (∫√Q)²/(4π) for every pure state ψ ≠ e^{iθ}|0⟩ in span{|0⟩, …, |K⟩} within a distance r_K > 0 of the vacuum |

Both sides are invariant under displacements and phase-space rotations, so the statements hold at every coherent state |β⟩ for the displaced truncations D(β) span{|0⟩, …, |K⟩}.

## Results

Write |n⟩ for the number states and, for a unit vector φ = Σ_{n≥1} φ_n|n⟩ orthogonal to |0⟩,

S(φ) = Σ_n 2^n |φ_n|²,  ψ_t = (|0⟩ + tφ)/√(1 + t²),  t > 0.

Then S(φ) ≥ 2, with equality exactly for φ = e^{iθ}|1⟩, the infinitesimal displacement.

**Theorem 1 (every direction).** Let φ have finite support. As t → 0,

- ‖W_{ψ_t}‖₁ − 1 = O(exp(−c t^{−1/K})) for some c > 0, where K is the largest n with φ_n ≠ 0;
- (∫√Q_{ψ_t})²/(4π) = 1 + t²(S(φ)/2 − 1) + O(t³);
- for φ = e^{iθ}|1⟩: (∫√Q_{ψ_t})²/(4π) ≥ 1 + t⁴/(2(1 + t²)) − O(exp(−1/(3t²))).

So the conjectured inequality holds strictly along every such direction for 0 < t < t₀(φ). Away from the displacement direction, the second-order coefficient of the gap is S(φ)/2 − 1 = Σ_{n≥2}(2^{n−1} − 1)|φ_n|², and along it the gap is of order t⁴/2.

**Theorem 2 (finite truncations).** For every K ≥ 1 there is r_K > 0 such that every unit vector ψ ∈ span{|0⟩, …, |K⟩} with ‖ψ − e^{iθ}|0⟩‖ < r_K for some θ satisfies ‖W_ψ‖₁ ≤ (∫√Q_ψ)²/(4π), with equality only for ψ = e^{iθ}|0⟩. The proof uses the quantitative form of the coherent-state entropy bound in [2, Theorem 3].

## Proof

**Negativity.** The phase-space function is W(α) = tr(ρ Ŵ(α)) with Ŵ(α) = (2/π) D(α) Π D(α)†, where Π is the parity. Since D(α)ΠD(α)†|0⟩ = |2α⟩, the cross term with the vacuum is ⟨φ|Ŵ(α)|0⟩ = (2/π)⟨φ|2α⟩. For ψ = (|0⟩ + v)/√(1 + ‖v‖²) with v ∈ span{|1⟩, …, |K⟩},

W_ψ(α) = (2/π) e^{−2|α|²} [1 + 2 Re p_v(α) + q_v(α)] / (1 + ‖v‖²),

where p_v and q_v are polynomials of degree at most K and 2K whose coefficients are bounded by C_K‖v‖ and C_K‖v‖². For ‖v‖ ≤ 1, W_ψ < 0 only where C_K‖v‖(1 + |α|)^{2K} ≥ 1/4, that is, outside a disc of radius R = (4C_K‖v‖)^{−1/(2K)} − 1. Since ∫W = 1, ‖W‖₁ = 1 + 2∫W₋, and the Gaussian tail outside that disc gives ‖W_ψ‖₁ − 1 ≤ C′_K exp(−c_K ‖v‖^{−1/K}).

**Order-1/2 side.** With F(z) = Σ_n φ_n z^n/√n!, an entire function with F(0) = 0, one has ⟨α|ψ_t⟩ = e^{−|α|²/2}(1 + tF(ᾱ))/√(1 + t²). Hence

∫√Q_{ψ_t} = I(t) / √(π(1 + t²)),  I(t) = ∫ e^{−|z|²/2} |1 + tF(z)| d²z.

For w = u + iv ∈ ℂ, | |1 + w| − (1 + u + v²/2) | ≤ 25|w|³. Indeed, for |w| ≤ 1/2 expanding the square root gives the bound 2|w|³, and for |w| > 1/2 the difference is at most 6|w| + |w|²/2 ≤ 12.5|w|² ≤ 25|w|³. The radial weight averages every entire function G to 2πG(0) times ∫e^{−r²/2} r dr. So ∫e^{−|z|²/2} F = ∫e^{−|z|²/2} F² = 0, and ∫e^{−|z|²/2}(Im F)² = (1/2)∫e^{−|z|²/2}|F|² = π S(φ), using ∫e^{−r²/2} r^{2n+1} dr = 2^n n!. Therefore

I(t) = 2π + (π/2) S(φ) t² + O(t³),  (∫√Q)²/(4π) = (1 + S t²/4 + O(t³))²/(1 + t²) = 1 + t²(S/2 − 1) + O(t³).

S ≥ 2 because φ_0 = 0, with equality only on |1⟩.

**The displacement direction.** For φ = |1⟩, F(z) = z, and the angular mean of |1 + ρe^{iθ}| is the series Σ_k ((−1/2)_k/k!)² ρ^{2k} for ρ ≤ 1. All its coefficients are positive, so it is at least 1 + ρ²/4 + ρ⁴/64. The region tr > 1 has weight O(exp(−1/(3t²))). This gives I(t) ≥ 2π(1 + t²/2 + t⁴/8) − O(exp(−1/(3t²))). Then (1 + t²/2 + t⁴/8)²/(1 + t²) ≥ 1 + t⁴/(2(1 + t²)). Directly, W_{ψ_t} ∝ e^{−2|α|²}[(1 + 2tx)² + 4t²y² − t²] with α = x + iy, which is negative only for x < −(1 − t)/(2t).

**Theorem 1.** In each case the negativity term is smaller than any power of t, while the gap of the right-hand side is of order t² or t⁴. Taking logarithms gives the logarithmic form. The strict inequality along a fixed direction also follows from Theorem 2; Theorem 1 adds the exact size of the gap.

**Theorem 2.** By [2, Theorem 3] with the convex function Φ(u) = −√u,

∫√Q_ψ ≥ 2√π (1 + c D[ψ]²/2),

where D[ψ] = 2(1 − sup_β |⟨β|ψ⟩|²)^{1/2} is the trace-norm distance to the coherent states and c > 0 is a constant of [2]. So (∫√Q_ψ)²/(4π) ≥ 1 + c D[ψ]². Let ψ = (|0⟩ + v)/√(1 + ε²) with v ∈ span{|1⟩, …, |K⟩} and ‖v‖ = ε. Then 1 − |⟨β|ψ⟩|² ≥ c_K ε^{2K+2} for every β, by cases on β:

- *|β| ≥ 1:* |⟨β|ψ⟩| ≤ e^{−1/2} + ε, so 1 − |⟨β|ψ⟩|² ≥ 1/2 for ε ≤ 0.09.
- *ε/4 ≤ |β| < 1:* ψ lies in the truncation, so 1 − |⟨β|ψ⟩|² is at least the weight e^{−|β|²}|β|^{2K+2}/(K + 1)! ≥ e^{−1}(ε/4)^{2K+2}/(K + 1)! of |β⟩ above level K.
- *|β| < ε/4:* |Σ_n β̄^n v_n/√n!| ≤ ε|β|e^{|β|²/2} by the bound on the inner product, so |⟨β|ψ⟩|² ≤ (1 + 0.6ε²)/(1 + ε²) and 1 − |⟨β|ψ⟩|² ≥ ε²/4 for ε ≤ 1/2.

With the negativity bound, ‖W_ψ‖₁ − 1 ≤ C′_K exp(−c_K ε^{−1/K}) < c c_K ε^{2K+2} ≤ c D[ψ]² for ε below some r_K. The phase of the vacuum component is removed first, and ‖ψ − e^{iθ}|0⟩‖ small gives ε small.

## Check

`sim/local.py`, output in `sim/out_local.txt`, evaluates both sides on a phase-space grid (`sim/search.py`) for the directions |1⟩, |2⟩, |3⟩, (|1⟩ + |2⟩)/√2 and (|1⟩ + i|3⟩)/√2, at t = 0.2, 0.1, 0.05 and 0.025. The gap is positive in every case, and its ratio to the predicted t²(S/2 − 1), or to t⁴/2 for |1⟩, tends to 1. At t = 0.025 the ratios lie between 0.977 and 1.004.

`sim/search.py`, output in `sim/out_search.txt`, maximizes ln‖W‖₁ − (2 ln ∫√Q − ln 4π) over pure states in span{|0⟩, …, |D − 1⟩} for D = 3, 5, 7 from 10 random starts each. The largest value found is below 1e-14, attained at states within grid accuracy of coherent states.

## Scope

- Theorems 1 and 2 are local statements: along directions of finite support, and on each finite truncation with a radius r_K that depends on K. A trace-norm neighbourhood of a coherent state in the full state space is not covered. Superpositions √(1 − p)|0⟩ + √p|β⟩ with |β| large lie in every such neighbourhood, and there both sides change at order √p.
- t₀(φ) is not uniform in φ: for φ = √(1 − δ²)|1⟩ + δ|2⟩ the t² term dominates only for t ≪ δ, and numerically the gap stays positive in between, with a dip of order t⁶ near t = √2 δ, where ψ_t is close to a coherent state.
- The constants t₀(φ) and r_K are not computed. The constant of [2] is explicit there.
- Theorem 2 rests on [2, Theorem 3], used as stated. The statements are Claims with the listed checks.

## References

1. Wigner negativity costs phase-space area: a conjectured refinement of the Lieb–Solovej inequality at Rényi order one half. arXiv:2611.30969 (2026).
2. R. L. Frank, F. Nicola, P. Tilli. The generalized Wehrl entropy bound in quantitative form. arXiv:2307.14089.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
