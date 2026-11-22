# Forward-only Hamiltonian state distinguishing with a minimum evolution duration

2026-11-22

## Problem

Let H ∈ ℂ^{d×d}, d ≥ 2, be an unknown Hamiltonian with ‖H‖ ≤ 1. An algorithm may apply e^{−iHt} to a register for any duration t ≥ τ of its choice. It cannot apply inverse or controlled evolutions, and each application costs t. Between applications it may use any operations that do not depend on H: unitaries, measurements, ancillas and adaptive classical control. Exactly one of the following holds, and ε ∈ (0, 1] is known:

YES: H|0⟩ = 0,  NO: H|0⟩ = ε|1⟩.

The algorithm must name the case correctly with probability at least 1 − δ in both cases. Its cost is the total evolution time. For τ → 0 this is Problem 2 of [1], which needs Θ(1/ε) total evolution time [1, Theorem 1.2]. The algorithm of [1] uses evolution steps whose length goes to 0, interleaved with projections onto span{|0⟩, |1⟩}, and then learns a 2 × 2 unitary. In [1, Section 1.3] it is asked how a prescribed minimum evolution duration would affect this, and in particular how long the intermediate evolution times can be while keeping O(1/ε) scaling.

| | total evolution time (constant δ) |
|---|---|
| Previous best bound, τ → 0 | Θ(1/ε) [1] |
| Previous lower bound, every τ | Ω(1/ε) [1, Section 2] |
| Theorem 1 (every 0 < τ ≤ 1, d ≥ 2) | O(max{1/ε, τ/ε²}), one-sided error |

In particular, every minimum duration τ ≤ ε keeps the optimal Θ(1/ε) total evolution time. The bound does not depend on the dimension d.

## Results

**Algorithm.** Let Π be the projector onto span{|0⟩, |1⟩}, let X_Π = |0⟩⟨1| + |1⟩⟨0| + (I − Π), and let s = τ. A step applies e^{−iHs}, measures {Π, I − Π}, and applies X_Π if the outcome is Π. A run prepares |0⟩ and performs 2m steps, where

m = max{1, ⌊min{1/(4εs), 1/(8s²)}⌋}.

The run stops early if an outcome I − Π occurs. Otherwise it ends with a measurement in {|0⟩, |1⟩}. The algorithm answers NO if some run ends with outcome |1⟩, and YES otherwise. For τ ∈ (1/2, 1] a run is instead a single application of e^{−iHτ} to |0⟩ followed by a measurement of {|0⟩⟨0|, I − |0⟩⟨0|}, and NO is answered if some run gives the second outcome.

**Theorem 1.** Let 0 < ε ≤ 1, 0 < τ ≤ 1 and 0 < δ < 1. In the YES case the algorithm never answers NO. In the NO case each run ends with the detection outcome with probability at least P, where the run time t satisfies

t / P ≤ 46 max{1/ε, τ/ε²}.

So R = ⌈ln(1/δ)/P⌉ runs give error at most δ, with total evolution time at most 46 (1 + ln(1/δ)) max{1/ε, τ/ε²}. Every application of e^{−iHt} has duration exactly τ, and the algorithm uses no ancilla.

## Proof

**One step as a matrix.** On span{|0⟩, |1⟩} the outcome Π of a step has Kraus operator A = Π e^{−iHs} Π, written as the 2 × 2 matrix with entries A_{jk} = ⟨j|e^{−iHs}|k⟩. A run that never sees I − Π applies the 2 × 2 matrix C^m with C = X A X A, so it ends with |1⟩ with probability |⟨1|C^m|0⟩|².

**YES case.** H|0⟩ = 0 gives e^{−iHs}|0⟩ = |0⟩, and ⟨0|e^{−iHs}|1⟩ = ⟨e^{iHs}0|1⟩ = 0. So A = diag(1, δ₁) with δ₁ = ⟨1|e^{−iHs}|1⟩, and C = X A X A = δ₁ I. The state stays a multiple of |0⟩, and outcome |1⟩ never occurs.

**NO case, entries of A.** Write α = A₀₀, β = A₁₀ and δ₁ = A₁₁. From H|0⟩ = ε|1⟩,

e^{−iHs}|0⟩ = |0⟩ + ε f(H)|1⟩,  f(x) = (e^{−isx} − 1)/x,

so β = ε⟨1|f(H)|1⟩. The same expansion of ⟨1|e^{iHs}|0⟩ gives A₀₁ = β. Let ν and μ be the spectral measures of |1⟩ and |0⟩ for H, supported in [−1, 1]. Then:

- f(x) = −is e^{−isx/2} sin(sx/2)/(sx/2), so |β| ≥ ε s ∫ sin(sx)/(sx) dν(x) ≥ ε sin s, and |β| ≤ εs.
- μ has mean ⟨0|H|0⟩ = 0 and second moment ‖H|0⟩‖² = ε², so |α − 1| ≤ ε²s²/2.
- ν has variance at most 1, so |δ₁| ≥ ∫ cos(s(x − x̄)) dν ≥ 1 − s²/2.

**NO case, exact amplitude.** Multiplying out,

C = [[αδ₁ + β², 2βδ₁], [2αβ, αδ₁ + β²]] = p I + N,  p = αδ₁ + β²,  N² = q² I,  q = 2β√(αδ₁).

Hence

⟨1|C^m|0⟩ = 2αβ p^{m−1} F_m(q/p),  F_m(x) = ((1 + x)^m − (1 − x)^m)/(2x) = Σ_{k odd} C(m, k) x^{k−1},

for either square root. If y = m|q/p| ≤ 1, then |F_m(x) − m| ≤ m Σ_{j ≥ 1} y^{2j}/(2j + 1)! = m(sinh(y)/y − 1), so |F_m| ≥ m(2 − sinh 1) ≥ 0.824 m.

**Constants for 0 < s ≤ 1/2.** From the entry bounds, |p| ≥ 1 − 2s² ≥ 1/2 and |q| ≤ 2εs. Let M = min{1/(4εs), 1/(8s²)}.

- If M ≥ 1, then M/2 ≤ m ≤ M and y ≤ 2Mεs/(1 − 2s²) ≤ 1. Also (1 − 2s²)^{m−1} ≥ e^{−4ms²} ≥ e^{−1/2}, |α| ≥ 7/8 and |β| ≥ 0.958 εs. So the amplitude is at least 0.837 εsm and P ≥ 0.70 (εsm)². The run time is t = 2ms, so t/P ≤ 2.86/(ε² s m) ≤ 5.72/(ε² s M) = 5.72 max{4/ε, 8s/ε²} ≤ 46 max{1/ε, s/ε²}.
- If M < 1, then m = 1 and the amplitude is exactly 2|αβ| ≥ 1.67 εs. Then t/P ≤ 0.72/(ε² s), and either 1/s < 4ε or 1/s² < 8. Both give t/P ≤ 5.8 max{1/ε, s/ε²}.

**The case 1/2 < τ ≤ 1.** One application of e^{−iHτ} to |0⟩ leaves |0⟩ with probability 1 − |∫e^{−ixτ} dμ|² = ∫∫ (1 − cos((x − x')τ)) dμ dμ'. Since |x − x'|τ ≤ 2 and (1 − cos u)/u² ≥ (1 − cos 2)/4 on [0, 2], this is at least 0.708 ε²τ². So t/P ≤ 1.42/(ε²τ) ≤ 5.7 τ/ε². In the YES case |0⟩ is invariant, and the error is again one-sided.

**Number of runs.** The runs are independent and NO is detected in each with probability at least P, so R runs miss with probability at most (1 − P)^R ≤ e^{−PR} ≤ δ. The total time is R t ≤ (ln(1/δ)/P + 1) t ≤ (1 + ln(1/δ)) t/P.

## Remarks

- The interleaved X_Π swaps the roles of |0⟩ and |1⟩. To first order this removes the unknown energy shift ⟨1|H|1⟩, which otherwise limits the coherent transfer from |0⟩ to |1⟩ to an amplitude O(ε). The swap makes the YES dynamics a multiple of the identity exactly, at every step length, so no step length has to go to 0.
- The leakage out of span{|0⟩, |1⟩} in each step is of order s², so its total over a run of time t is of order ts. The run lengths O(min{1/ε, 1/τ}) keep this below a constant. For τ ≤ ε a single run of time O(1/ε) succeeds with constant probability. For τ > ε, runs of time O(1/τ) succeed with probability Ω((ε/τ)²).
- In [2], Hamiltonian learning with a minimum evolution time T reaches the 1/ε scaling for Pauli-sparse Hamiltonians, with cost exponential in the sparsity. Theorem 1 concerns a different task, distinguishing rather than learning, with no sparsity assumption, and its bound does not depend on the dimension.

## Check

`sim/check.py`, output in `sim/out.txt`:

- For the random instances with d between 3 and 8, ε between 0.003 and 0.5, step lengths up to 1/2, half of them with a strong shift of ⟨1|H|1⟩ and strong coupling of |1⟩ to the rest of the space: in the YES case A = diag(1, δ₁) and ⟨1|C^m|0⟩ = 0 to 10⁻¹². In the NO case A₀₁ = A₁₀, the entry bounds hold, the closed form for ⟨1|C^m|0⟩ matches the matrix power to 10⁻⁹, and the amplitude is at least the lower bound of the proof.
- Over a logarithmic grid of 300 × 300 pairs with 10⁻⁴ ≤ ε ≤ 1 and 10⁻⁵ ≤ τ ≤ 1, the per-run bounds of the proof give t/P ≤ 8.2 max{1/ε, τ/ε²}, inside the constant 46 of Theorem 1.
- On fixed instances in d = 8, the exact detection probability per run lies above the bound.

## Scope

- Theorem 1 is an upper bound. For ε < τ ≤ 1 the only lower bound is Ω(1/ε) [1], so the optimal total time in that range is not determined here.
- The step length is exactly τ. Longer steps are allowed by the model but are not used.
- Lean: not formalized.

## References

1. E. Wang, J. Carolan, A. M. Childs. On state distinguishing without inverse queries. arXiv:2610.05389 (2026).
2. M. Shin, J. Lee, C. Oh. Heisenberg-limited Hamiltonian learning without short-time control. arXiv:2604.27838 (2026).

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
