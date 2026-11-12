# A √q/ε quantum lower bound for partition functions from thermal-state reflections

2026-11-12

## Problem

Let χ be a finite set and H: χ → {0, 1, …, n} an energy function, with partition function Z(β) = Σ_{ω∈χ} e^{−βH(ω)}, so that Z(0) = |χ| and Z(∞) = |H^{−1}(0)|. The thermal qsample is |μ_β⟩ = Σ_ω (e^{−βH(ω)}/Z(β))^{1/2} |ω⟩, and R_β = 1 − 2|μ_β⟩⟨μ_β| is the reflection about it. The task is to output Ẑ with |Ẑ − Z(∞)| ≤ ε Z(∞), given χ. Let q = log(Z(0)/Z(∞)) ≤ log|χ|.

Quantum algorithms for this task [3, 4, 5] are built from reflections R_β at chosen β, thermal qsamples, and rotations controlled by the energy, and their cost is counted in reflections. Previous best bounds: Ω(1/ε) reflections [1, Theorem 3], with the question whether a lower bound that grows with |χ| holds stated open in [1, Section 4]; upper bound Õ(log^{3/4}|χ| log^{3/4}(n)/ε + log^{1/2}|χ| log^{3/2} n) reflections [4, proof of Theorem 4.1], with the annealing schedule of [3, Theorem 13]. For classical algorithms that sample the energy of thermal states, Θ̃(q/ε²) samples are necessary and sufficient [2, Theorems 3 and 4].

## Model

An *energy-symmetric* algorithm works on configuration registers, each a copy of ℂ^χ, and a workspace W, and uses:

1. preparation of a configuration register in |μ_β⟩ for any β ∈ [0, ∞] (cost 1);
2. the reflection R_β on a configuration register, or its controlled version, for any β, possibly with β held in a register (cost 1);
3. unitaries Σ_ω |ω⟩⟨ω| ⊗ V_{H(ω)} that act on W controlled by the energy of a configuration register, with V_0, …, V_n fixed by the algorithm (cost 0);
4. unitaries on W (cost 0);

and it outputs the result of a measurement of W. The product and mean estimators of [4, 5] use only such operations. The uniform state |μ_0⟩ is counted in item 1, since with item 3 each copy gives one sample of the energy at β = 0.

## Result

**Theorem 1.** For every n ≥ 7 and ε ≤ 1/100 there are energy functions H_0, H_1: χ → {0, …, n} on a common finite set χ, with q = log(Z(0)/Z(∞)) ∈ [n(n − 1)/2, n(n − 1)/2 + 2.1] for both and log|χ| ≤ q + log(10n/ε) + 1, such that every energy-symmetric algorithm that estimates Z(∞) to relative error ε with success probability at least 2/3 on both uses k qsamples and T reflections with

k + 2T ≥ n/(35ε) ≥ √(2q)/(35ε).

So Ω(√q/ε) reflections and qsamples are needed by energy-symmetric algorithms. The bound Ω(1/ε) of [1] holds for a different class, which reaches the energy only through reflections but may apply any operation on the configurations that does not depend on H; the two classes are incomparable. For classical energy sampling the same instances give Ω(q/ε²), implied by [2, Lemma 45]; the quantum bound is its square root. On the algorithmic side, the product estimator of [5, Section 4.3] uses Õ(m/ε) reflections for an annealing schedule with m stages whose stage ratios have relative second moment at most 4.

## Proofs

*Reduction to the energy register.* Let c_x = |H^{−1}(x)| > 0 for all x, and let |u_x⟩ be the uniform superposition over H^{−1}(x). The isometry J: ℂ^{n+1} → ℂ^χ, |x⟩ ↦ |u_x⟩, satisfies |μ_β⟩ = J|m_β⟩ with |m_β⟩ = Σ_x (c_x e^{−βx}/Z(β))^{1/2} |x⟩. Hence R_β J = J(1 − 2|m_β⟩⟨m_β|), the energy-controlled unitary of item 3 maps J|x⟩ ⊗ |w⟩ to J|x⟩ ⊗ V_x|w⟩, and unitaries on W commute with J. By induction, the state of an energy-symmetric algorithm is (J^{⊗r} ⊗ 1_W) applied to the state of the same algorithm on registers ℂ^{n+1}, with |μ_β⟩, R_β and the energy-controlled unitaries replaced by |m_β⟩, 1 − 2|m_β⟩⟨m_β| and Σ_x |x⟩⟨x| ⊗ V_x. The measurement of W has the same statistics. Only the vectors m_β depend on the instance.

*Instances.* Following [2, Section 8.1], let c_x for x = 0, …, n be the coefficients of g(t) = Π_{k=0}^{n−1}(e^k + t) = Σ_x c_x t^x, and set ν = 10ε/n and c′_x = e^{νx} c_x. With the energy E = n − x, the thermal weights are proportional to c_x e^{βx}, and z(β) = log Σ_x c_x e^{βx} = Σ_k log(e^k + e^β) has z″(β) = Σ_k e^{k+β}/(e^k + e^β)² ≤ 2e/(e − 1) ≤ 4 [2, Observation 49]. The ground states are x = n, with c_n = 1, so q = z(0) = Σ_k log(e^k + 1) ∈ [n(n − 1)/2, n(n − 1)/2 + 2].

(i) *Close qsamples.* For β ∈ [0, ∞), the overlap of the base and tilted vectors is ⟨m_β|m′_β⟩ = exp(z(β + ν/2) − (z(β) + z(β + ν))/2) ≥ e^{−ν²/2}, since the second difference of z over a step ν/2 is at most 4(ν/2)². So ‖m_β − m′_β‖² = 2(1 − ⟨m_β|m′_β⟩) ≤ ν², and at β = ∞ both vectors equal |n⟩.

(ii) *Different answers.* The ground-state fractions satisfy log Q′ − log Q = νn − (z(ν) − z(0)) ≥ νn − z′(0)ν − 2ν² with z′(0) = Σ_k 1/(1 + e^k) ≤ e/(e − 1), so log Q′ − log Q ≥ 10ε − 15.9ε/n − 2ν² > 7.7ε for n ≥ 7. An estimate with relative error ε ≤ 1/100 determines log Z(∞) up to 1.01ε, so it separates the two instances.

(iii) *Integer counts.* Let K = ⌈10n/ε⌉ and N = ⌈K Σ_x c_x⌉, scale both count vectors to the common total N, round to integers and change the largest count of each so that the totals agree. Each count changes by a relative amount η ≤ 0.023ν (asserted in `sim/check.py`), so each m_β moves by at most 1.02η and log Q by at most 2.03η. Let χ be a set of size N and H_0, H_1 any energy functions with these level sizes; then q changes by at most 0.1, and log|χ| ≤ q + log K + 1.

*Lower bound.* By (i) and (iii), ‖m^{(0)}_β − m^{(1)}_β‖ ≤ ν + 0.07ν ≤ 1.07ν for every β. For unit vectors a, b, ‖R_a − R_b‖ = 2(1 − |⟨a|b⟩|²)^{1/2} ≤ 2‖a − b‖, and a reflection controlled by a register holding β is block diagonal in β. In the energy-register picture the two runs differ only in these vectors, so by the hybrid argument [6] the final states satisfy ‖ψ^{(0)} − ψ^{(1)}‖ ≤ 1.07ν k + 2.14ν T. Success probability 2/3 on both instances with different answers needs ‖ψ^{(0)} − ψ^{(1)}‖ ≥ 1/3, so k + 2T ≥ 1/(3.21ν) ≥ n/(35ε). Finally 2q ≤ n² − n + 4.2 ≤ n² for n ≥ 7, so n ≥ √(2q). ∎

## Check

`sim/check.py` builds the counts in log space for n from 7 to 200 and ε from 10⁻² to 10⁻⁵ and asserts: ‖m_β − m′_β‖ ≤ ν on a grid of β in [0, 4n] and at β = ∞ (the largest value is 0.50ν); |log Q′ − log Q| > 2.02ε (the smallest value is 8.6ε); the range of q for the base and both tilted count vectors; that the integer realization moves the vectors and log Q by at most 0.07ν; and ‖R_a − R_b‖ ≤ 2‖a − b‖ on 2000 random pairs. Output in `sim/out.txt`.

## Scope

- Written proof with numerical checks.
- The bound holds for energy-symmetric algorithms. Algorithms that apply operations on the configurations which do not commute with the symmetry (for example measuring configuration labels or reflecting about other states) are not covered.
- Qsamples and reflections at β = 0 are counted. This is needed in a model with free energy-controlled unitaries, since free uniform samples would reveal the level sizes at no cost, and it matches the cost model of [2].
- The instances have q of order n²; for q much larger than n², the bound Ω(n/ε) of Theorem 1 is the one shown.
- The upper bounds of [4, 5] are not shown to match Ω(√q/ε).

## References

[1] Z. Chen, G. Nannicini. A simple lower bound for the complexity of estimating partition functions on a quantum computer. arXiv:2404.02414.

[2] D. G. Harris, V. Kolmogorov. Parameter estimation for Gibbs distributions. ACM Transactions on Algorithms 21(1), Article 3 (2024). arXiv:2007.10824 (numbering of the arXiv version).

[3] A. W. Harrow, A. Y. Wei. Adaptive quantum simulated annealing for Bayesian inference and estimating partition functions. SODA 2020. arXiv:1907.09965.

[4] A. Cornelissen, Y. Hamoudi. A sublinear-time quantum algorithm for approximating partition functions. SODA 2023. arXiv:2207.08643.

[5] R. Zhang. Improved upper and lower bounds for quantum convex-body volume estimation. arXiv:2610.04987.

[6] C. H. Bennett, E. Bernstein, G. Brassard, U. Vazirani. Strengths and weaknesses of quantum computing. SIAM Journal on Computing 26, 1510-1523 (1997). arXiv:quant-ph/9701001.

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
