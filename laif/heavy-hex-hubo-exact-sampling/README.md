# Exact Boltzmann sampling of heavy-hex higher-order spin glasses

_18 November 2026_

In [1], digitized counterdiabatic quantum sampling (DCQS) on a 156-qubit IBM Heron processor draws low-temperature Boltzmann samples of the spin glass

H(z) = Σ_i h_i z_i + Σ_⟨ij⟩ J_ij z_i z_j + Σ_⟨ijk⟩ K_ijk z_i z_j z_k,  z ∈ {−1, +1}^156,

with every nearest-neighbour term of the heavy-hex coupling map (156 one-body, 176 two-body and 244 three-body terms) and coefficients drawn from the Sidon set {±8/28, ±13/28, ±19/28, ±1}. The same instance is solved in [2] by a quantum annealer followed by the IBM processor. The figure of merit of [1] is

ln Z̃ = ln Σ_{distinct sampled states z} exp(−H(z)/T).

For 50 000 samples, which take 5 s on the processor at the sampling rate stated there, [1] reports that parallel tempering needs 1000 to 1500 times as many samples to reach the same ln Z̃ at T = 0.02, about twice the runtime.

## Instances

The coefficients of [1, 2] are not published. The instances here are five fresh draws from the Sidon set on the exact term structure: the 156-qubit Heron r2 coupling map (eight rows of 16 qubits joined by four bridge qubits per gap) gives exactly 156 one-body, 176 two-body and 244 three-body terms, where the three-body terms are all paths i-j-k of length two. Their ground energies lie between −209.82 and −188.07. The instance of [1, 2] has the ground energy −186.86 [2].

## Result

The interaction graph of these instances, with the three-body terms as triangles, has an elimination order of width 16. Variable elimination along it gives, on one laptop core:

- the exact ln Z at a given temperature in 11 to 65 ms,
- an exact ground state in 11 to 32 ms,
- independent exact Boltzmann samples, drawn backwards along the order from the conditional tables, at about 15 to 40 µs each, so 50 000 samples take about 1 to 2 s.

Every method obeys ln Z̃ ≤ ln Z, because ln Z̃ sums over a subset of all states. So the gap ln Z − ln Z̃ of N exact samples bounds by how much any sampler can exceed exact sampling on this figure of merit at equal sample count. For N = 50 000, the largest gap over the five instances is:

| T | 0.5 | 0.25 | 0.125 | 0.1 | 0.05 | 0.02 |
|---|---|---|---|---|---|---|
| ln Z − ln Z̃, 50 000 exact samples | 6.8 | 0.60 | 0.037 | 0.016 | 0.002 | ≤ 10⁻⁴ |

At T = 0.02, where [1] reports the runtime comparison, no sampler can exceed 50 000 exact samples by more than 10⁻⁴ on these instances, and the exact ln Z itself takes milliseconds.

For comparison with the parallel-tempering numbers of [1], a plain parallel tempering (14 replicas on a fixed geometric ladder from T = 0.02 to 1.5, single-spin Metropolis sweeps, neighbour swaps after each sweep, the states of all replicas counted) reaches ln Z within 10⁻⁴ at T = 0.02 after 3 × 50 000 states on four of the five instances (about 2 s) and after 30 × 50 000 on the fifth (about 10 s). [1] reports 1000 to 1500 × 50 000 with an adaptive ladder on its own instance.

## Scope

- **Instances.** Fresh draws on the same term structure and coefficient set, not the coefficients of [1, 2]. The elimination width depends only on the term structure, so the exact methods apply unchanged to the instance of [1, 2].
- **Parallel tempering.** The ladder here is fixed and geometric; [1] tunes the number of replicas and the temperatures adaptively for a target swap acceptance. The instances differ.
- **Wall time** is measured on one laptop core and set against the sampling rate of the processor stated in [1]; post-processing of the quantum samples is not counted there and not here.
- The figure of merit counts distinct states only, and at low temperature it is reached by any method that lists the lowest-energy states, sampled or not.

## Exactness

The sampler draws the variables in reverse elimination order, each from its conditional distribution given the variables already drawn. Exactness of sequential sampling from such conditionals, for any nonnegative weight with positive total, is the Lean theorem `P_eq` in [qemcmc-block-heat-bath](../qemcmc-block-heat-bath/) (standard axioms only). That the elimination tables are these conditionals is not formalized; `sim/test_hubo.py` checks ln Z and the ground energy against enumeration on three connected 16-qubit pieces of the coupling map, and a chi-square test of 200 000 samples against the exact distribution.

## Files

- `sim/hubo.py`: the coupling map, the instances, the energy and the exact eliminator (`log_z`, `sample`, `ground`).
- `sim/test_hubo.py`: the checks against enumeration.
- `sim/exact156.py`: exact ln Z, ground energies and ln Z − ln Z̃ for 1000, 10 000 and 50 000 exact samples (`data/exact156.txt`).
- `sim/pt156.py`: the parallel tempering and its ln Z̃ (`data/pt156.txt`).

## References

1. N. N. Hegade, N. L. Kortikar, B. A. Bhargava et al. Digitized counterdiabatic quantum sampling. arXiv:2510.26735.
2. S. V. Romero, A. G. Cadavid, E. Solano, N. N. Hegade. Sequential quantum computing. arXiv:2506.20655.
