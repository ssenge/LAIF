# Selected configuration interaction for the stretched H12 chain at a fixed determinant budget

_25 November 2026_

In [1], quantum measurements propose determinants for selected configuration interaction (SCI). The test system is the equally spaced linear H12 chain in the STO-3G basis with canonical restricted mean-field (RHF) orbitals, whose full space has 853,776 determinants with six electrons of each spin. A fixed classical baseline is kept, candidates from a heat-bath (HCI) pool [3] and from the quantum proposals are ranked by a common energetic criterion (CEN2), and the final space is diagonalized once at N = 20,000 determinants. At the bond length R = 1.8 Å, the noiseless quantum proposals give a variational energy 52.95 mHa above the full configuration interaction (FCI) energy, against 93.45 mHa for the classical-only selection. On the trapped-ion processor the gain over classical-only selection is positive and smaller than in the noiseless case [1].

## Result

A standard iterative selection [2] at the same final budget: start from the RHF determinant, rank all outside determinants by their first-order energy |⟨I|H|ψ⟩|² / (E₀ − H_II), add whole spin bundles (all determinants with the same doubly and singly occupied orbitals, scored by the sum over the bundle) until the space doubles, take the lowest singlet, and repeat until the space holds exactly 20,000 determinants.

| R (Å) | Error, iterative selection (mHa) | With second-order correction (mHa) | 20,000 determinants of largest FCI weight (mHa) | Values of [1] at the same budget (mHa) |
|---|---|---|---|---|
| 1.2 | 12.49 | 3.79 | 12.38 | |
| 1.3 | 20.35 | 7.58 | 20.23 | |
| 1.4 | 30.72 | 13.89 | 31.45 | |
| 1.5 | 42.21 | 23.27 | 45.37 | |
| 1.6 | 50.54 | 33.50 | 58.72 | |
| 1.7 | 52.95 | 40.83 | 66.67 | |
| 1.8 | 49.66 | 42.29 | 68.26 | 52.95 quantum proposals, 93.45 classical-only (40.47 and 54.59 with second-order correction) |

All errors are relative to the FCI energy in the same basis. At R = 1.8 Å the error is 49.66, 49.69 and 49.81 mHa for growth factors 2, 1.5 and 1.25 per step. The second-order correction is the perturbative sum with diagonal energy denominators over all determinants outside the final space, as in [1, Eq. (5)].

At R = 1.8 Å, the geometry of the hardware run in [1], the iterative classical selection reaches a lower variational energy at the same final dimension than the noiseless quantum proposals combined with the classical pool. Its energy is therefore also below the hardware result, whose gain is smaller than the noiseless one [1]. This hints at a possible gap in the comparison of [1]: the classical-only reference there is a single selection stage from a fixed pool, and a standard iterative selection at the same budget already reaches below the quantum-augmented energy. With the second-order correction, the quantum-augmented space of [1] stays 1.8 mHa lower.

## Scope

- **Same budget.** The comparison fixes the number of determinants in the final space, as in [1]. Total computational cost is not matched, in [1] or here.
- **No protected baseline.** The iterative selection starts from one determinant and does not keep the fixed baseline of [1].
- **Orbitals.** Canonical RHF orbitals, as in [1]. The difference between RHF and FCI energies is 0.282 Ha at 1.2 Å and 0.751 Ha at 1.8 Å, as reported in [1].
- **Status.** Numerical, with the exact FCI energy as reference. Each final space is checked to be a union of whole spin bundles with exactly 20,000 determinants, its state to be a singlet, and its energy to lie above the FCI energy.

## Files

- `sim/cipsi.py`: setup, FCI, iterative selection, largest-weight reference and second-order correction (`python -I cipsi.py out.jsonl 1.8 2.0`, about 3 minutes and below 1 GB per geometry).
- `data/scan.jsonl`: the seven geometries. `data/growth.jsonl`: the growth factors at 1.8 Å.

## Use of AI

The analysis, code and text were produced with Claude Opus 5.5.

## References

1. K. Yamamoto, I. Hamamura, J. W. Pedersen, D. Gowland, G. Laude, S. Maekawa, D. Muñoz Ramo, E. Kyoseva, W. Dawson. Quantum residual exploration for selected configuration interaction. arXiv:2611.12672.
2. B. Huron, J. P. Malrieu, P. Rancurel. Iterative perturbation calculations of ground and excited state energies from multiconfigurational zeroth-order wavefunctions. Journal of Chemical Physics 58, 5745 (1973).
3. A. A. Holmes, N. M. Tubman, C. J. Umrigar. Heat-bath configuration interaction: an efficient selected configuration interaction algorithm inspired by heat-bath sampling. Journal of Chemical Theory and Computation 12, 3674 (2016).
