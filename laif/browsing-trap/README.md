# The browsing trap: collapse and recovery densities of browsers for tree regeneration

Written 25 Nov 2026.

**Setting.** A tree species has canopy share C and saplings in k height classes. Seeds fall on the free space
1 − C and enter class 1. Saplings advance at rate g, die at the background rate m, and escape from class k into the
canopy (efficiency e). The canopy dies at rate m_C. Browsers at density D have a Type II functional response, so the
per-sapling browse rate is φ = aD/(1 + a h N), with N the browsable saplings. Browsed saplings die at rate μφ. With
several tree species, each species has its own rates and a palatability π_i, and the browsers share their time over
all saplings.

Satiation of browsers creates an Allee effect: more saplings dilute the browsing per sapling. Allee effects driven
by satiated consumers are known [1], and a "browse trap" for plants held in small stages by browsers is described
in [2]. Here the densities at which regeneration collapses and recovers are given exactly.

## Results

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Browser densities of collapse and recovery of a tree species with k height classes | Allee effects from consumer satiation [1]; browse trap described in [2] | The equilibria form the explicit curve D(C). Recovery from the empty state needs D < D_r = ((e f g^k/m_C)^{1/k} − g − m)/(μ a), independent of the satiation h. The established state collapses at D_c = max_C D(C). Both states are stable for D_r < D < D_c, and the gap D_c − D_r grows with h | Claim (stability of the positive branch: numerical). Numerical: ODE runs confirm both states |
| Obs. 1 | Composition with several tree species | | At the same browser density the final canopy can be a palatable species alone or an unpalatable species alone, depending on the initial state | Numerical |

## Statement

Write κ = m_C/(e f g^k) and O*(C) = ((1 − C)/κ)^{1/k}.

**Theorem 1 (Claim).** The positive equilibria are exactly the points (C, D(C)) with O*(C) ≥ g + m, where

D(C) = φ(C)(1 + a h N(C))/a,  φ(C) = (O*(C) − g − m)/μ,  N(C) = f C (1 − C)/O*(C) · Σ_{c=0}^{k−1} (g/O*(C))^c.

The empty state is stable for D > D_r = D(0+), and the positive branch exists up to D_c = max D(C). When D(C)
rises from C = 0, the branch folds back, so for D in (D_r, D_c) the stable empty state coexists with a positive
equilibrium. In the ODE runs this positive equilibrium is stable.

*Proof sketch.* At equilibrium each class has the same exit rate O = g + m + μφ. So n_c = n_1 (g/O)^{c−1}, and
n_1 = fC(1 − C)/O. Recruitment balance e g n_k = m_C C gives O = O*(C). Given C, this fixes φ, then N, and
then D from the functional response. The empty state has invasion rate e f g^k / (g + m + μ a D)^k − m_C, whose sign
change gives D_r. ∎

**Reading.** A species lost at browser density D_c returns only below D_r. Satiation (large h) does not change D_r,
but it raises D_c. The return of a lost species therefore needs a much lower browser density than the density at
which it was lost.

## Scope

- One canopy compartment per species, a fixed browser density, and no seed input from outside the stand.
- The parameters in the scripts are illustrative and not calibrated to a forest.

## Scripts

- `sim/trap.py`: the ODE model for any number of tree species.
- `sim/branch.py`: the curve D(C), D_r and D_c for k = 1, 2, 4, 8 and three satiation levels. It asserts both stable
  states at a density between D_r and D_c.
- `sim/multi.py`: three species of different palatability. It asserts the two compositions at the same density.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check
proofs, to write the scripts, and to draft the text.

## References

1. J. C. Gascoigne, R. N. Lipcius. Allee effects driven by predation. J. Appl. Ecol. (2004).
   doi:10.1111/j.0021-8901.2004.00944.x.
2. A. Palmerlee, K. Vaughn, T. Young. Escaping the browse trap: patterns of natural blue oak regeneration in grazed
   landscapes. Rangeland Ecol. Manage. (2025). doi:10.1016/j.rama.2024.11.005.
