# Local algorithms for Max-q-XORSAT on regular hypergraphs of large girth

_11 November 2026_

Max-q-XORSAT has one clause per hyperedge e = (i_1, ..., i_q) with a sign J_e, and the clause is satisfied when z_{i_1} ⋯ z_{i_q} = J_e for the spins z_i = ±1. We study local algorithms of radius p on (D + 1)-regular q-uniform hypergraphs of girth above 2p + 1. There the expected satisfied fraction is the same on every such hypergraph, for every choice of the signs, and as D → ∞ it is

  1/2 + ν √(q/(2D)) + o(1/√D).

Reference [1] computes the coefficient ν for QAOA at depth p, which has radius p, and optimizes it for q = 3, ..., 6 and p ≤ 14 (numerical values in [2]). By [4], the same coefficient describes QAOA on the pure q-spin model. For q = 2 this is Max-Cut, which the folder [max-k-cut-local-algorithms](../max-k-cut-local-algorithms/) covers. For comparison, the best satisfied fraction of random (D + 1)-regular q-uniform hypergraphs has coefficient Π_q, given by a variational formula [5].

## Result

For q = 3 and q = 4, a classical local message-passing algorithm of radius p has a larger coefficient ν than QAOA at depth p, for every p from 1 to 14, in the limit D → ∞. For q = 5 the same holds for every p from 2 to 14, and for q = 6 for every p from 8 to 12. For p ≥ 2 this rests on the single-site description of the limit below, which is used here without a proof for these algorithms. For p = 1 the value is exact.

| p | q = 3, QAOA [1, 2] | q = 3, here | q = 4, QAOA [1, 2] | q = 4, here |
|---|---|---|---|---|
| 1 | 0.2706 | 0.28377 | 0.2517 | 0.25420 |
| 2 | 0.3718 | 0.4165 | 0.3480 | 0.3770 |
| 3 | 0.4352 | 0.4783 | 0.4086 | 0.4516 |
| 4 | 0.4792 | 0.5152 | 0.4511 | 0.4805 |
| 5 | 0.5124 | 0.5554 | 0.4835 | 0.5075 |
| 6 | 0.5385 | 0.5822 | 0.5091 | 0.5346 |
| 7 | 0.5597 | 0.6229 | 0.5301 | 0.5422 |
| 8 | 0.5773 | 0.6259 | 0.5475 | 0.5885 |
| 9 | 0.5922 | 0.6399 | 0.5624 | 0.6054 |
| 10 | 0.6050 | 0.6521 | 0.5752 | 0.6071 |
| 11 | 0.6161 | 0.6630 | 0.5864 | 0.6204 |
| 12 | 0.6258 | 0.6671 | 0.5963 | 0.6204* |
| 13 | 0.6345 | 0.6802 | 0.6050 | 0.6338 |
| 14 | 0.6422 | **0.6937** | 0.6128 | **0.6361** |

The entry marked * is the algorithm of depth 11, since an algorithm of radius 11 also has radius at most 12. At p = 1 the margin is 0.0132 for q = 3 and 0.0025 for q = 4, both exact. From p = 2 on, the smallest margin is 0.0360 for q = 3 (at p = 4) and 0.0121 for q = 4 (at p = 7). Both are more than 15 standard errors of the sampled values.

For q = 5 the network family is above QAOA at every depth p from 2 to 14:

| p | q = 5, QAOA [1, 2] | q = 5, here |
|---|---|---|
| 2 | 0.33 | 0.3475 |
| 3 | 0.3878 | 0.3932 |
| 4 | 0.4285 | 0.4492 |
| 5 | 0.4595 | 0.4716 |
| 6 | 0.4842 | 0.4943 |
| 7 | 0.5044 | 0.5092 |
| 8 | 0.5212 | 0.5345 |
| 9 | 0.5356 | 0.5462 |
| 10 | 0.5481 | 0.5724 |
| 11 | 0.5589 | 0.5863 |
| 12 | 0.5685 | 0.5991 |
| 13 | 0.577 | 0.5991* |
| 14 | 0.5846 | **0.5991*** |

The entries marked * are the algorithm of depth 12. The smallest margin is 0.0048 (at p = 7), about 7 standard errors. At p = 1 the best algorithm of the class is the threshold algorithm below, with ν = 0.23407 for q = 5.

For q = 6 the network family is above QAOA at every depth p from 8 to 12:

| p | q = 6, QAOA [1, 2] | q = 6, here |
|---|---|---|
| 8 | 0.4984 | 0.5040 |
| 9 | 0.5122 | 0.5261 |
| 10 | 0.5241 | 0.5410 |
| 11 | 0.5345 | 0.5438 |
| 12 | 0.5437 | 0.5531 |

The smallest margin is 0.0056 (at p = 8), about 8 standard errors.

## The algorithms

Every vertex i draws a random sign s_i and starts with the message m_0(i) = μ s_i. In round t = 1, ..., p it computes the field

  φ_t(i) = D^(−1/2) Σ_{e ∋ i} J_e Π_{j ∈ e, j ≠ i} m_{t−1}(j)

and then its next message m_t(i) = F_t(s_i, φ_1(i), ..., φ_t(i)). After round p it outputs z_i = sign G(s_i, φ_1(i), ..., φ_p(i)). The output depends on the radius-p neighbourhood of i, so on hypergraphs of girth above 2p + 1 the neighbourhood of a clause is a hypertree.

Every vertex also draws a second random sign τ_i. It sends τ_i m_t(i) instead of m_t(i), computes φ_t(i) from the messages it receives, applies F_t and G to τ_i φ_t(i) instead of φ_t(i), and outputs τ_i z_i. This is the algorithm above run on the signs J_e Π_{j ∈ e} τ_j. On a hypertree these signs are independent and uniform for any fixed J_e, so the value does not depend on the signs, and the radius stays p. All values in this folder are for this version. On independent uniform signs it has the same value as the version without τ.

Two families of functions F_t and G are used. At each depth the table shows the better one (`data/xor_limit_q.jsonl`, field `family`).

- **Spin dynamics.** The dynamics of [6], with the field of a q-body clause: each vertex holds ψ ∈ ℂ², starting at cos α u + sin α s_i w with u = (1, 1)/√2, w = (1, −1)/√2. Round t applies the phase exp(−i G_t σ φ_t) to the component σ = ±1 and then the mixer ψ ↦ ψ + (e^(−iβ_t) − 1)⟨u, ψ⟩u. The message is m = |ψ_+|² − |ψ_−|², before each round. The output is the sign of the final m, or, in the family "spin, linear output", the sign of a linear combination of m_0, ..., m_p and φ_1, ..., φ_p. The schedule has 2p + 1 parameters, plus 2p + 1 output weights.
- **Network.** F_t = tanh(a_t · tanh(W_t v + b_t) + c_t) and G the same without the outer tanh, with 8 hidden units and v = (s, φ_1, ..., φ_t) padded with zeros, and μ = tanh(c_0).

In the limit, the output that is best for given messages is the sign of a linear combination of the fields and the messages, which is why the linear output is used for the spin dynamics.

### Infinite degree

As D → ∞ the field at a vertex follows the single-site description

  φ_t = η_t + Σ_{r<t} K(t, r) m_{r−1},  K(t, r) = (q − 1) E[∂m_{t−1}/∂φ_r] Q(t − 1, r − 1)^(q−2),

where Q(t, r) = E[m_t m_r], η is a centred normal process with covariance Q(t − 1, r − 1)^(q−1) (entrywise power), and ∂/∂φ_r is the mean total response, including the feedback through the sum. The clause term then gives

  ν = √(q/2) Σ_{t=1}^{p} E[∂z/∂φ_t] E[m_{t−1} z]^(q−1),  E[∂z/∂φ] = Σ⁻¹ E[η z],

by normal integration by parts, with Σ the covariance of η. This is the same kind of limit that [1] computes for QAOA, and the same as Section 6 of the Max-k-Cut folder for q = 2. It is computed layer by layer from samples of the process (`sim/xor_limit.py`, `sim/xor_mp.py`).

At p = 1 there is no sum, η is a normal variable, and the best output is z = sign(η + λ s) for a threshold λ, the threshold algorithm of [3]. Then

  ν = √(q/2) · √(2/π) · e^(−λ²/2) · erf(λ/√2)^(q−1),

which is maximal at λ = 1.1322 for q = 3 and λ = 1.2922 for q = 4, with the values in the table (`sim/xor_p1.py`). It was shown in [3] that this algorithm is above QAOA at p = 1 for q = 2, 3 and 4.

### Training and evaluation

The spin schedules are trained by gradient descent on the limit with a smoothed output, each depth starting from the previous one with a nearly idle last layer, and refined by a random search and a simplex search for the smallest depths (`sim/xsearch.py`, `sim/xaxis.py`). The networks are trained the same way, each depth starting from the previous one with its last message function copied (`sim/xor_mp.py`). Each value for p ≥ 2 is the mean of independent solves of the limit on noise that played no part in training or in the choice of the schedule (`sim/xeval.py`, seeds from 5000): 10 solves with 4 · 10⁵ samples for q = 3 and p ≤ 10, and 40 solves with 10⁵ samples otherwise (all of q = 5 and 6). The standard error is at most 0.0008. For q = 3 and 4 a second evaluation on other noise (5 solves with 2 · 10⁵ samples) agrees with every value to within 0.003. With fewer samples per solve the estimate is lower, by up to about 0.008 at 5 · 10⁴ samples.

## Status and checks

Numerical results, with an exact value at p = 1. No part is formalized in Lean.

- **Exact radius 1:** the closed form agrees with the sampled limit: 0.2829 ± 0.0004 (spin dynamics) and 0.2837 ± 0.0002 (network) against 0.28377 for q = 3, and 0.2545 ± 0.0003 (network) against 0.25420 for q = 4.
- **Two implementations:** for q = 2 the spin dynamics of `sim/xor_limit.py` gives 0.3362, 0.4580 and 0.5397 at p = 1, 2, 3 on the schedules of the Max-k-Cut folder, whose separate implementation gives 0.3367, 0.4583 and 0.5389.
- **Finite degree:** `sim/xor_tree.py` and `sim/xor_mp_tree.py` sample the algorithms on the (D + 1)-regular q-uniform hypertree around a clause, and report (satisfied fraction − 1/2)/√(q/(2D)) (`data/xor_tree_check.txt`). For q = 3 and the spin dynamics, on the schedules in `data/xor_tree_check_3.jsonl`, p = 1 gives 0.2715 ± 0.0028, 0.294 ± 0.009 and 0.276 ± 0.029 at D = 10, 100 and 1000, against 0.2829. p = 2 gives 0.357 ± 0.004, 0.388 ± 0.007 and 0.376 ± 0.013 at D = 10, 30 and 100, against 0.3776. For the network at p = 2, q = 3 gives 0.3902 ± 0.0028, 0.4058 ± 0.0028, 0.3950 ± 0.0057 and 0.4137 ± 0.0064 at D = 10, 20, 40 and 100, against 0.4165, and q = 4 gives 0.3588 ± 0.0024 and 0.3668 ± 0.0049 at D = 10 and 40, against 0.3770. At p = 3, q = 3 gives 0.4526 ± 0.0038 and 0.4717 ± 0.0079 at D = 10 and 20, against 0.4783, and q = 4 gives 0.4080 ± 0.0024 and 0.4292 ± 0.0036 at D = 6 and 12, against 0.4516. For q = 5 at p = 2 the network gives 0.3286 ± 0.0047 and 0.3357 ± 0.0097 at D = 10 and 20, against 0.3475. At small D the values lie below the limit. The series that reach D ≥ 20 end within 2.5 standard errors of it.
- **Not covered:**
  - a proof of the single-site description for p ≥ 2, and error bounds for its sampling beyond the repeated solves;
  - finite degree for p ≥ 4, and beyond the checks above for p ≤ 3;
  - q = 5 at p = 1, q = 6 outside 8 ≤ p ≤ 12, and q ≥ 7.

## Files

- `sim/xor_limit.py`: the single-site limit of the spin dynamics and its training.
- `sim/xor_mp.py`: the same for the network family.
- `sim/xor_p1.py`: the exact value at p = 1.
- `sim/xsearch.py`, `sim/xaxis.py`: random search, simplex search and refinement of spin schedules, also with the linear output.
- `sim/xeval.py`: the repeated solves.
- `sim/xor_tree.py`, `sim/xor_mp_tree.py`: the finite-degree checks on the hypertree.
- `data/xor_limit_3.jsonl`, `data/xor_limit_4.jsonl`, `data/xor_limit_5.jsonl`, `data/xor_limit_6.jsonl`: the schedule, value, standard error and family at each depth.
- `data/xor_tree_check.txt`, `data/xor_tree_check_3.jsonl`: the finite-degree checks and the spin schedules they use.

Requirements: Python 3.12 with numpy, scipy and jax. Run the scripts from `sim/`.

## References

1. J. Basso, E. Farhi, K. Marwaha, B. Villalonga, L. Zhou. The Quantum Approximate Optimization Algorithm at High Depth for MaxCut on Large-Girth Regular Graphs and the Sherrington-Kirkpatrick Model. TQC 2022, arXiv:2110.14206.
2. J. Basso, E. Farhi, K. Marwaha, B. Villalonga, L. Zhou. Performance of the QAOA on MaxCut over Large-Girth Regular Graphs, 2022. https://github.com/benjaminvillalonga/large-girth-maxcut-qaoa (file data.csv).
3. K. Marwaha, S. Hadfield. Bounds on approximating Max kXOR with quantum and classical local algorithms. Quantum 6, 757 (2022), arXiv:2109.10833.
4. J. Basso, D. Gamarnik, S. Mei, L. Zhou. Performance and limitations of the QAOA at constant levels on large sparse hypergraphs and spin glass models. FOCS 2022, arXiv:2204.10306.
5. S. Sen. Optimization on sparse random hypergraphs and spin glasses. Random Structures & Algorithms 53(3), 504-536 (2018), arXiv:1606.02365.
6. F. Morone, S. Rawat, D. Sels. Whither quantum advantage? New classical lower bounds for Max-Cut on large-girth 3-regular graphs. arXiv:2610.17236, 2026.
