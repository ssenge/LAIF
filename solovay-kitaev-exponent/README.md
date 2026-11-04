# Solovay-Kitaev exponent

Minor results from a bounded attempt to improve the Solovay-Kitaev exponent. No exponent was improved; the best known remain 1.13747 for a qubit [1] and 1.44042 for general SU(d) [2]. Result 1 has a proof, checked by hand and numerically; it is not formalized in Lean, and no human has checked it. Its core is close to [3, §4.3], so it is not claimed as new. Results 2 to 4 are measurements only.

| # | Result | Status | Importance |
|---|---|---|---|
| 1 | No finite-order symmetry of the kind used in [1] exists on SU(d), d ≥ 3; on SU(2) such symmetries are half-turns | proved below | minor |
| 2 | The words of [1] stall at order 6 for d ≥ 3 | measured | minor |
| 3 | No recursion in the tested classes beats tribonacci growth | measured, heuristic search | minor |
| 4 | SU(3) has no shorter cancelling words than d = 6 up to length 22 | measured | minor |

Background: by the framework of [2], a fixed word of length L with vanishing order r gives any exponent above max(1, log_r L). So the question is how short words of high order can be. The words of [3] gain a factor φ = 1.618 in order per doubling of length, on any group. The gain of [1] is x₀ = 1.839, on SU(2) only. Exponent 1 would need a factor 2.

## 1. No finite-order symmetry

**Definition.** Let H ≤ F₂ and let φ be an automorphism of H of finite order. A realization of φ on SU(d) assigns to each input (g, h) an automorphism θ of SU(d) with θ(w(g, h)) = φ(w)(g, h) for all w in H. Here θ is conjugation by J, or for d ≥ 3 possibly g → J ḡ J⁻¹.

**Theorem.** Let H be nonabelian. (a) For d ≥ 3, if φ ≠ id then φ has no realization on SU(d). (b) On SU(2), a realized φ has φ² = id, and J is a pure quaternion, that is, a half-turn.

The inputs can be restricted to any set with nonempty interior, because the trace identities used continue analytically. So working near the identity does not escape.

In outline:
1. On SU(2), J lies in the quaternion algebra D = (t₁² − 4, κ − 2) over K = R(t₁, t₂, t₃), with t₁ = tr g, t₂ = tr h, t₃ = tr gh, κ = tr[g, h]. J^m central then gives a root of unity J/J̄. If its order is at least 3, D contains i, so D splits over C(t₁, t₂, t₃). A residue computation along κ = 2 shows that it does not split.
2. Restricting to the d-dimensional irreducible representation of SU(2) carries a realization on SU(d) down to SU(2), so φ² = id.
3. For an involution, w = v φ(v)⁻¹ (inner) or w = v φ(v) (outer) has tr w real on SU(d)². This contradicts Borel's theorem that nontrivial word maps are dominant, since tr M = tr M⁻¹ fails generically for d ≥ 3.

**Not ruled out:** symmetries that hold only modulo high order, one-way maps H → H', infinite-order φ (an example exists on SU(2)), thin sets of inputs (such as SO(3)² in SU(3)), and identities with no symmetry behind them, such as Lie polynomial identities of sl_d. So this excludes the mechanism, not exponents below 1.44 for SU(3).

## 2. The words of [1] stall for d ≥ 3

Vanishing order of w_n(a, b) = u_n(a, bab⁻¹), exact arithmetic over F_P at random points (`sim/ccan.py`).

| n | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|---|
| d = 2 | 2 | 5 | 8 | 15 | 28 | 51 | 94 | 173 | 318 |
| d = 3, 4, 5, 8 | 2 | 5 | 6 | 6 | 6 | 6 | 6 | 6 | 6 |

The d = 2 row equals the lower bound d_n of [1] exactly. The plateau at 6 is measured for n ≤ 8, not proved.

## 3. Searches for a better recursion on the qubit

**Class.** new = ∏_m σ_m(W_{level_m}), where σ_m is one of the 8 sign patterns (half-turns and inverses) and the W are recent words. This contains the recursion of [1] and that of [3], whose gain comes from free cancellation. Lengths are exact reduced lengths in p, q. Valuations are lower bounds from treating components as independent, with exact vanishing detected by word equality.

| Run | Levels | Copies per step | Horizon, log₂ L | Beam width | Best min valuation over the chain of [1], end of run |
|---|---|---|---|---|---|
| `recursion.py` | 1 | ≤ 4 | 40 | 3000 | slope equal to tribonacci, 0.87915 |
| `mixed_L2M4.log` | 2 | ≤ 4 | 14 | 30 | 1.030 |
| `mixed_L3M4.log` | 3 | ≤ 4 | 13 | 15 | 1.030 |
| `mixed_L2M5.log` | 2 | ≤ 5 | 14 | 30 | 1.030 |

In all three mixed runs, the best valuations at length near 2^k are the d_n of [1], and the ratio and the potential do not move from log₂ L = 10 to 14 (ratio 1.029 to 1.030, ψ 2.895). The 3% gain is a constant saving from a little free cancellation: lengths 62 and 990 in place of 64 and 992. The best chain is the recursion of [1] in four-copy form with a different seed.

Exact arithmetic on the replayed chain (`sim/verify_chain.py`) gives (5, 2, 3) at L = 4, up to (1979, 1076, 1661) at L = 3960, which equals the search's lower bounds at every level from L = 248 on, where they were compared.

**Limits.**
- The beam search is heuristic, and the width is small, so a recursion that loses for several steps before gaining could be pruned.
- Only short products were tried. The run with 6 copies hit its time limit before the full library finished.
- Components are treated as independent, so extra cancellation from relations between levels is not credited, although the exact check agreed on the best chain.
- Frame changes, where a new pair of words brings a new half-turn, are covered only as far as short products reach them. A hand estimate for one restart gives 3.24 against 3.38 in the best case. It was not checked by program, and other seeds were not tried.

**Failed runs.** `sim/invalid_runs/` holds logs in which impossible valuations appeared, because exactly vanishing components looked like huge valuations and pushed the chain of [1] out of the beam. They should not be used. `mixed.py` now removes these cases by a degree bound and an exact test.

## 4. Short words in SU(3)

Largest vanishing order of any nontrivial word up to a given length (`sim/shortest.py`, meet in the middle over all reduced words, each record rechecked at a second random point). d = 6 stands in for the free group.

| length ≤ | 4 | 8 | 14 | 22 | 24 | 26 |
|---|---|---|---|---|---|---|
| d = 2 | 2 | 3 | 5 | 7 | 7 | 8 |
| d = 3 | 2 | 3 | 5 | 6 | 6 | not run |
| d = 4 | 2 | 3 | 5 | 6 | 6 | not run |
| d = 6 | 2 | 3 | 5 | 6 | not run | not run |

Values between columns equal the column to their left. SU(2) separates at length 22. These lengths are small, and identities of sl₃ may only matter at higher degree, so this is weak evidence.

## What to try first if this is reopened

For d ≥ 3, cancellation has to come from approximate symmetries or from Lie identities of sl_d, and we have no construction for either. For the qubit, a wider search, or a proof that tribonacci is optimal within the sign-flip class, which was not attempted here.

## References

1. Yehuda. arXiv:2607.15811.
2. G. Kuperberg. Breaking the cubic barrier in the Solovay-Kitaev algorithm. arXiv:2306.13158.
3. A. Elkasapy, A. Thom. On the length of the shortest non-trivial element in the derived and the lower central series. arXiv:1312.1261.
