# Noisy reservoirs: a compressing repetition memory beats the rate α_q

Written 11 Nov 2026.

## Problem

In the model of [1], a reservoir of n qubits gets one classical input per time step. Each step:
1. it discards k input qubits and reinitialises them in an encoding state σ(u);
2. it applies a fixed unitary to all qubits;
3. it depolarises every qubit, keeping its state with probability q.

The memory depth W(ε) is the smallest L such that any two input histories agreeing on their last L inputs lead to echo states within trace distance ε.

[1, Theorem 1] shows that the largest memory depth W_{q,k}(ε) over all reservoirs is exponential in k:
- **Upper bound.** For every reservoir, W(ε) ≤ δ^{−1}⌈ln(1/(2ε))⌉, with δ^{−1} = 2^{(1+4q)/(1−q)} 2^{β_q k} and β_q = q(1 + q²)/((1 − q)(1 − q²)).
- **Lower bound.** A repetition-code reservoir with k = r + 2 input qubits has W(ε) ≥ ¼ e^{α_q(k−3)} ln(q/ε), with α_q = ½ ln(1/(1 − q²)).

Per input qubit, the two bounds grow by the factors 2^{β_q} and e^{α_q}. At q = 0.5 these are e^{1.155} and e^{0.144}; at q = 0.9 they are e^{59.4} and e^{0.83}. [1] lists closing the gap between the exponents as an open problem. It also asks whether a quantum code can beat the classical rate α_q.

## Result

A classical reservoir already beats the rate α_q. The repetition reservoir of [1] uses r fresh qubits per step to rewrite all r copies. The reservoir below instead keeps r ≫ k copies and uses the k − 2 fresh qubits only to remove the information in the error pattern, as much as fits.

**The reservoir.** Take r memory qubits (r odd, h = (r − 1)/2) and k = k′ + 2 input qubits. The input qubits are reinitialised in |c⟩|b⟩|0^{k′}⟩, where c = 1 means "store the bit b" and c = 0 means "keep". All states stay diagonal, so every qubit is a classical bit that flips with probability p = (1 − q)/2 per step. The fixed unitary is a permutation of basis states:
1. *Decode.* Read the memory string x as its majority m and its error pattern e = x ⊕ m^r, of weight at most h.
2. *Compress.* Fix an injective map e ↦ (e′, g), with g ∈ {0, 1}^{k′}, that sends every pattern of weight w to a pattern e′ of weight f(w) ≤ w. The function f is chosen greedily: class w goes to the smallest class v whose remaining capacity, C(r, v) 2^{k′} minus what earlier classes use, holds its C(r, w) patterns. Write g into the k′ fresh qubits, which are discarded at the next step.
3. *Write or keep.* If c = 0, set the memory to m^r ⊕ e′. If c = 1, set it to b^r ⊕ e′ and move m into the qubit that held b. This costs one bit, not r bits.

**Theorem 1.** Let λ_{r,k′} = Σ_w π(w) F(w), where π is the stationary distribution of the error weight w ≤ h (relative to the majority) and F(w) is the probability that one step moves more than h copies away from the current majority. Then the reservoir has memory depth

W(ε) ≥ (1 − ε)/(2λ_{r,k′}).

Both π and F come from a random walk on h + 1 states with an explicit transition matrix, so λ is computable exactly.

*Proof.*
- *The chain is exact.* Noise acts independently on the copies. The weight after noise depends only on the weight before it, and step 2 maps every pattern of weight w to weight f(w). So the error weight is a random walk on {0, …, h} whose next value depends only on the current one, with the transition from w given by the noise followed by w ↦ f(w), or w ↦ f(r − w) after a majority flip.
- *A flip has probability λ at every step.* In the echo state the error weight has the stationary distribution π. Writing a bit does not change the error weight, so after the write the weight stays stationary. Hence the majority flips with probability exactly λ at every later step.
- *The bias survives.* Consider two histories that differ only in the bit b written at some step, and agree afterwards on t steps of "keep". The dynamics commutes with complementing all copies, so the majority equals b exactly when the number of flips so far is even. The majority readout therefore distinguishes the two echo states with bias at least 1 − 2P(some flip in t steps) ≥ 1 − 2tλ. The trace distance is at least this bias, so W(ε) > t whenever 1 − 2tλ > ε. ∎

**Values.** The table gives ln(1/λ) for the best r found (r ≤ 2400), and ln W(0.01) from Theorem 1, against both bounds of [1].

| q | k | r | ln(1/λ) | ln W(0.01), Theorem 1 | ln W(0.01), lower bound of [1] | ln W(0.01), upper bound of [1] |
|---|---|---|---|---|---|---|
| 0.9 | 5 | 1537 | 17.20 | 16.49 | 1.78 | 330.4 |
| 0.9 | 10 | 2049 | 51.86 | 51.16 | 5.93 | 627.6 |
| 0.9 | 15 | 1665 | 83.16 | 82.46 | 10.08 | 924.7 |
| 0.9 | 20 | 2305 | 116.27 | 115.56 | 14.23 | 1221.8 |
| 0.9 | 30 | 1793 | 171.06 | 170.35 | 22.54 | 1816.1 |
| 0.5 | 5 | 7 | 2.16 | 1.46 | 0.27 | 11.3 |
| 0.5 | 10 | 347 | 3.85 | 3.15 | 0.98 | 17.1 |
| 0.5 | 20 | 2305 | 7.10 | 6.39 | 2.42 | 28.7 |
| 0.5 | 30 | 1793 | 10.14 | 9.44 | 3.86 | 40.2 |
| 0.5 | 40 | 1217 | 13.08 | 12.38 | 5.30 | 51.8 |

At q = 0.9 and k = 5, for example, the memory depth is at least 1.4 · 10⁷ steps.

Between consecutive rows, ln(1/λ) grows by 5.5 to 6.9 per input qubit at q = 0.9 and by 0.29 to 0.34 at q = 0.5, against α_q = 0.830 and 0.144 for the repetition reservoir. The cap r ≤ 2400 is binding at q = 0.9, so these values understate the reservoir.

## Remarks

- *Why r ≫ k helps.* Noise injects about r h₂(p) bits of entropy per step into r copies (h₂ is the binary entropy), and k′ fresh qubits remove k′ bits. For large r the error weight settles at a typical fraction well below ½, where compression removes as much entropy as noise adds. A majority flip then needs a large deviation over one or several steps, and its cost grows with r. Writing κ = k′/r, a large-deviation computation (`sim/ldp.py`) gives an exponent per input qubit that increases as κ decreases: about 0.28 at q = 0.5 and above 6 at q = 0.9, as κ → 0. These are estimates, not part of Theorem 1.
- *What it means for the open problem.* The lower exponent of [1] is the exact rate of the majority vote. The compressing reservoir keeps the majority vote but uses the fresh qubits more efficiently, so the exponent of the best reservoir is strictly larger than α_q. The reservoir is classical, so a quantum code is not needed to beat α_q. Whether quantum codes do better still is open.

## Check

`sim/check.py` (about 5 minutes) checks:
1. the class map: the capacity condition and f(w) ≤ w for r ≤ 39, and explicit injective maps on bit strings for r ≤ 11;
2. an exact simulation of the full bit system for r ≤ 11, which gives the same flip rate as the weight chain;
3. λ in exact rational arithmetic for r = 41, k′ = 8, q = 0.9, against the floating-point value;
4. the table, with assertions that each value lies between the two bounds of [1].

The floating-point code computes stationary distributions by elimination with nonnegative sums only, with the back substitution in logarithms. `sim/ldp.py` holds the large-deviation estimate. The output is in `sim/out.txt`.

## References

1. M. Baumann, J. Stein, C. Linnhoff-Popien. The Fundamental Memory Ceiling of Noisy Quantum Reservoirs. arXiv:2610.26228 (2026).
