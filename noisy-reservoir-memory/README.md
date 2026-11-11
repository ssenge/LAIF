# Noisy reservoirs: a compressing repetition memory has memory exponent ln 2 · q²/(1 − q²), above α_q

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

A classical reservoir already beats the rate α_q. The repetition reservoir of [1] uses r fresh qubits per step to rewrite all r copies. The reservoirs below instead keep r ≫ k copies and use the k − 2 fresh qubits only to remove the information in the error pattern, as much as fits.

- **Theorem 2** (asymptotic): lim inf_{k→∞} (1/k) ln W_{q,k}(ε) ≥ γ_q = ln 2 · q²/(1 − q²) for every 0 < q < 1 and 0 < ε < 1. Since α_q ≤ q²/(2(1 − q²)), this gives γ_q ≥ 2 ln 2 · α_q ≈ 1.39 α_q. The ratio between the upper exponent β_q ln 2 of [1] and the lower exponent drops from β_q ln 2/α_q to at most (1 + q²)/(q(1 − q)).
- **Theorem 1** (exact, finite k): a variant with a class-preserving map has a memory depth that is computable exactly from a random walk on h + 1 states. At finite k its values are larger still (table).

| q | α_q (repetition) | γ_q (Theorem 2) | growth per qubit in the table (Theorem 1) | upper exponent β_q ln 2 of [1] |
|---|---|---|---|---|
| 0.5 | 0.144 | 0.231 | 0.29 to 0.34 | 1.155 |
| 0.9 | 0.830 | 2.955 | 5.5 to 6.9 | 59.4 |

**The reservoir.** Take r memory qubits (r odd, h = (r − 1)/2) and k = k′ + 2 input qubits. The input qubits are reinitialised in |c⟩|b⟩|0^{k′}⟩, where c = 1 means "store the bit b" and c = 0 means "keep". All states stay diagonal, so every qubit is a classical bit that flips with probability p = (1 − q)/2 per step. The fixed unitary is a permutation of basis states:
1. *Decode.* Read the memory string x as its majority m and its error pattern e = x ⊕ m^r, of weight at most h.
2. *Compress.* Fix an injective map e ↦ (e′, g), with g ∈ {0, 1}^{k′}, that sends every pattern of weight w to a pattern e′ of weight f(w) ≤ w. The function f is chosen greedily: class w goes to the smallest class v whose remaining capacity, C(r, v) 2^{k′} minus what earlier classes use, holds its C(r, w) patterns. Write g into the k′ fresh qubits, which are discarded at the next step.
3. *Write or keep.* If c = 0, set the memory to m^r ⊕ e′. If c = 1, set it to b^r ⊕ e′ and move m into the qubit that held b. This costs one bit, not r bits.

**Theorem 1 (class map).** Let λ_{r,k′} = Σ_w π(w) F(w), where π is the stationary distribution of the error weight w ≤ h (relative to the majority) and F(w) is the probability that one step moves more than h copies away from the current majority. Then the reservoir has memory depth

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

### Theorem 2: the asymptotic exponent

**Index compression.** Use the same reservoir, but in step 2 order all patterns of weight at most h by weight, with a fixed order inside each weight, and number them i = 0, …, 2^{r−1} − 1. Map the pattern with index i to e′ = the pattern with index ⌊i/2^{k′}⌋ and g = i mod 2^{k′}. This is a bijection onto {0, …, 2^{r−1−k′} − 1} × {0, 1}^{k′} (k′ ≤ r − 1). So after every step the error weight is at most

v(r, k′) = min{v : Σ_{u≤v} C(r, u) ≥ 2^{r−1−k′}}.

**Lemma 3.** In every step the majority flips with probability at most F* = P(v − X + Y > h), where v = v(r, k′), X ~ Bin(v, p) and Y ~ Bin(r − v, p) are independent. Hence W(ε) ≥ (1 − ε)/(2F*).

*Proof.* The weight after noise is a sum over copies: a wrong copy stays wrong with probability 1 − p, a correct copy becomes wrong with probability p. For p < ½ the first is stochastically larger, so the weight after noise is stochastically increasing in the weight before it. The weight before noise is at most v, which gives the first claim at every step and for every history. The bias argument of Theorem 1, with the union bound over t steps, gives the second. ∎

*Proof of Theorem 2.* Fix 0 < κ < 1, let k′ = k − 2 and r the odd integer next to k′/κ. Let s_κ < ½ solve h₂(s_κ) = 1 − κ, with h₂ the binary entropy in bits.
1. *The weight bound.* For v ≤ r/2, C(r, v) ≥ 2^{r h₂(v/r)}/(r + 1) and Σ_{u≤v} C(r, u) ≤ 2^{r h₂(v/r)}. So v(r, k′)/r → s_κ as k → ∞.
2. *The tail bound.* For every θ ≥ 0, F* ≤ exp(−[θ(h + 1 − v) − (r − v) ln(1 − p + p e^θ) − v ln(1 − p + p e^{−θ})]). Hence (1/r) ln(1/F*) ≥ Ψ(v/r) − o(1), with

   Ψ(s) = sup_{θ≥0} [θ(½ − s) − (1 − s) ln(1 − p + p e^θ) − s ln(1 − p + p e^{−θ})],

   which is continuous and decreasing on [0, ½).
3. *Combining.* With Lemma 3 and r/k → 1/κ, lim inf (1/k) ln W ≥ Ψ(s_κ)/κ for every κ.
4. *The limit κ → 0.* Write s = ½ − u. The logarithmic moment function in the bracket has slope 2pu and curvature p(1 − p) at θ = 0, so Ψ(½ − u) = (1 − 2p)²u²/(2p(1 − p)) + O(u³) = 2q²u²/(1 − q²) + O(u³). Also h₂(½ − u) = 1 − (2/ln 2)u² + O(u⁴), so u² = (ln 2/2)κ + O(κ²) at s_κ. Hence Ψ(s_κ)/κ → ln 2 · q²/(1 − q²) = γ_q.

Taking the supremum over κ proves the theorem. The bound γ_q ≥ 2 ln 2 · α_q follows from ln(1/(1 − x)) ≤ x/(1 − x) with x = q². For the ratio to the upper exponent, β_q/(q²/(1 − q²)) = (1 + q²)/(q(1 − q)). ∎

For example, at q = 0.9 and κ = 0.05 the exact value (1/k) ln(1/F*) is 2.09, 2.17 and 2.19 at k = 50, 200 and 400, against the limit Ψ(s_κ)/κ = 2.21 (check 5).

## Remarks

- *Why r ≫ k helps.* Noise injects about r h₂(p) bits of entropy per step into r copies (h₂ is the binary entropy), and k′ fresh qubits remove k′ bits. For large r the error weight settles at a typical fraction well below ½, where compression removes as much entropy as noise adds. A majority flip then needs a large deviation over one or several steps, and its cost grows with r. Writing κ = k′/r, a large-deviation computation (`sim/ldp.py`) gives an exponent per input qubit that increases as κ decreases: about 0.28 at q = 0.5 and above 6 at q = 0.9, as κ → 0. These are estimates, not part of Theorem 1.
- *What it means for the open problem.* The lower exponent of [1] is the exact rate of the majority vote. The compressing reservoirs keep the majority vote but use the fresh qubits more efficiently, and by Theorem 2 the exponent of the best reservoir is at least γ_q > α_q. They are classical, so a quantum code is not needed to beat α_q. Whether quantum codes do better still is open, and so is the remaining factor (1 + q²)/(q(1 − q)) between the exponents.

## Check

`sim/check.py` (about 10 minutes) checks:
1. the class map: the capacity condition and f(w) ≤ w for r ≤ 39, and explicit injective maps on bit strings for r ≤ 11;
2. an exact simulation of the full bit system for r ≤ 11, which gives the same flip rate as the weight chain;
3. λ in exact rational arithmetic for r = 41, k′ = 8, q = 0.9, against the floating-point value;
4. the table, with assertions that each value lies between the two bounds of [1];
5. the index compression bound of Theorem 2 at k = 50, 200, 400, and the limit γ_q.

The floating-point code computes stationary distributions by elimination with nonnegative sums only, with the back substitution in logarithms. `sim/ldp.py` holds the large-deviation estimate. The output is in `sim/out.txt`.

## References

1. M. Baumann, J. Stein, C. Linnhoff-Popien. The Fundamental Memory Ceiling of Noisy Quantum Reservoirs. arXiv:2610.26228 (2026).
