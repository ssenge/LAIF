# k-distinctness: queries versus success probability

Written 5 Nov 2026.

## Result

[1] proves the tight bound Ω(n^{3/4 − 1/(4(2^k − 1))}) for k-distinctness with bounded error, for alphabets of size Ω(n²). Its proof also bounds the success probability of an algorithm with T queries. On the hard inputs of [1, Section 6.1] (one k-block and Θ(n) blocks of each size 1, ..., k − 1), every T-query algorithm succeeds with probability

    O(1/n + T^e / n^{e − 1}),   e = 4 − 2^{2−k}.

For k = 3 the second term is T^{7/2}/n^{5/2}. [1, Section 7] asks for a tight trade-off between queries and success probability. This folder shows that the second term is attained:

| k | Range of T where the bound of [1] is attained | Algorithm |
|---|---|---|
| any k ≥ 3 | n^{1 − 2^{k−1}/(2^k − 1)} ≤ T ≤ n^{1/2} | nested Grover search, up to constant factors |
| 3 | n^{3/7} ≤ T ≤ n^{1/2} | nested Grover search, up to constant factors |
| 3 | n^{1/2} ≤ T ≤ n^{5/7} | the walk of [2] with T/√n iterations, up to polylog factors |

So for 3-distinctness the success probability with T queries is Θ̃(T^{7/2}/n^{5/2}) for all T between n^{3/7} and n^{5/7}, where n^{5/7} is the bounded-error complexity. Below the lower end of each range, the term 1/n in the bound of [1] is larger than what the algorithms achieve, and the trade-off is open.

## The argument

**Lower bound.** The bound of [1] is an average over the hard inputs, so it also bounds the success probability on the worst input. It is proved in a relaxed setting where block values need not be distinct [1, Definition 4.3], and [1, Proposition 4.4] transfers it to actual inputs when q = Ω(n²).

**Nested Grover search.** Stage 1 queries r_1 = T random positions. For l = 2, ..., k − 1, stage l holds a list of r_{l−1} equal (l − 1)-tuples and runs BBHT search [3] repeatedly, with T queries in total, for positions that extend one of them. On the hard inputs Θ(r_{l−1}) positions are marked, so each search costs Θ(√(n/r_{l−1})) and the stage finds r_l = Θ(T √(r_{l−1}/n)) of them. A fixed extension of the tuple of the k-block is among them with probability Θ(r_l/r_{l−1}). Stage k runs Grover search with T iterations for a position that extends a listed (k − 1)-tuple to a k-tuple. Only the tuple of the k-block has such an extension, so this succeeds with probability Θ(T²/n) when T ≤ √n. In total

    Θ((r_1/n) · Π_l (r_l/r_{l−1}) · T²/n) = Θ(r_{k−1} T²/n²) = Θ(T^e / n^{e − 1}).

The range comes from three conditions: the last Grover search is not saturated (T ≤ √n), the last list is nonempty, and each search has T² r_{l−1} ≥ n. In the range the second term of [1] also exceeds 1/n.

**Partial walk for k = 3.** The algorithm of [2, Section 4] walks on sets S2 of s2 colliding pairs. A set is marked if it contains a pair of the 3-collision, so ε = Θ(s2/n). The update replaces m = s1²/n pairs with an inner element distinctness walk on sets of size s1. Setup costs Õ(s1 + s2 √(n/s1)), and one iteration of the search costs Õ(√(n s2/s1) + √n) [2, Theorems 3.3, 4.2, 4.3, 4.8]. The search alternates the checking reflection with a phase estimation reflection about the start state, as in [4], so W iterations give marked amplitude sin((2W + 1)θ) with sin²θ = ε, up to the error of the approximate reflections. Take s1 = T, s2 = T^{3/2}/√n and W = T/√n. Then the setup costs Õ(T), each iteration costs Õ(√n), and the amplitude is Θ(W √(s2/n)) = Θ(T^{7/4}/n^{5/4}). A final Grover search of cost √n finds the third index. At T = n^{5/7} these are the parameters of [2].

The partial run needs all errors to be small compared with the amplitude W√ε ≥ n^{−3/8}, not just below a constant. The setup state of [2, Theorem 4.2] is exact up to the event |H(I)| < cs1, which has probability e^{−Θ(s1)} [2, Lemma 5.5], and up to the errors of its Grover searches. Those errors, and the error of each phase estimation reflection, can be made 1/poly(n) at a polylog factor. The conditions of [2] hold: m = T²/n ≥ 1 needs T ≥ √n (for T = Θ(√n), nested Grover search gives the same value up to constants), and the spectral gap Ω(m/s2) needs m ≤ s2, which holds for T ≤ n.

## Machine check

`lean/KDistTradeoff.lean` checks the exponent arithmetic, with Lean 4.36.0-rc1 and Mathlib revision `d875a8de5222f62cf1c2fafc7984588adadc990a`. It contains no `sorry`, and its theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Exponents are of n, with T = n^τ.

- `rho_closed`: the list exponents have the closed form (2 − 2^{−l})τ − (1 − 2^{−l}).
- `nested_eq_belovs`: the success exponent of nested Grover search equals that of the bound of [1], for every k.
- `window_valid`, `belovs_ge_inv_n`: in the stated range all conditions of the nested search hold, and the second term of [1] is at least 1/n.
- `walk_k3`, `walk_k3_end`: the walk parameters for k = 3 satisfy the conditions on [1/2, 5/7] (including m ≤ s2 and the budgets for setup and iterations) and give the exponent of [1], with constant success at 5/7.

**Not machine-checked:** the lower bound of [1], the walk of [2], BBHT and Grover search.

## Numerical check

`sim/check_window.py` recomputes the exponents in exact rational arithmetic for k = 2, ..., 6 and checks that the two exponents agree across the stated range.

## References

[1] A. Belovs. Tight quantum lower bound for k-distinctness. arXiv:2604.05133, 2026.

[2] A. M. Childs, S. Jeffery, R. Kothari, F. Magniez. A time-efficient quantum walk for 3-distinctness using nested updates. arXiv:1302.7316, 2013. Merged with A. Belovs, arXiv:1302.3143, in ICALP 2013.

[3] M. Boyer, G. Brassard, P. Høyer, A. Tapp. Tight bounds on quantum searching. Fortschr. Phys. 46, 1998. arXiv:quant-ph/9605034.

[4] F. Magniez, A. Nayak, J. Roland, M. Santha. Search via quantum walk. SIAM J. Comput. 40(1), 2011. arXiv:quant-ph/0608026.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
