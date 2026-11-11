# Quantum property testing of concatenations of two palindromes

Written 12 Nov 2026.

**Setting.** Σ is a finite alphabet and L_REV = {u u^r v v^r : u, v ∈ Σ⁺} is the language of concatenations of two even palindromes, where u^r is u reversed. A query returns one letter of the input x = x₀ … x_{n−1}. An ε-tester accepts every x ∈ L_REV and rejects every x that differs from each word of L_REV of length n in at least εn positions, each with probability at least 2/3.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | ε-testing L_REV | O(n^{1/3} log n / ε) quantum queries [1]; classically O(√n log n / ε) [2] and Ω(√n) [3] | O(log n / ε²) quantum queries | Claim; checked by script |
| Thm 2 | ε-testing whether y is a cyclic shift of x (x, y ∈ Σⁿ, no promise on the letters) | | O(log n / ε²) quantum queries | Claim; checked by script |

The tester reads the two palindromes as one hidden reflection of the cyclic word and finds its axis from coset states, as in the hidden subgroup problem of the dihedral group. When all letters are distinct, deciding whether y is a cyclic shift of x is that hidden subgroup problem and takes logarithmically many quantum queries [4, 5]. Here the letters are arbitrary, for example bits, and the phases of the coset states stay exact; only the distribution of the Fourier samples changes, and it equals the autocorrelation of x.

## 1. Axes

Let n be even and C = {c odd : 1 ≤ c ≤ n − 3}. Call x *symmetric about c* if x_i = x_{(c − i) mod n} for every i.

**Lemma 1.** (a) x ∈ L_REV iff x is symmetric about some c ∈ C. (b) If x is ε-far from L_REV, then Pr_i[x_i ≠ x_{(c − i) mod n}] ≥ 2ε for every c ∈ C, with i uniform.

*Proof.* (a) For x = u u^r v v^r take c = 2|u| − 1: the positions 0, …, c pair as i ↔ c − i, and the positions c + 1, …, n − 1 pair as i ↔ c − i + n. Conversely, for c ∈ C these pairings make x₀ … x_c an even palindrome of length c + 1 ≥ 2 and x_{c+1} … x_{n−1} an even palindrome of length n − c − 1 ≥ 2. (b) Every word y symmetric about c satisfies y_i = y_{c−i}, so each pair {i, c − i} with x_i ≠ x_{c−i} contains a position where x and y differ. The pairs are disjoint, so the number p_c of such pairs is at most the distance from x to y, and the claim follows from p_c ≥ εn and Pr_i[x_i ≠ x_{c−i}] = 2p_c / n. □

For odd n there is no word of L_REV of length n.

## 2. The Fourier sample

Let ω = e^{2πi/n}, f(i, 0) = x_i and f(i, 1) = x_{(−i) mod n} for (i, b) ∈ ℤ_n × {0, 1}. One sample:

1. prepare (2n)^{−1/2} Σ_{i,b} |i, b⟩|f(i, b)⟩ with one query and measure the last register, with outcome v;
2. apply the quantum Fourier transform of ℤ_n to i and measure, with outcome k;
3. measure b in the X basis or in the Y basis, chosen uniformly at random, with outcome s ∈ {±1}, and set Z = 2s or Z = 2is.

Let R(d) = Pr_a[x_a = x_{(a+d) mod n}] be the autocorrelation of x, with a uniform. Then R(0) = 1 and R(−d) = R(d).

**Lemma 2.** If x is symmetric about c, then conditioned on (v, k) the qubit b is (|0⟩ + ω^{−kc}|1⟩)/√2, so E[Z | k] = ω^{−kc}, and the outcome k satisfies E[ω^{kd}] = R(d) for every d.

*Proof.* Let A = {a : x_a = v} and Â(k) = Σ_{a∈A} ω^{ka}. Symmetry gives x_{−j} = x_{j+c}, so {j : x_{−j} = v} = A − c and the state after step 1 is proportional to Σ_{a∈A} (|a, 0⟩ + |a − c, 1⟩). The Fourier transform turns it into a multiple of Σ_k Â(k) |k⟩ (|0⟩ + ω^{−kc}|1⟩). Hence Pr[v, k] = |Â(k)|² / n² and Σ_k Pr[v, k] ω^{kd} = n^{−2} Σ_{a,a′∈A} Σ_k ω^{k(a − a′ + d)} = n^{−1} |{a ∈ A : a + d ∈ A}|. Summing over v gives R(d). The X and Y measurements of (|0⟩ + e^{iθ}|1⟩)/√2 have means cos θ and sin θ, so E[Z] = e^{iθ}. □

**Lemma 3.** If x is symmetric about c, then Pr_i[x_i ≠ x_{(c′ − i) mod n}] = 1 − R(c − c′) for every c′.

*Proof.* x_{c′−i} = x_{c−(c′−i)} = x_{i + (c − c′)}. □

## 3. The tester

**Theorem 1.** For every finite alphabet, L_REV has an ε-tester with T + 2m quantum queries, T = ⌈32 ln(6n) / ε²⌉ and m = ⌈32 / ε⌉, so O(log n / ε²) queries.

*Algorithm.* Reject if n is odd or n < 4. Take T samples (k_t, Z_t), let score(c′) = T^{−1} Σ_t Re(ω^{k_t c′} Z_t) for c′ ∈ C, and let c* maximize the score. Draw m uniform positions i, count the mismatches M = |{i : x_i ≠ x_{(c* − i) mod n}}|, and accept iff M < 1.5 εm.

*Proof.* Let x be symmetric about c ∈ C. Every term Re(ω^{k c′} Z) lies in [−2, 2] and by Lemma 2 has mean Re E[ω^{k(c′ − c)}] = R(c′ − c). By the Hoeffding bound and a union bound over the at most n/2 axes in C, all scores lie within ε/2 of their means, except with probability n e^{−Tε²/32} ≤ 1/6. Then R(c* − c) ≥ score(c*) − ε/2 ≥ score(c) − ε/2 ≥ 1 − ε, so the mismatch rate of c* is at most ε by Lemma 3, and the Chernoff bound gives Pr[M ≥ 1.5 εm] ≤ e^{−εm/12} ≤ e^{−8/3} < 1/10. The error is below 1/6 + 1/10 < 1/3.

Let x be ε-far from L_REV. Whatever the samples, c* ∈ C, so its mismatch rate is at least 2ε by Lemma 1(b), and Pr[M < 1.5 εm] ≤ e^{−εm/16} ≤ e^{−2} < 1/6. □

The bound concerns queries. The search for c* as written takes O(nT) classical time.

**Theorem 2.** Given x, y ∈ Σⁿ, accepting if y_i = x_{(i+s) mod n} for some s and rejecting if y differs from every cyclic shift of x in at least εn positions takes O(log n / ε²) quantum queries: T = ⌈128 ln(12n) / ε²⌉ samples and m = ⌈64 / ε⌉ checked positions.

*Proof.* Use f(i, 0) = x_i and f(i, 1) = y_i. If y_i = x_{i+s}, then {j : y_j = v} = A − s and Lemmas 2 and 3 hold with s in place of c and every s′ ∈ ℤ_n as a candidate, where the mismatch rate of s′ is 1 − R(s − s′). Estimate every score within ε/4 (failure at most 2n e^{−Tε²/128} ≤ 1/6), so the chosen shift has mismatch rate at most ε/2, and accept iff fewer than 0.75 εm of the m checked positions mismatch. The Chernoff tails are e^{−εm/24} ≤ e^{−8/3} < 1/10 for members and e^{−εm/32} ≤ e^{−2} < 1/6 for inputs ε-far from every shift. □

## Scripts

`sim/check_tester.py` computes the measurement statistics of Section 2 exactly, from the Fourier transforms of the level sets, and simulates the testers with them.

- On yes-instances (random, sparse and periodic, n up to 398, alphabets of size 2 and 3) and on cyclic shifts, the qubit phase is exact. The mean of the score terms, taken over the measured X and Y outcomes, equals R(c′ − c) to 10⁻⁹.
- The tester of Theorem 1, with its T and m, for ε = 0.1, made no error on 60 yes-instances with n ∈ {64, 256, 1024, 4096} and 60 inputs at distance at least εn from L_REV, with the distance computed exactly. It also accepted all 40 yes-instances that have a second axis in C with a mismatch rate between 1.25ε and 2.2ε.
- The tester of Theorem 2 was correct on 20 shifted pairs and 20 pairs that are ε-far from every shift.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. K. Khadiev, D. Serov. Quantum property testing algorithm for the concatenation of two palindromes language. arXiv:2406.11270, 2024.
2. M. Parnas, D. Ron, R. Rubinfeld. Testing membership in parenthesis languages. Random Structures & Algorithms 22(1), 98–138, 2003.
3. N. Alon, M. Krivelevich, I. Newman, M. Szegedy. Regular languages are testable with a constant number of queries. SIAM Journal on Computing 30(6), 1842–1862, 2001.
4. M. Ettinger, P. Høyer, E. Knill. The quantum query complexity of the hidden subgroup problem is polynomial. Information Processing Letters 91(1), 43–48, 2004.
5. A. Belovs, A. Rosmanis. Quantum lower bounds for tripartite versions of the hidden shift and the set equality problems. arXiv:1712.10194, 2017.
