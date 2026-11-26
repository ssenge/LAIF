# Quantum algorithm for Pigeonhole Equal Subset Sum

Written 26 Nov 2026.

**Problem.** Given positive integers w_1, …, w_n with w_1 + ⋯ + w_n < 2^n − 1, find two different sets A, B ⊆ [n] with w(A) = w(B), where w(S) = Σ_{i∈S} w_i. There are 2^n sets and at most 2^n − 1 sums, so a solution always exists. The problem was introduced in [1] and lies in the class PPP. O*(·) hides factors polynomial in n.

**Memory model.** Quantum circuits with quantum random access to quantum memory (QRAQM): a gate reads or writes one cell of an array of m qubits, addressed in superposition, in time polylogarithmic in m. Classical tables written once and read in superposition (QRACM) are a special case. The walk of Lemma 2 needs QRAQM.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Pigeonhole Equal Subset Sum, worst case | classical O*(2^{n/3}) [3]; quantum O*(2^{2n/5}) with QRAQM [4, Theorem 6.3]; quantum O*(2^{2n/7}) with QRAQM, implied by [3] and [4] (Remark 3) | quantum O*(2^{3n/11}) ⊆ O(2^{0.2728n}) with QRAQM | Claim; exponent arithmetic and the counting bounds checked by scripts |

Searching all 2^n sets for a collision with element distinctness [5] takes O*(2^{2n/3}). In [8] it is noted that no algorithm faster than O*(2^{n/3}) was known for this problem, even in the quantum setting. On random instances a classical algorithm runs in O*(2^{n/4}) [9]; the bound here is for every instance.

## 1. Tools from earlier work

Write f_t(u) for the number of sets S with u(S) = t, for integers u_1, …, u_ℓ, and F(u) = Σ_t max(0, f_t − 1). A solution exists exactly when F ≥ 1.

- **Reduction [3, Lemmas 8 to 10].** We may assume w_1 < ⋯ < w_n and w([i]) ≥ 2^i − 1 for i < n (otherwise a shorter prefix is an instance). Let k satisfy 2^k ≤ F(w) < 2^{k+1}. A set 𝒟 of at most 200n⁵ pairs (X, Y) of subsets of {k+1, …, n} can be computed in poly(n) time, such that for one of them the instance W_{X,Y} = (w_1, …, w_k, w(X) − w(Y)) (without the last entry if X = Y) has F(W_{X,Y}) ≥ Δ := 2^{2k−n}/(200n⁵). Every solution of W_{X,Y} gives a solution of w in poly(n) time.
- **Small F [2, Lemma 4].** If 2^{k+1} ≤ 2^n/(3n²), the instance is solved deterministically in O*(2^{k/2}) time.
- **Bins [4, Theorem 3.5].** For a prime p and integers u_1, …, u_ℓ, a table of the sizes |T_r| of the bins T_r = {S : u(S) ≡ r (mod p)} is built in O(ℓ²p) time. With read access to it, the i-th set of T_r in a fixed order is computed in O(ℓ²) time, also in superposition.
- **Variable-time search [7].** Among P items, where checking item r takes a known time t_r, a marked item is found with bounded error in time Õ(√(Σ_r t_r²)). If G items are marked, applying it to a uniformly random subset of ⌈P/G⌉ items gives expected time Õ(√(Σ_r t_r²/G)) and a marked item with constant probability.
- **Quantum walks [6].** On the Johnson graph J(T, R), with spectral gap Ω(1/R), a marked vertex is found in time O*(S + ε^{−1/2}(√R U + C)), where ε is the fraction of marked vertices, S is the setup cost, U the update cost and C the checking cost.

## 2. Two lemmas

**Lemma 1 (bins of a random prime).** Let u_1, …, u_ℓ be integers with ℓ ≤ n + 1 and all subset sums at most 2^{n+2} in absolute value, N₀ = 2^ℓ, and let p be a uniform prime in [P, 2P].

(a) E_p Σ_r |T_r|² ≤ Σ_t f_t² + c n N₀²/P for an absolute constant c.

(b) If Z is a set of at most P/(c′ n) distinct subset sums, then with probability at least 3/4 the residues of Z mod p take at least |Z|/2 values.

*Proof.* Σ_r |T_r|² counts the ordered pairs (S, S′) with u(S) ≡ u(S′) (mod p). Pairs with equal sums give Σ_t f_t². A nonzero difference z has |z| ≤ 2^{n+3}, so at most (n + 3)/log₂ P primes in [P, 2P] divide it, out of at least P/(2 ln 2P), which gives probability O(n/P) and (a). For (b), the expected number of pairs in Z with equal residues is at most |Z|² · O(n/P) ≤ |Z|/8 for c′ large enough, so by Markov's inequality at most |Z|/2 of them occur with probability at least 3/4, and each such pair removes at most one residue. ∎

**Lemma 2 (collision walk in one bin).** Let a list of T items be given, where the i-th item and its value are computed in O*(1) time, and suppose κ ≥ 1 distinct values are each taken by at least h ≥ 2 items, with κh ≤ T. Then two items with the same value are found with bounded error in time O*((T²/(κh²))^{1/3}), with QRAQM.

*Proof.* For each of the κ values keep exactly h of its items; this only lowers the marked fraction below. Let R = ⌊(1/8)(T/(h√κ))^{2/3}⌋. If R < 2, then T²/(κh²) = O(1), a uniform pair of items collides with probability at least κh²/(4T²) = Ω(1), and Grover search over pairs takes O(1) steps. Otherwise walk on J(T, R), storing the values of the chosen items in a dictionary with insertion, deletion and lookup in O*(1) [5]. A vertex is marked if it holds two items with equal value, which the dictionary keeps track of, so S = O*(R) and U = C = O*(1).

Fix one value and let X be the number of its h items in a uniform R-set. Put x = hR/T, so x ≤ (1/8)(h/(κT))^{1/3}, hence x ≤ 1/8 and κx² ≤ 1/64, since κh ≤ T and h ≤ T. From 1[X ≥ 2] ≥ C(X, 2) − 2C(X, 3), E C(X, 2) = C(h, 2)R(R − 1)/(T(T − 1)) ≥ x²/8 (for h, R ≥ 2) and E C(X, 3) ≤ x³/6, we get Pr[X ≥ 2] ≥ x²/8 − x³/3 ≥ x²/16. For two values a ≠ b, Pr[X_a ≥ 2, X_b ≥ 2] ≤ E[C(X_a, 2)C(X_b, 2)] = C(h, 2)² R^{(4)}/T^{(4)} ≤ x⁴/4, with falling factorials R^{(4)} and T^{(4)}. By the Bonferroni inequality the marked fraction is ε ≥ κx²/16 − κ²x⁴/8 ≥ κx²/32. The cost is O*(R + ε^{−1/2}√R) = O*(R + T/(h√(κR))) = O*(R) = O*((T²/(κh²))^{1/3}). Both moment bounds are also checked exactly in [`sim/hypergeom.py`](sim/hypergeom.py). ∎

## 3. Theorem 1

**Theorem 1.** With QRAQM, Pigeonhole Equal Subset Sum can be solved with bounded error in time O*(2^{3n/11}).

**Algorithm.** For every k ∈ {0, …, n − 1}, every (X, Y) ∈ 𝒟 and every j ∈ {0, …, n + 1}, run the following on u = W_{X,Y}, with ℓ ≤ k + 1 entries, N₀ = 2^ℓ, h = 2^j + 1 and m = ⌈Δ/(2^{j+1}(n + 1))⌉, each with its time budget. Check every output and stop at the first correct one. Also run the small-F algorithm of [2] whenever it applies.

1. *Heavy case.* Grover search over pairs (S, S′) of subsets of [ℓ] for S ≠ S′ with u(S) = u(S′), with the budget O(√(P/n)).
2. *Bins.* Draw a prime p ∈ [P, 2P], build the table of bin sizes (O*(P) time) and run variable-time search over r ∈ ℤ_p. Checking bin r runs Lemma 2 on T_r with parameters (κ, h), for one of the two settings (A) κ = ⌈m/(4P)⌉ when P ≤ 2m, or (B) κ = 1, and with time t_r = O*((|T_r|²/(κh²))^{1/3}), known from the table.

**Correctness and time.** Take k with 2^k ≤ F(w) < 2^{k+1}, the pair of the reduction, so F(u) ≥ Δ, and j with m_j := |{t : f_t ≥ h}| ≥ m, which exists by [2, Lemma 8].

- If Σ_t f_t² ≥ c″ n N₀²/P, a uniform pair (S, S′) is a solution with probability at least (Σ_t f_t² − N₀)/N₀² = Ω(n/P), and step 1 finds one in O(√(P/n)) time.
- Otherwise, by Lemma 1(a) and Markov's inequality, Σ_r |T_r|² = O(n N₀²/P) with probability at least 3/4, and then, by Hölder's inequality, Σ_r |T_r|^{4/3} ≤ N₀^{2/3}(Σ_r |T_r|²)^{1/3} = O*(N₀^{4/3} P^{−1/3}). Call a bin good if it holds κ sums each taken by at least h sets.
  - In setting (A), the proof of [2, Lemma 9] shows that with probability at least 0.9 over p, Ω(P/n) bins hold at least m/(4P) such sums.
  - In setting (B), Lemma 1(b) applied to min(m_j, P/(c′ n)) of these sums gives at least min(m, P/(c′ n))/2 good bins with probability at least 3/4.

  With G good bins, variable-time search costs Õ(√(Σ_r t_r²/G)) = O*((κh²)^{−1/3} N₀^{2/3} P^{−1/6} G^{−1/2}). Since mh ≥ Δ/(2(n + 1)) and h ≥ 2, the time of step 2 is
  - (A), for P ≤ 2m: O*(P + N₀^{2/3} P^{−1/3} Δ^{−1/3});
  - (B), for P ≥ c′ n m: O*(P + N₀^{2/3} P^{−1/6} Δ^{−1/2}).

With N₀ ≤ 2^{k+1} and Δ = 2^{2k−n}/poly(n), write exponents in units of n with k = κ₀n.

- κ₀ ≤ 6/11: the small-F algorithm of [2] takes 2^{k/2} ≤ 2^{3n/11}. (If [2] does not apply, then 2^{k+1} > 2^n/(3n²), so κ₀ is close to 1 and the case κ₀ ≥ 5/8 below covers it.)
- 6/11 ≤ κ₀ ≤ 5/8: setting (B) with P = 2^{(3n−2k)/7}, which is at least c′ n m since (3n − 2k)/7 ≥ 2k − n for κ₀ ≤ 5/8, takes 2^{(3n−2k)/7} ≤ 2^{3n/11}.
- κ₀ ≥ 5/8: setting (A) with P = min(2^{n/4}, 2m). In the time bound of (A) before using mh ≥ Δ/(2(n + 1)), the second term is (mh²)^{−1/3} N₀^{2/3} P^{−1/3}. For P = 2^{n/4} it is at most 2^{(2k − (2k − n))/3 − n/12} = 2^{n/4} up to poly(n). For P = 2m < 2^{n/4} it is at most (mh)^{−2/3} N₀^{2/3}, so 2^{2(n−k)/3} ≤ 2^{n/4} up to poly(n). Either way the time is O*(2^{n/4}) ⊆ O*(2^{3n/11}).

The worst case is k = 6n/11, where the first two bounds meet at 2^{3n/11}. The guesses of k, (X, Y) and j are polynomially many, and every output is checked, so the total time is O*(2^{3n/11}) and the error probability is bounded. ∎

**Remark 3 (the implied bound 2^{2n/7}).** Using one random bin with pair finding [4, Theorem 2.8] inside Lemma 6 of [3], in place of its subsampling, is setting (A) alone. Together with the small-F algorithm of [2] it gives O*(2^{2n/7}) with QRAQM, with the worst case at k = 4n/7. What Theorem 1 adds is setting (B): more bins than frequent sums (P > m), with amplitude amplification over the bins by variable-time search, made possible by the second moment of the bin sizes and the heavy case.

## 4. Scripts

In [`sim/`](sim/), run with Python 3:

- [`exponents2.py`](sim/exponents2.py) optimizes the exponent of every branch over a grid of k and P and asserts the worst cases: 1/2 for the classical branch alone, 2/7 for Remark 3, and 3/11 at k = 6n/11 for Theorem 1. It also shows that a classical table with Grover search in one bin (QRACM only) gives no exponent below 1/3.
- [`hypergeom.py`](sim/hypergeom.py) checks the two hypergeometric bounds of Lemma 2 exactly for T ≤ 400 and h ≤ 11.
- [`check_reduction.py`](sim/check_reduction.py) checks, on 60 instances with 8 to 14 integers and exact subset-sum tables, the structure bound −iF ≤ w_i − 2^{i−1} ≤ F of [3, Lemma 4], the bound |𝒟| ≤ 200n⁵, the existence of (X, Y) ∈ 𝒟 with F(W_{X,Y}) · |𝒞| ≥ F(w), the second-moment bound of Lemma 1(a) averaged over primes, and the count of distinct residues of Lemma 1(b).

## 5. Limits

- The bound needs QRAQM. With QRACM only, the methods here give no exponent below 1/3.
- The algorithm finds one solution with bounded error. It is not deterministic.
- Not formalized: the algorithm, Lemmas 1 and 2, and the reduction of [3]. The scripts check the exponent arithmetic, the hypergeometric bounds, and the reduction lemmas on small instances.

## References

1. C. H. Papadimitriou. On the complexity of the parity argument and other inefficient proofs of existence. Journal of Computer and System Sciences 48(3) (1994).
2. C. Jin, H. Wu. A faster algorithm for pigeonhole equal sums. ICALP 2024, arXiv:2403.19117.
3. C. Jin, R. Williams, S. Zhang. New algorithms for Pigeonhole Equal Subset Sum. ESA 2025, LIPIcs 351, 86.
4. J. Allcock, Y. Hamoudi, A. Joux, F. Klingelhöfer, M. Santha. Classical and quantum algorithms for variants of Subset-Sum via dynamic programming. ESA 2022, arXiv:2111.07059.
5. A. Ambainis. Quantum walk algorithm for element distinctness. SIAM Journal on Computing 37(1) (2007), arXiv:quant-ph/0311001.
6. F. Magniez, A. Nayak, J. Roland, M. Santha. Search via quantum walk. SIAM Journal on Computing 40(1) (2011), arXiv:quant-ph/0608026.
7. A. Ambainis. Quantum search with variable times. Theory of Computing Systems 47(3) (2010), arXiv:quant-ph/0609168.
8. N. Chukhin, A. S. Kulikov, M. Levitskii, I. Mihajlin. Improved quantum algorithms for Subset Sum and k-SUM. ECCC TR26-135 (2026).
9. D. Bhati, P. Dutta, A. Joux, M. S. Rajasree, K. Węgrzycki. Pigeonhole Equal Subset Sum: subexponential algorithm, tight lower bounds, and average-case analysis. arXiv:2610.31056.

## Use of AI

The algorithm, the analysis, the scripts and this text were produced with the help of Claude Opus 5.5.
