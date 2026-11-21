# Frequency moments and integer-order Rényi entropy: quantum query bounds

Written 21 Nov 2026.

**Setting.** The input is a string a_1, …, a_N over an alphabet [M], and a query returns one symbol. If symbol j occurs n_j times, the k-th frequency moment is F_k = Σ_j n_j^k. The task is to output an estimate of F_k within relative error ε, with probability at least 2/3 [1]. In the related distribution setting, a unitary U with U|0⟩ = Σ_j √p_j |j⟩|ψ_j⟩ gives purified query access to a distribution p on [n] (U, its inverse and their controlled versions can be applied), and the task is to estimate the Rényi entropy H_k(p) = log(Σ_j p_j^k)/(1 − k) within additive error ε [2, 3].

| | Problem | Previous best bound, constant ε | This folder | Status |
|---|---|---|---|---|
| Thm 1 | F_k for fixed k ≥ 3, string queries | lower Ω(N^{max(1/3, 1/2 − 1/(2k))}) [1]; upper Õ(N^{u_k}) with u_3 = 4/9, u_4 = 1/2, implied by [2] | Ω(N^{a_k}) with a_k = (2^{k−1} − 1)/(2^k − 1), for relative error below a constant c_k > 0; implied by [4, Thm 2.6] with the instances of [5] | Claim; checked by script |
| Cor 2 | H_k for fixed k ≥ 3, purified access | lower Ω(n^{1/2 − 1/(2k)}) [9, Thm 14], [3, Thm 2.9]; upper Õ(n^{u_k}) [2] | Ω(n^{a_k}) for additive error below a constant c′_k > 0 | Claim |
| Thm 3 | F_k for fixed k ≥ 2 on strings whose multiplicities are at most a constant B ≥ 2 | upper Õ(N^{u_k}) implied by [2] (all strings) | O(N^{a_k}) for every constant relative error ε; with Theorem 1, Θ(N^{a_k}) for k ≥ 3, B ≥ k and small constant ε | Claim; checked by simulation |

For k = 3 the exponent is a_3 = 3/7, between the previous lower exponent 1/3 and the upper exponent 4/9. For k = 4 it is 7/15 (previously 3/8, upper 1/2), and for k = 5 it is 15/31. The exponent a_k is also the exponent of k-distinctness testing [4, Cor. 5.1] and of finding k-collisions in random strings [6]. Theorem 3 shows that it is the exponent of F_k on strings of bounded multiplicity, which include the instances of Theorem 1. The bounds of [2] are stated for purified access and apply to strings through the simulation in the proof of Corollary 2. Tight bounds for finding one r-collision in a function with prescribed class sizes are given in [10].

## Instances

The construction follows [4, Section 2.1]. A positive frequency statistic is a random variable X on [A] = {1, …, A}, with mean μ = E[X]. Its mean-one version Z on {0} ∪ [A] has Pr[Z = a] = Pr[X = a]/μ for a ∈ [A] and Pr[Z = 0] = 1 − 1/μ, so E[Z] = 1. For N ≥ 2, the input distribution Π_N draws m = ⌊N/2⌋ independent copies z_1, …, z_m of Z. If z = Σ_i z_i ≤ N, the string gets one fresh symbol of multiplicity z_i for each nonzero z_i and N − z further symbols that occur once each. Otherwise it is a string of N distinct symbols. Positions and symbol names are uniformly random.

Let X_0, X_1 be the positive frequency statistics on [k] from [5, Section 2.2], as used in [4, Cor. 5.1]. They satisfy E[X_1^j]/E[X_0^j] = E[X_1]/E[X_0] for j = 1, …, k − 1, Pr[X_0 = k] = 0 and Pr[X_1 = k] > 0. By [4, Prop. 2.4], the mean-one versions satisfy E[Z_0^j] = E[Z_1^j] for j = 0, …, k − 1. Write Π_b for the input distribution of X_b.

## The moment gap

**Lemma 1.** Let ν be a real function on {0, …, k} with Σ_a ν(a) a^j = 0 for j = 0, …, k − 1. Then Σ_a ν(a) a^k = k! · ν(k).

*Proof.* The polynomial q(x) = x(x − 1)⋯(x − k + 1) is monic of degree k, so x^k − q(x) has degree below k and Σ_a ν(a) a^k = Σ_a ν(a) q(a). Here q(a) = 0 for a < k and q(k) = k!. ∎

With ν(a) = Pr[Z_1 = a] − Pr[Z_0 = a], Lemma 1 gives

  γ = E[Z_1^k] − E[Z_0^k] = k! · Pr[Z_1 = k] > 0.

## Theorem 1

**Theorem 1.** For every fixed k ≥ 3 there is a constant c_k > 0 such that every quantum algorithm that estimates F_k of strings of length N over [M], for any M ≥ N, within relative error c_k, with probability at least 2/3, makes Ω(N^{a_k}) queries.

*Proof.* On the event z ≤ N, every nonzero z_i contributes z_i^k to F_k and each of the N − z singletons contributes 1, so

  F_k / N = 1 + (1/N) Σ_i (z_i^k − z_i).

The summands are independent and lie in [0, k^k]. Let φ_b = 1 + (m/N)(E[Z_b^k] − 1). Then φ_1 − φ_0 = (m/N) γ ≥ γ/3. By Hoeffding's inequality, F_k/N lies within δ = (φ_1 − φ_0)/8 of φ_b with probability 1 − e^{−Ω(N)}. The event z > N also has probability e^{−Ω(N)}, since E[z] = m ≤ N/2 and each z_i is at most k.

Let c_k = (φ_1 − φ_0)/(4 φ_1), which is bounded below by a positive constant depending only on k, since φ_1 ≤ 1 + k^k. Take an estimate G with (1 − c_k) F_k ≤ G ≤ (1 + c_k) F_k. If F_k ≤ N(φ_0 + δ), then G < N(φ_0 + φ_1)/2. If F_k ≥ N(φ_1 − δ), then G > N(φ_0 + φ_1)/2. So comparing G with N(φ_0 + φ_1)/2 distinguishes Π_0 from Π_1 with bias at least 1/3 − o(1).

By [4, Thm 2.6] with A = r = k, every T-query algorithm with T ≤ c√N has bias at most C k T^{2 − 2^{1−k}} / N^{1 − 2^{1−k}} + N e^{−cN/k^2}. Hence T = Ω(N^{(1 − 2^{1−k})/(2 − 2^{1−k})}) = Ω(N^{a_k}), as a_k < 1/2. ∎

An estimate within any smaller relative error is also an estimate within c_k, so the bound holds for every ε ≤ c_k. For the explicit pairs in the script, the two values φ_0 and φ_1 differ by about 10% at k = 3 and by about 0.15% at k = 5.

## Corollary 2

**Corollary 2.** For every fixed k ≥ 3 there is a constant c′_k > 0 such that estimating H_k(p) within additive error c′_k, with purified query access to a distribution p on [n], needs Ω(n^{a_k}) queries.

*Proof.* A string f of length n over [n] defines p_j = n_j/n. Preparing the uniform superposition over positions and applying one string query gives (1/√n) Σ_i |i⟩|f(i)⟩ = Σ_j √p_j |j⟩|ψ_j⟩, where |ψ_j⟩ is uniform over the positions of j. The inverse of a string query costs one string query (conjugate with the negation of the target register), and a controlled string query costs two (compute into a fresh register, add it under control, uncompute). So every purified query costs O(1) string queries. Since H_k(p) = log(F_k/n^k)/(1 − k), an estimate H with |H − H_k(p)| ≤ c′_k gives F = n^k e^{(1−k)H}, and e^{−(k−1)c′_k} F_k ≤ F ≤ e^{(k−1)c′_k} F_k. With c′_k = c_k/(2(k − 1)), F lies within relative error c_k of F_k, and Theorem 1 applies. ∎

## Theorem 3, the algorithm for bounded multiplicities

**Theorem 3.** For fixed k ≥ 2, B ≥ 2 and 0 < ε < 1, F_k of a string of length N in which every symbol occurs at most B times can be estimated within relative error ε, with probability at least 2/3, with O(N^{a_k}) queries. The constant depends on k, B and ε.

For B = 1 every symbol occurs once and F_k = N, so the hypothesis B ≥ 2 loses nothing.

**Notation.** Let c_t be the number of symbols that occur exactly t times. A chain of length ℓ is an ordered ℓ-tuple of distinct positions that carry the same symbol, and its class is the multiplicity t of that symbol. There are P_ℓ = Σ_t c_t t(t − 1)⋯(t − ℓ + 1) chains of length ℓ, so P_1 = N, and n^k = Σ_ℓ S(k, ℓ) n(n − 1)⋯(n − ℓ + 1) with the Stirling numbers S(k, ℓ) of the second kind gives

  F_k = Σ_{ℓ=1}^{k} S(k, ℓ) P_ℓ.

A chain c of length ℓ and class t has exactly t − ℓ extensions, the positions y ∉ c with the same symbol, and every chain of length ℓ + 1 arises from exactly one chain of length ℓ and one extension. Let π_ℓ be the class of a uniformly random chain of length ℓ, π_ℓ(t) = c_t t(t − 1)⋯(t − ℓ + 1)/P_ℓ, and ρ_ℓ = Σ_t π_ℓ(t)(t − ℓ) = P_{ℓ+1}/P_ℓ. For a probability vector q on the classes {ℓ, …, B}, write ⟨q⟩_ℓ = Σ_t q(t)(t − ℓ) and Φ_ℓ(q)(t) = q(t)(t − ℓ)/⟨q⟩_ℓ. Then Φ_ℓ(π_ℓ) = π_{ℓ+1}.

**Constants.** Let S = Σ_ℓ S(k, ℓ), θ = ε/(12 S B^k), η′ = min(θ, ε/(4 k S (B + 1)^k)), η = η′/(2B), γ = η′/(2B), L = 4B/θ and δ = γ/(L + 1)^k. Let x_1 = a_k and x_{ℓ+1} = a_k − 1/2 + x_ℓ/2, so that x_{k−1} = 1/(2^k − 1), and let s_ℓ = ⌈N^{x_ℓ}⌉.

**Algorithm.**

1. Query s_1 independent uniformly random positions. They form the multiset R_1 of chains of length 1.
2. For ℓ = 1, …, k − 1:
   1. If some symbol carries more than 2B chains of R_ℓ, abort.
   2. For a position y, let m_ℓ(y) be the number of chains of R_ℓ that carry the symbol of y and do not contain y, so m_ℓ(y) ∈ [0, 2B] and Σ_y m_ℓ(y) is the number of extension pairs, s_ℓ ⟨q_ℓ⟩_ℓ, where q_ℓ is the empirical class law of R_ℓ. Run amplitude estimation [8] on the mean of m_ℓ(y)/(2B) over a uniformly random position y, with O(√(BN/(s_ℓ θ))/η) queries, and repeat O(log k) times to take the median. Let ρ̂_ℓ be the resulting estimate of ⟨q_ℓ⟩_ℓ.
   3. If ρ̂_ℓ < θ, set P̂_{ℓ+1} = ⋯ = P̂_k = 0 and go to step 3. Otherwise set P̂_{ℓ+1} = P̂_ℓ ρ̂_ℓ, with P̂_1 = N.
   4. If ℓ ≤ k − 2, draw s_{ℓ+1} independent uniform extension pairs (c, y): find a position y with m_ℓ(y) ≥ 1 by search with an unknown number of solutions [7], accept it with probability m_ℓ(y)/(2B) and search again otherwise, and then take c uniformly among the m_ℓ(y) chains counted by m_ℓ(y). The chains (c, y) form R_{ℓ+1}.
3. Output F̂ = Σ_ℓ S(k, ℓ) P̂_ℓ.

**Lemma 2 (exact class law).** Conditionally on R_ℓ, the chains of R_{ℓ+1} are independent, and the class of each has law Φ_ℓ(q_ℓ). The class of each chain of R_1 has law π_1.

*Proof.* The search outputs a uniformly random position among those with m_ℓ(y) ≥ 1, since the search algorithm treats all solutions alike. After the acceptance step, y has probability proportional to m_ℓ(y), and the pair (c, y) is uniform among the Σ_y m_ℓ(y) extension pairs. A chain c of R_ℓ of class t has t − ℓ extensions, so the class of (c, y), which is the class of c, equals t with probability q_ℓ(t)(t − ℓ)/⟨q_ℓ⟩_ℓ. For R_1, a uniform position has a symbol of multiplicity t with probability t c_t/N = π_1(t). ∎

**Lemma 3 (stability).** If ⟨q⟩_ℓ ≥ θ/2, then ‖Φ_ℓ(q) − Φ_ℓ(p)‖_1 ≤ L ‖q − p‖_1 for every probability vector p.

*Proof.* With weights w(t) = t − ℓ ∈ [0, B], ‖wq/⟨q⟩ − wp/⟨p⟩‖_1 ≤ ‖w(q − p)‖_1/⟨q⟩ + ⟨p⟩ |1/⟨q⟩ − 1/⟨p⟩| ≤ 2B ‖q − p‖_1/⟨q⟩. ∎

*Proof of Theorem 3.* Let N be large. We bound four failure events.

- *Abort.* At level 1, a fixed symbol occurs at most B times, so it is drawn more than 2B times with probability at most (s_1 B/N)^{2B+1}. Over at most N symbols this is O(N^{1 − (2B+1)(1 − a_k)}) = o(1), since 1 − a_k > 1/2. At a later level that is reached, ⟨q_ℓ⟩_ℓ ≥ θ/2 (see the stopping rule below), so a draw lands on a fixed symbol with probability at most 2B · B/(s_ℓ θ/2), and at most s_ℓ symbols can be hit. More than 2B of the s_{ℓ+1} draws land on one symbol with probability O(s_ℓ (s_{ℓ+1}/s_ℓ)^{2B+1}) = O(N^{x_ℓ − (2B+1)(x_ℓ − x_{ℓ+1})}). As x_ℓ − x_{ℓ+1} ≥ x_ℓ/2 and x_ℓ > 0, this is o(1).
- *Sampling.* Conditionally on the previous levels, q_{ℓ+1} is the empirical law of s_{ℓ+1} independent draws from Φ_ℓ(q_ℓ) (Lemma 2), and q_1 is the empirical law of s_1 draws from π_1. By Hoeffding's inequality for each of the B classes, every level satisfies ‖q_1 − π_1‖_1 ≤ δ and ‖q_{ℓ+1} − Φ_ℓ(q_ℓ)‖_1 ≤ δ, except with probability at most 2Bk exp(−2 N^{1/(2^k − 1)} δ²/B²) = o(1).
- *Estimation.* The amplitude estimation runs with a fixed number M = c√(BN/(s_ℓ θ))/η of iterations, for an absolute constant c, whatever the value of the mean μ = s_ℓ⟨q_ℓ⟩_ℓ/(2BN). Its error is at most 2π√μ/M + π²/M² with probability at least 8/π² [8, Thm 12], and each median of O(log k) runs fails with probability at most 1/(10k). When it succeeds and c is large enough, ρ̂_ℓ < θ if ⟨q_ℓ⟩_ℓ < θ/2, and ρ̂_ℓ is within relative error η of ⟨q_ℓ⟩_ℓ if ⟨q_ℓ⟩_ℓ ≥ θ/2.
- *Budget.* The run is stopped after ten times its expected number of queries, which fails with probability at most 1/10 by Markov's inequality.

On the complement, which has probability at least 2/3, the following holds.

*Stopping rule.* If level ℓ is not stopped, then ρ̂_ℓ ≥ θ and ⟨q_ℓ⟩_ℓ ≥ θ/(1 + η) ≥ θ/2. If it is stopped, then ⟨q_ℓ⟩_ℓ < θ/(1 − η) ≤ 2θ.

*Drift.* Let D_ℓ = ‖q_ℓ − π_ℓ‖_1. Then D_1 ≤ δ, and by Lemma 3 and Φ_ℓ(π_ℓ) = π_{ℓ+1}, D_{ℓ+1} ≤ δ + L D_ℓ for every level that is not stopped. Hence D_ℓ ≤ δ(L + 1)^k = γ at every level that is reached.

*Ratios.* At a level that is not stopped, |ρ̂_ℓ − ρ_ℓ| ≤ η⟨q_ℓ⟩_ℓ + |⟨q_ℓ⟩_ℓ − ⟨π_ℓ⟩_ℓ| ≤ ηB + B D_ℓ ≤ η′. Every ρ_ℓ and every ρ̂_ℓ is at most B + 1, so |P̂_ℓ − P_ℓ| ≤ N k η′ (B + 1)^k for the levels before a stop. Summed with the weights S(k, ℓ), this is at most εN/4.

*Tail.* If level ℓ is stopped, then ρ_ℓ ≤ ⟨q_ℓ⟩_ℓ + B D_ℓ ≤ 2θ + η′ ≤ 3θ, so P_{ℓ+1} ≤ 3θ P_ℓ ≤ 3θ B^{ℓ−1} N, and P_i ≤ B^{i−ℓ−1} P_{ℓ+1} for i > ℓ. The omitted part of F_k is at most 3θ S B^k N = εN/4.

So |F̂ − F_k| ≤ εN/2 ≤ εF_k/2, as F_k ≥ N.

*Queries.* At a level that is reached, at least s_ℓ θ/(4B) positions have m_ℓ(y) ≥ 1, so a search costs O(√(BN/(s_ℓ θ))) queries in expectation [7], and each draw needs at most 2B runs of the search in expectation. The expected total is

  O(s_1 + Σ_ℓ √(N/s_ℓ) + Σ_{ℓ ≤ k−2} s_{ℓ+1} √(N/s_ℓ)),

with constants depending on k, B and ε. Every term is O(N^{a_k}), since x_1 = a_k, (1 − x_ℓ)/2 ≤ (1 − x_{k−1})/2 = a_k and x_{ℓ+1} + (1 − x_ℓ)/2 = a_k. For N below a constant N_0(k, B, ε), reading the whole string costs O(1) queries. ∎

For k = 2 the bound is O(N^{1/3}), with the exponent of [1]. For k = 3 the level sizes are N^{3/7} and N^{1/7}, and for k = 4 they are N^{7/15}, N^{1/5} and N^{1/15}, as in the k-collision finding algorithm of [6], which the sampling steps follow. Theorem 1 uses inputs whose multiplicities are at most k, so for k ≥ 3, B ≥ k and small constant ε the two theorems give Θ(N^{a_k}). For k = 2 the matching bound Ω(N^{1/3}) of [1] uses multiplicities at most 2.

## Scripts

`sim/check_gap.py` builds explicit mean-one pairs Z_0 on {0, …, k − 1} and Z_1 on {0, …, k} with equal moments of order below k, for k = 3, …, 8. It checks the moment gap γ = k! Pr[Z_1 = k] in exact arithmetic, and Lemma 1 on 500 random signed functions. It then samples the induced inputs exactly, through the multinomial counts of the m draws. At sizes where the gap is at least ten standard deviations, F_k/N stays within five standard deviations of φ_b, and the two cases separate. Finally it checks a_k = (1 − 2^{1−k})/(2 − 2^{1−k}) and a_k > max(1/3, 1/2 − 1/(2k)) for 3 ≤ k ≤ 39.

```
python sim/check_gap.py
exact pairs and moment gap t k! checked for k = 3..8
gap identity and one-dimensional null space checked
k=3, N=639128: F_k/N limits 2.3750 vs 2.6042 (sd 0.0026, 0.0057), samples [2.3708,2.3809] vs [2.5954,2.6178]
k=4, N=134977068: F_k/N limits 12.0000 vs 12.0938 (sd 0.0021, 0.0023), samples [11.9952,12.0042] vs [12.0895,12.0986]
k=5, N=5716060800: F_k/N limits 97.0000 vs 97.1500 (sd 0.0036, 0.0037), samples [96.9904,97.0071] vs [97.1429,97.1583]
exponents checked for k = 3..39
```

`sim/check_upper.py` runs the algorithm of Theorem 3 with chains of positions, with the quantum steps replaced by their ideal outputs: amplitude estimation returns the number of extension pairs within relative error η, and the search returns a uniformly random position y with m_ℓ(y) ≥ 1. It checks the Stirling identity for k ≤ 8 and n ≤ 14, and the level-size exponents for k ≤ 11. It estimates F_3 and F_4 on 24 random strings of length 2 · 10⁶ with multiplicities at most 5, F_3 on the two instance families of Theorem 1, and F_k on profiles where most symbols reach the bound B. Finally it evaluates the query count of the proof on these runs and fits its growth, which checks the exponent arithmetic on actual level sizes.

```
python sim/check_upper.py
Stirling identity checked
level-size exponents checked for k = 2..11: ['3/7', '1/7'] ['7/15', '1/5', '1/15']
random profiles, N = 2e6, k = 3, 4, B = 5: worst relative error 0.037
pair instance: F_3/N true 2.3758 median of 5 estimates 2.3819
pair instance: F_3/N true 2.6036 median of 5 estimates 2.5976
bound profile k=3, B=5, {5: 400000}: relative error of the median 0.006
bound profile k=3, B=5, {1: 1000000, 5: 200000}: relative error of the median 0.001
bound profile k=4, B=4, {4: 500000}: relative error of the median 0.007
bound profile k=4, B=4, {1: 1600000, 4: 100000}: relative error of the median 0.016
bound profile k=3, B=2, {1: 1000000, 2: 500000}: relative error of the median 0.002
k=3: cost proxy exponent 0.425 (a_k = 0.429)
k=4: cost proxy exponent 0.468 (a_k = 0.467)
```

**Not formalized:** all of the folder. The search and amplitude estimation subroutines [7, 8], Hoeffding's inequality and Theorem 2.6 of [4] enter as known results. The simulation does not run quantum subroutines and does not measure queries.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. A. Montanaro. The quantum complexity of approximating the frequency moments. Quantum Information and Computation 16(13–14), 2016. arXiv:1505.00113.
2. Z. Xiong. A new quantum algorithm framework for integer order entropy estimation. arXiv:2611.25964, 2026.
3. K. Chen, Q. Wang, Z. Zhang. A list of complexity bounds for property testing by quantum sample-to-query lifting. arXiv:2512.01971, 2025.
4. C. Kayal, F. Magniez, S. Sen, D. Szabó. Quantum query lower bounds from classical moment matching. arXiv:2611.05117, 2026.
5. P. Peng, Y. Wang. An optimal separation between two property testing models for bounded degree directed graphs. ICALP 2023. arXiv:2305.13089.
6. Q. Liu, M. Zhandry. On finding quantum multi-collisions. arXiv:1811.05385, 2018.
7. M. Boyer, G. Brassard, P. Høyer, A. Tapp. Tight bounds on quantum searching. arXiv:quant-ph/9605034, 1996.
8. G. Brassard, P. Høyer, M. Mosca, A. Tapp. Quantum amplitude amplification and estimation. arXiv:quant-ph/0005055, 2000.
9. T. Li, X. Wu. Quantum query complexity of entropy estimation. IEEE Transactions on Information Theory 65(5), 2019. arXiv:1710.06025.
10. T. Peng, S. Hou, X. Dong. Tight quantum query bounds for collision finding over arbitrary bounded types. arXiv:2611.17804, 2026.
