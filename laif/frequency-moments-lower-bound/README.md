# Frequency moments and integer-order Rényi entropy: quantum query bounds

Written 21 Nov 2026.

**Setting.** The input is a string a_1, …, a_N over an alphabet [M], and a query returns one symbol. If symbol j occurs n_j times, the k-th frequency moment is F_k = Σ_j n_j^k. The task is to output an estimate of F_k within relative error ε, with probability at least 2/3 [1]. In the related distribution setting, a unitary U with U|0⟩ = Σ_j √p_j |j⟩|ψ_j⟩ gives purified query access to a distribution p on [n] (U, its inverse and their controlled versions can be applied), and the task is to estimate the Rényi entropy H_k(p) = log(Σ_j p_j^k)/(1 − k) within additive error ε [2, 3].

| | Problem | Previous best bound, constant ε | This folder | Status |
|---|---|---|---|---|
| Thm 1 | F_k for fixed k ≥ 3, string queries | lower Ω(N^{max(1/3, 1/2 − 1/(2k))}) [1]; upper Õ(N^{u_k}) with u_3 = 4/9, u_4 = 1/2 [2] | Ω(N^{a_k}) with a_k = (2^{k−1} − 1)/(2^k − 1), for relative error below a constant c_k > 0; implied by [4, Thm 2.6] with the instances of [5] | Claim; checked by script |
| Cor 2 | H_k for fixed k ≥ 3, purified access | lower Ω(n^{1/2 − 1/(2k)}) [3, Thm 2.9]; upper Õ(n^{u_k}) [2] | Ω(n^{a_k}) for additive error below a constant c′_k > 0 | Claim |
| Thm 3 | F_k for fixed k ≥ 2 on strings whose multiplicities are at most a constant B | upper Õ(N^{u_k}) [2] (all strings) | O(N^{a_k}) for every constant relative error ε; with Theorem 1, Θ(N^{a_k}) for B ≥ k and small constant ε | Claim; checked by simulation |

For k = 3 the exponent is a_3 = 3/7, between the previous lower exponent 1/3 and the upper exponent 4/9. For k = 4 it is 7/15 (previously 3/8, upper 1/2), and for k = 5 it is 15/31. The exponent a_k is also the exponent of k-distinctness testing [4, Cor. 5.1] and of finding k-collisions in random strings [6]. Theorem 3 shows that it is the exponent of F_k on strings of bounded multiplicity, which include the instances of Theorem 1.

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

An estimate within any smaller relative error is also an estimate within c_k, so the bound holds for every ε ≤ c_k. The constant c_k decreases with k. For the explicit pairs in the script, the two values φ_0 and φ_1 differ by about 10% at k = 3 and by about 0.15% at k = 5.

## Corollary 2

**Corollary 2.** For every fixed k ≥ 3 there is a constant c′_k > 0 such that estimating H_k(p) within additive error c′_k, with purified query access to a distribution p on [n], needs Ω(n^{a_k}) queries.

*Proof.* A string f of length n over [n] defines p_j = n_j/n. Preparing the uniform superposition over positions and applying one string query gives (1/√n) Σ_i |i⟩|f(i)⟩ = Σ_j √p_j |j⟩|ψ_j⟩, where |ψ_j⟩ is uniform over the positions of j. The string query is its own inverse, and a controlled string query costs two string queries. So every purified query costs O(1) string queries. Since H_k(p) = log(F_k/n^k)/(1 − k), an estimate H with |H − H_k(p)| ≤ c′_k gives F = n^k e^{(1−k)H}, and e^{−(k−1)c′_k} F_k ≤ F ≤ e^{(k−1)c′_k} F_k. With c′_k = c_k/(2(k − 1)), F lies within relative error c_k of F_k, and Theorem 1 applies. ∎

## Theorem 3, the algorithm for bounded multiplicities

Let c_t be the number of symbols that occur exactly t times, and P_ℓ = Σ_t c_t t(t − 1)⋯(t − ℓ + 1) the number of ordered ℓ-tuples of distinct positions with equal symbols, so P_1 = N. Since n^k = Σ_ℓ S(k, ℓ) n(n − 1)⋯(n − ℓ + 1) with the Stirling numbers S(k, ℓ) of the second kind,

  F_k = Σ_{ℓ=1}^{k} S(k, ℓ) P_ℓ,  and P_{ℓ+1} = P_ℓ ρ_ℓ with ρ_ℓ = E_{π_ℓ}[t − ℓ],

where π_ℓ is the distribution on multiplicities with π_ℓ(t) ∝ c_t t(t − 1)⋯(t − ℓ + 1). As F_k ≥ N and F_k ≥ P_ℓ, it suffices to estimate every ρ_ℓ within an additive error η = η(k, B, ε) > 0, and to stop as soon as some ρ_ℓ is below η, since then ρ_ℓ < 2η and P_{ℓ+1}, …, P_k are O(B^k η N).

**Theorem 3.** For fixed k ≥ 2, B ≥ 1 and ε > 0, F_k of a string of length N whose symbols occur at most B times each can be estimated within relative error ε, with probability at least 2/3, with O(N^{a_k}) queries.

*Algorithm.* Let x_1 = a_k and x_{ℓ+1} = a_k − 1/2 + x_ℓ/2, so that x_{k−1} = 1/(2^k − 1) > 0, and let s_ℓ = ⌈C N^{x_ℓ}⌉ for a constant C = C(k, B, ε). The set U holds the queried positions.

1. Query a uniformly random set R_1 of s_1 positions.
2. For ℓ = 1, …, k − 1: for a fresh position y ∉ U, let m_ℓ(y) be the number of elements of R_ℓ with the symbol of y, a number in [0, B]. Estimate the sum Σ_{y∉U} m_ℓ(y) within relative error η by amplitude estimation of the mean of m_ℓ. Each element r of R_ℓ has t_r = (occurrences of its symbol in U) + (occurrences outside U), and the first part is known, so this gives an estimate of the mean of t_r − ℓ over R_ℓ, the estimate of ρ_ℓ. If it is below η, stop. If ℓ ≤ k − 2, sample s_{ℓ+1} distinct fresh positions y with probability proportional to m_ℓ(y), by Grover search over the fresh positions with m_ℓ(y) ≥ 1 followed by acceptance with probability m_ℓ(y)/B. They form R_{ℓ+1} and join U.
3. Output Σ_ℓ S(k, ℓ) N Π_{i<ℓ} ρ̂_i.

*Cost.* While ρ_ℓ ≥ η, the fresh positions with m_ℓ ≥ 1 number at least s_ℓ η/B, so each Grover sample costs O(B√(N/(s_ℓ η))) queries in expectation, and the amplitude estimation costs O(√(BN/(s_ℓ η))/η). The total is O(s_1 + Σ_{ℓ ≤ k−2} s_{ℓ+1}√(N/s_ℓ) + Σ_ℓ √(N/s_ℓ)), and the choice of x_ℓ makes every term O(N^{a_k}): x_{ℓ+1} + (1 − x_ℓ)/2 = a_k and (1 − x_{k−1})/2 = a_k. Repeating O(1) times and taking the median gives success probability 2/3, and the expected cost becomes a worst-case cost by Markov's inequality.

*Correctness.* The positions of R_1 are uniform, so the multiplicity of the symbol of each element of R_1 has law π_1. If the empirical law of the multiplicities over R_ℓ is close to π_ℓ, a sample with probability proportional to m_ℓ(y) has a symbol whose multiplicity t has probability proportional to the R_ℓ-weight of t times the number of fresh occurrences, which is t − ℓ except when the symbol was hit by U more than ℓ times. The expected fraction of such coincidences is O(B k s_1/N) = O(N^{a_k − 1}). So the law of a level-(ℓ + 1) sample is within o(1) in total variation of π_{ℓ+1}, and the empirical law over R_{ℓ+1} is within O(B/√s_{ℓ+1}) of it by Hoeffding's inequality, with s_{ℓ+1} ≥ C N^{1/(2^k − 1)}. Hence every ρ̂_ℓ is within η of ρ_ℓ with high probability for N ≥ N_0(k, B, ε), and smaller N are handled by reading the whole string. ∎

For k = 2 the bound is O(N^{1/3}), with the exponent of [1]. For k = 3 and k = 4 the level sizes are N^{3/7}, N^{1/7} and N^{7/15}, N^{1/5}, N^{1/15}, as in the k-collision finding algorithm of [6], which the sampling steps follow.

## Scripts

`sim/check_gap.py` builds explicit mean-one pairs Z_0 on {0, …, k − 1} and Z_1 on {0, …, k} with equal moments of order below k, for k = 3, …, 8. It checks the moment gap γ = k! Pr[Z_1 = k] in exact arithmetic, and Lemma 1 on 500 random signed functions. It then samples the induced inputs exactly, through the multinomial counts of the m draws. At sizes where the gap is ten standard deviations, F_k/N stays within five standard deviations of φ_b, and the two cases separate. Finally it checks a_k = (1 − 2^{1−k})/(2 − 2^{1−k}) and a_k > max(1/3, 1/2 − 1/(2k)) for 3 ≤ k ≤ 39.

```
python sim/check_gap.py
exact pairs and moment gap t k! checked for k = 3..8
gap identity and one-dimensional null space checked
k=3, N=639128: F_k/N limits 2.3750 vs 2.6042 (sd 0.0026, 0.0057), samples [2.3708,2.3809] vs [2.5954,2.6178]
k=4, N=134977068: F_k/N limits 12.0000 vs 12.0938 (sd 0.0021, 0.0023), samples [11.9952,12.0042] vs [12.0895,12.0986]
k=5, N=5716060800: F_k/N limits 97.0000 vs 97.1500 (sd 0.0036, 0.0037), samples [96.9904,97.0071] vs [97.1429,97.1583]
exponents checked for k = 3..39
```

`sim/check_upper.py` simulates the algorithm of Theorem 3 with the quantum steps replaced by their ideal outputs: approximate counting returns the true value within relative error η, and Grover sampling returns a uniformly random marked position. It checks the Stirling identity for k ≤ 8 and n ≤ 14, and the level-size exponents for k ≤ 11. It estimates F_3 and F_4 on 24 random strings of length 2 · 10⁶ with multiplicities at most 5, and F_3 on the two instance families of Theorem 1. Finally it fits the growth of the query count of the simulated algorithm.

```
python sim/check_upper.py
Stirling identity checked
level-size exponents checked for k = 2..11: ['3/7', '1/7'] ['7/15', '1/5', '1/15']
random profiles, N = 2e6, k = 3, 4, B = 5: worst relative error 0.042
pair instance: F_3/N true 2.375 median of 5 estimates 2.3567
pair instance: F_3/N true 2.6092 median of 5 estimates 2.6319
k=3: cost proxy exponent 0.418 (a_k = 0.429)
k=4: cost proxy exponent 0.456 (a_k = 0.467)
```

**Not formalized:** all of the folder. The simulation does not run quantum subroutines and does not measure queries.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. A. Montanaro. The quantum complexity of approximating the frequency moments. Quantum Information and Computation 16(13–14), 2016. arXiv:1505.00113.
2. Z. Xiong. A new quantum algorithm framework for integer order entropy estimation. arXiv:2611.25964, 2026.
3. K. Chen, Q. Wang, Z. Zhang. A list of complexity bounds for property testing by quantum sample-to-query lifting. arXiv:2512.01971, 2025.
4. C. Kayal, F. Magniez, S. Sen, D. Szabó. Quantum query lower bounds from classical moment matching. arXiv:2611.05117, 2026.
5. P. Peng, Y. Wang. An optimal separation between two property testing models for bounded degree directed graphs. ICALP 2023. arXiv:2305.13089.
6. Q. Liu, M. Zhandry. On finding quantum multi-collisions. arXiv:1811.05385, 2018.
