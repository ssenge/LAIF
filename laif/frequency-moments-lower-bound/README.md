# Frequency moments and integer-order Rényi entropy: a quantum query lower bound

Written 21 Nov 2026.

**Setting.** The input is a string a_1, …, a_N over an alphabet [M], and a query returns one symbol. If symbol j occurs n_j times, the k-th frequency moment is F_k = Σ_j n_j^k. The task is to output an estimate of F_k within relative error ε, with probability at least 2/3 [1]. In the related distribution setting, a unitary U with U|0⟩ = Σ_j √p_j |j⟩|ψ_j⟩ gives purified query access to a distribution p on [n] (U, its inverse and their controlled versions can be applied), and the task is to estimate the Rényi entropy H_k(p) = log(Σ_j p_j^k)/(1 − k) within additive error ε [2, 3].

| | Problem | Previous best bound, constant ε | This folder | Status |
|---|---|---|---|---|
| Thm 1 | F_k for fixed k ≥ 3, string queries | lower Ω(N^{max(1/3, 1/2 − 1/(2k))}) [1]; upper Õ(N^{u_k}) with u_3 = 4/9, u_4 = 1/2 [2] | Ω(N^{a_k}) with a_k = (2^{k−1} − 1)/(2^k − 1), for relative error below a constant c_k > 0; implied by [4, Thm 2.6] with the instances of [5] | Claim; checked by script |
| Cor 2 | H_k for fixed k ≥ 3, purified access | lower Ω(n^{1/2 − 1/(2k)}) [3, Thm 2.9]; upper Õ(n^{u_k}) [2] | Ω(n^{a_k}) for additive error below a constant c′_k > 0 | Claim |

For k = 3 the exponent is a_3 = 3/7, between the previous lower exponent 1/3 and the upper exponent 4/9. For k = 4 it is 7/15 (previously 3/8, upper 1/2), and for k = 5 it is 15/31. The exponent a_k is also the exponent of k-distinctness testing [4, Cor. 5.1].

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

**Not formalized:** all of the folder.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. A. Montanaro. The quantum complexity of approximating the frequency moments. Quantum Information and Computation 16(13–14), 2016. arXiv:1505.00113.
2. Z. Xiong. A new quantum algorithm framework for integer order entropy estimation. arXiv:2611.25964, 2026.
3. K. Chen, Q. Wang, Z. Zhang. A list of complexity bounds for property testing by quantum sample-to-query lifting. arXiv:2512.01971, 2025.
4. C. Kayal, F. Magniez, S. Sen, D. Szabó. Quantum query lower bounds from classical moment matching. arXiv:2611.05117, 2026.
5. P. Peng, Y. Wang. An optimal separation between two property testing models for bounded degree directed graphs. ICALP 2023. arXiv:2305.13089.
