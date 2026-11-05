# No quantum speedup for smooth strongly convex finite sums in high dimension

Written 5 Nov 2026.

## Setting

This is Case 1 of the quantum finite-sum problem of [1]:

minimize F(x) = (1/n) Σᵢ fᵢ(x) + ψ(x) over x ∈ R^d,

where each fᵢ is convex and ℓ-smooth, ψ is μ-strongly convex and known, and F(0) − F* ≤ Δ. Write κ = ℓ/μ. An algorithm queries the quantum finite-sum oracle

O_F |x⟩|i⟩|b⟩ = |x⟩|i⟩|b ⊕ ∇fᵢ(x)⟩,

also in superposition over x and i, and must output an expected ε-optimal point, E[F(x)] ≤ F* + ε, on every instance. As in the reduction of [1, Lemma 11], the queries are supported on a ball ‖x‖ ≤ R. Here R is any radius of at least 3√(Δ/μ), and the dimension needed below grows like R².

Known bounds:

| | Bound |
|---|---|
| Classical lower bound | Ω(n + √(nκ) log(1/ε)) [3] |
| Classical upper bound | O((n + √(nκ)) log(Δ/ε)), by Katyusha [2] |
| Quantum upper bound | Õ(n + √d + √κ (n^{1/3}d^{1/3} + n^{−2/3}d^{5/6})) [1] |
| Quantum lower bound | Ω(n + n^{3/4} κ^{1/4} log^{1/2}(Δμ/(εℓ))) [1], for κ ≥ 100n and d = Ω̃(Δℓ²/(μ²nε)) |

The paper [1] asks whether tighter quantum lower bounds hold.

## Result

Scale so that ℓ = 1, replacing fᵢ, ψ, Δ and ε by fᵢ/ℓ, ψ/ℓ, Δ/ℓ and ε/ℓ; then μ = 1/κ. Define the following constants:

- N = ⌊n/2⌋ and μ̃ = nμ;
- Q = (1/μ̃ + 1)/2 and q = (√Q − 1)/(√Q + 1);
- k is the largest integer with q^{2k+1} > 3ε/(μΔ);
- a = (1 − μ̃)/(16n), C = √(Δ/(2Naq)) and c = C q^{k+1} √(μ̃/(2(k+1)));
- s = ⌊4R²/c²⌋ and A = 400(k+1)²s.

**Theorem 1.** Let n ≥ 2, κ ≥ 100n, R ≥ 3√(Δ/μ) and 0 < ε < q³μΔ/(3ℓ), so that k ≥ 1. Suppose

d ≥ N(k+1)A + (8R²/c²) ln(40 N(k+1)A).

Then every quantum algorithm whose queries are supported on ‖x‖ ≤ R, and which outputs an expected ε-optimal point on every instance of Case 1, makes at least

N(k+1) ln(3/2) / 16000 ≥ 6·10⁻⁷ √(nκ) ln(μΔ/(3εℓ))

queries to O_F.

**Corollary 2.** For κ ≥ 100n and ε ≤ μΔ/(9ℓ), we have n ≤ √(nκ)/10 and ln(μΔ/(3εℓ)) ≥ (1/2) ln(μΔ/(εℓ)). So the bound reads Ω(n + √(nκ) log(μΔ/(εℓ))).

- This is the classical lower bound of [3].
- For ε ≤ μ²Δ/ℓ², we have log(μΔ/(εℓ)) ≥ (1/2) log(Δ/ε), so the bound also matches the classical upper bound of Katyusha [2] up to a constant factor.

So in Case 1, quantum queries give no asymptotic speedup once d is a large enough polynomial. With R = 3√(Δ/μ), we have R²/c² < 3κΔ(k+1)/(8nε), so

d = O((k+1)⁴ κΔ/ε) = O(κ³ Δ log⁴(μΔ/(εℓ)) / (n²ε))

suffices.

## 1. The instance

The construction keeps ℓ = 1. Let φ_c be the helper function of [1, Eq. (5)]:

- φ_c(z) = 0 for |z| ≤ c;
- φ_c(z) = 2(|z| − c)² for c < |z| ≤ 2c;
- φ_c(z) = z² − 2c² for |z| > 2c.

It is convex and C¹ with a 4-Lipschitz derivative, and z² − 2c² ≤ φ_c(z) ≤ z².

Let v_{i,r} be orthonormal vectors, for 1 ≤ i ≤ N and 0 ≤ r ≤ k, and write y_{i,r} = ⟨x, v_{i,r}⟩. With ζ = 1 − q, define

- f_{2i−1}(x) = ((1 − μ̃)/16) (y_{i,0}² − 2C y_{i,0} + Σ_{r even, 2 ≤ r ≤ k} φ_c(y_{i,r−1} − y_{i,r}));
- f_{2i}(x) = ((1 − μ̃)/16) (ζ φ_c(y_{i,k}) + Σ_{r odd, 1 ≤ r ≤ k} φ_c(y_{i,r−1} − y_{i,r}));
- f_n = 0 if n is odd;
- ψ(x) = (μ/2)‖x‖².

This is the instance of [1, Definition 3], with the constants C and c chosen as above. Each pair (f_{2i−1}, f_{2i}) is a *chain* with vectors v_{i,0}, …, v_{i,k}.

Let x_⊥ be the part of x orthogonal to all v_{i,r}. Then F(x) = Σᵢ G(yᵢ) + (μ/2)‖x_⊥‖², where for y ∈ R^{k+1}

G(y) = a (y₀² − 2C y₀ + Σ_{r=1}^{k} φ_c(y_{r−1} − y_r) + ζ φ_c(y_k)) + (μ/2)‖y‖².

Let H be G with every φ_c(z) replaced by z². Then H − 2ac²(k+1) ≤ G ≤ H, and H is a μ-strongly convex quadratic.

We have μ/(2a) = 8μ̃/(1 − μ̃) = 4/(Q − 1). So the first-order conditions of H read

- (2 + 4/(Q−1)) y₀ − y₁ = C;
- y_{r−1} − (2 + 4/(Q−1)) y_r + y_{r+1} = 0 for 1 ≤ r < k;
- (1 + ζ + 4/(Q−1)) y_k = y_{k−1}.

Since q + 1/q = 2 + 4/(Q−1) and ζ = 1 − q, the point ŷ_r = C q^{r+1} solves them. The minimum is H(ŷ) = −aCŷ₀ = −aC²q.

**Lemma 1 (the instance is in Case 1).** Each fᵢ is convex and 1-smooth, and 0 ≤ F(0) − F* ≤ Δ.

*Proof.* Convexity holds because φ_c is convex and composed with linear maps.

For smoothness, look at the groups of vectors each function uses:

- In f_{2i−1}, the terms use the disjoint groups {v_{i,0}}, {v_{i,1}, v_{i,2}}, {v_{i,3}, v_{i,4}}, …. Their generalized Hessians are at most 2 and 4‖v_{i,r−1} − v_{i,r}‖² = 8. So ∇f_{2i−1} is ((1 − μ̃)/2)-Lipschitz.
- In f_{2i}, the groups are {v_{i,0}, v_{i,1}}, {v_{i,2}, v_{i,3}}, …, and v_{i,k} also carries ζφ_c. So the constant is at most ((1 − μ̃)/16)(8 + 4ζ) ≤ 3/4.

For the gap, F(0) = 0 and F* = N min G ≥ N(H(ŷ) − 2ac²(k+1)). Also 2ac²(k+1) = aμ̃C²q^{2k+2} ≤ aC²q. Hence F(0) − F* ≤ 2NaC²q = Δ. ∎

**Lemma 2 (every chain coordinate is needed).** If |⟨x, v_{i,t}⟩| < c/2 for some i and some 0 ≤ t ≤ k, then F(x) − F* > 3ε.

*Proof.* The other chains and x_⊥ contribute at least their minimum, so F(x) − F* ≥ G(yᵢ) − min G. Next:

- min G ≤ G(ŷ) ≤ H(ŷ), and G(yᵢ) ≥ H(yᵢ) − 2ac²(k+1).
- By strong convexity, H(yᵢ) − H(ŷ) ≥ (μ/2)‖yᵢ − ŷ‖² ≥ (μ/2)(ŷ_t − c/2)².
- Since ŷ_t ≥ C q^{k+1} and c ≤ C q^{k+1}/20 (as μ̃ ≤ 1/100), we get ŷ_t − c/2 ≥ (39/40) C q^{k+1}.
- Also 2ac²(k+1) = aμ̃C²q^{2k+2} = ((1 − μ̃)/16) μC²q^{2k+2}.

Together these give

G(yᵢ) − min G ≥ ((1/2)(39/40)² − 1/16) μC²q^{2k+2} ≥ 0.41 μC²q^{2k+2}.

Finally, Na ≤ 1/32 and q^{2k+1} > 3ε/(μΔ), so μC²q^{2k+2} = μΔq^{2k+1}/(2Na) ≥ 16μΔq^{2k+1} > 48ε. The gap is therefore more than 0.41 · 48ε > 3ε. ∎

## 2. Chains with a large alphabet

**Chain problem.** Let A, k and s be positive integers.

- The input is a key tuple m = (m₀, …, m_k) ∈ [A]^{k+1}.
- A query position is a tuple S = (S₀, …, S_k) of subsets of [A] with Σⱼ |Sⱼ| ≤ s.
- The answer at S is w(S) = (w₀, …, w_k). Here wⱼ = mⱼ if j = 0, or if m_{j'} ∈ S_{j'} for some j' ∈ {j − 1, j, j + 1} ∩ [0, k]. Otherwise wⱼ = ⊥.
- The oracle is |S⟩|b⟩ ↦ |S⟩|b ⊕ w(S)⟩, with answers written in binary. The goal is to output m.

Write f_ch for this function. Its input and output alphabets are finite.

**Lemma 3.** If A ≥ 400(k+1)²s, every algorithm with at most k queries outputs m with probability less than 1/4 on average over a uniform m. Hence Q_{1/4}(f_ch) ≥ k + 1.

*Proof.* This is a hybrid argument as in [5].

1. Let O_p be the oracle of the tuple (m₀, …, m_{p−1}, ⊥, …, ⊥). A key ⊥ lies in no set, and a position with key ⊥ answers ⊥.
2. Run the algorithm with O_p at its p-th query, and let φ_p be the state just before that query. By induction, φ_p depends only on m₀, …, m_{p−2}.
3. Compare O and O_p at a position S.
   - The answers wⱼ for j ≤ p − 2 agree.
   - w_{p−1} differs only if m_p ∈ S_p.
   - A wⱼ with j ≥ p is revealed by O only if some m_{j'} with j' ≥ p − 1 lies in S_{j'}.

   So the answers differ only if m_{j'} ∈ S_{j'} for some j' ≥ p − 1.
4. The keys m_{p−1}, …, m_k are uniform and independent of φ_p. Let Π_p project onto the positions where O and O_p differ. Then E‖Π_p φ_p‖² ≤ Σⱼ |Sⱼ|/A ≤ s/A.
5. Let ψ be the final state with O and ψ' the final state of the hybrid run. Then ‖ψ − ψ'‖ ≤ Σ_p ‖(O − O_p)φ_p‖ ≤ 2 Σ_p ‖Π_p φ_p‖. So E‖ψ − ψ'‖ ≤ 2k√(s/A) < 1/10.
6. With at most k queries, ψ' depends only on m₀, …, m_{k−1}, so it outputs the right m_k with probability 1/A. Success probabilities differ by at most 2‖ψ − ψ'‖, so the average success is at most 1/A + 1/5 < 1/4.

An algorithm with error at most 1/4 on every input would succeed with probability at least 3/4 on average. So Q_{1/4}(f_ch) ≥ k + 1. ∎

**Theorem (strong direct product [4, Theorem 1.1], with δ = 1).** For every function f with finite input and output alphabets, Q_{1/2}(f^{(N)}) ≥ N ln(3/2) Q_{1/4}(f)/8000. Here f^{(N)} has N independent inputs, and a query may address any position of any input, also in superposition.

With Lemma 3: an algorithm that outputs all N key tuples of N independent chains with probability at least 1/2 on every input makes at least N(k+1) ln(3/2)/8000 queries.

## 3. The reduction

**Candidates.** The algorithm B below draws a Haar random orthonormal family u_{i,j,α} in R^d, for 1 ≤ i ≤ N, 0 ≤ j ≤ k and α ∈ [A]. The inputs of B are N key tuples mᵢ = (m_{i,0}, …, m_{i,k}), which B does not know, and the hidden instance of Section 1 uses v_{i,j} = u_{i,j,m_{i,j}}. For ‖x‖ ≤ R, let Sⱼ(x) = {α : |⟨x, u_{i,j,α}⟩| > c/2} and Sⁱ(x) = (S₀(x), …, S_k(x)).

**Lemma 4 (one query of O_F costs two chain queries).** For ‖x‖ ≤ R:

- Σⱼ |Sⱼ(x)| ≤ s;
- ∇f_{2i−1}(x) and ∇f_{2i}(x) are functions of x, the candidates, and the answer w of chain i at Sⁱ(x).

*Proof.* The candidates are orthonormal, so the sum of ⟨x, u⟩² over all of them is at most ‖x‖² ≤ R². Hence fewer than 4R²/c² candidates have |⟨x, u⟩| > c/2.

For the gradient, recall that φ_c' vanishes on |z| ≤ c.

- A term φ_c(y_{i,r−1} − y_{i,r}) has a nonzero gradient only if |y_{i,r−1}| > c/2 or |y_{i,r}| > c/2, that is, if m_{i,r−1} ∈ S_{r−1} or m_{i,r} ∈ S_r. Then w reveals both m_{i,r−1} and m_{i,r}.
- The term ζφ_c(y_{i,k}) needs v_{i,k} only if |y_{i,k}| > c, and then m_{i,k} ∈ S_k.
- The terms in v_{i,0} use w₀ = m_{i,0}, which is always revealed.

So the gradient is the sum of the terms whose vectors are all revealed. ∎

**Simulation of one query.** The simulation runs these steps:

1. Compute Sⁱ(x) into a work register.
2. Query chain i.
3. XOR the gradient into the output register.
4. Query again to erase w.
5. Uncompute Sⁱ(x).

On ‖x‖ ≤ R, this is exactly O_F, also with i in superposition. A query to the zero component f_n costs nothing.

**Lemma 5 (decoding).** Fix the key tuples, run the algorithm with the simulated oracle, and let x be its output. With probability at least 2/3 − 1/20, the following holds for every i and j: exactly one candidate u_{i,j,α} has |⟨x, u⟩| ≥ c/2, and that candidate has α = m_{i,j}.

*Proof.* The argument has four steps.

1. **Independence.** The whole family of candidates is Haar distributed. So for every fixed set of keys, the true vectors form a Haar orthonormal family. Given the true vectors, the other candidates form a Haar orthonormal family of the complement W, where dim W = d − N(k+1). By Lemma 4 the algorithm sees exactly O_F of the true instance. So x depends only on the true vectors and the algorithm's randomness, and it is independent of the false candidates given the true ones.
2. **Near optimality.** By Markov's inequality, F(x) − F* < 3ε with probability at least 2/3. On that event, Lemma 2 gives |⟨x, v_{i,j}⟩| ≥ c/2 for all i and j.
3. **Norm.** On the same event, strong convexity gives ‖x*‖ ≤ √(2Δ/μ) and ‖x − x*‖ ≤ √(6ε/μ) ≤ √(2Δ). So ‖x‖ < 1.6√(Δ/μ) ≤ R.
4. **Union bound.** A false candidate u is uniform on the unit sphere of W. So for a fixed x with ‖x‖ ≤ R, Pr[|⟨x, u⟩| ≥ c/2] ≤ 2 exp(−dim W · c²/(8R²)). A union bound over the N(k+1)(A − 1) false candidates, with the assumed bound on d, gives at most 1/20. ∎

*Proof of Theorem 1.* Let the algorithm make T queries, and let B be the following algorithm for N independent chains:

1. Draw the candidates.
2. Run the algorithm with the simulated oracle.
3. Decode the output as in Lemma 5.

B makes 2T chain queries. By Lemma 5 it outputs all N key tuples with probability more than 1/2 on every input. By Lemma 3 and the strong direct product theorem, 2T ≥ N(k+1) ln(3/2)/8000.

For the explicit bound, write L = ln(μΔ/(3ε)).

- Since ln(1/q) ≤ 2/(√Q − 1), the choice of k gives k + 1 ≥ (√Q − 1)L/4 − 1/2. With k ≥ 1, this implies k + 1 ≥ (√Q − 1)L/8.
- For κ ≥ 100n, we have √Q − 1 ≥ 0.6√(κ/n) and N ≥ n/3.

So T ≥ 6·10⁻⁷ √(nκ) L. ∎

## Remarks

1. **The alphabet.** In [1], each chain entry takes one of two known values. A query can then cover the four extensions of a known prefix by two entries, and Grover's search on four items finds the right one with a single query. So a plain hybrid argument does not apply to the two-valued chains. The bound in [1] comes from an adversary argument and reads n√k. With A ≥ 400(k+1)²s values per entry, a query that guesses an unknown key succeeds with amplitude O(√(s/A)). Then the single chain needs k + 1 queries, and the strong direct product theorem [4] extends this to the superposition over the n components.

2. **The constants of [1, Lemma 5].** The proof of that lemma finds the minimum −μ̃C²(√Q − 1)²/16 for each chain. With the printed constant C = √(Δ/μ) · 4/(√Q − 1), this hints at F(0) − F* = nΔ rather than Δ, and the check below finds nΔ for n = 2, 4 and 8. Using Δ/n in place of Δ in that lemma seems to restore F(0) − F* ≤ Δ. This changes only the argument of the logarithm in [1, Corollary 3]. The instance above sets C directly, so that Lemma 1 holds.

3. **Query norm.** Theorem 1 holds for every finite radius R, with d growing like R².

## Check

`sim/finitesum_check.py`, run with `python sim/finitesum_check.py` (NumPy and SciPy), checks the following:

- Lemma 1 and Lemma 2 for five parameter sets. It pins one chain coordinate to ±c/2 and minimizes, and it computes F(0) − F*.
- Remark 2, with the constants of [1].
- Convexity and smoothness, from Hessians at random points.
- Lemma 4 on 3000 random queries, comparing the true gradients with those rebuilt from the revealed keys.

All checks pass:

```
n=2 kappa=200 eps=0.0001: k=4, c=3.55e-02, F(0)-F*=0.5003 <= 1, min gap with one |y_t| <= c/2: 2.309e-02 >= bound 2.587e-03 > 3 eps
n=2 kappa=800 eps=1e-06: k=20, c=1.70e-03, F(0)-F*=0.5000 <= 1, min gap with one |y_t| <= c/2: 4.273e-04 >= bound 2.487e-05 > 3 eps
n=4 kappa=1600 eps=1e-06: k=18, c=2.37e-03, F(0)-F*=0.5000 <= 1, min gap with one |y_t| <= c/2: 3.769e-04 >= bound 2.190e-05 > 3 eps
n=6 kappa=600 eps=1e-05: k=6, c=1.70e-02, F(0)-F*=0.5001 <= 1, min gap with one |y_t| <= c/2: 2.389e-03 >= bound 2.777e-04 > 3 eps
n=2 kappa=3200 eps=1e-07: k=48, c=3.27e-04, F(0)-F*=0.5000 <= 1, min gap with one |y_t| <= c/2: 7.415e-05 >= bound 2.152e-06 > 3 eps
constants of [1], n=2, Delta=1: F(0)-F* = 2.0000
constants of [1], n=4, Delta=1: F(0)-F* = 4.0000
constants of [1], n=8, Delta=1: F(0)-F* = 8.0000
components convex, largest Hessian eigenvalue seen 0.499 <= 1 (k=20)
gradient simulation exact on 3000 queries (k=4, A=6), largest candidate set total 6
```

## References

1. Y. Zhang, C. Zhang, C. Fang, L. Wang, T. Li. Quantum Algorithms and Lower Bounds for Finite-Sum Optimization. ICML 2024, arXiv:2406.03006.
2. Z. Allen-Zhu. Katyusha: The First Direct Acceleration of Stochastic Gradient Methods. STOC 2017, arXiv:1603.05953.
3. B. Woodworth, N. Srebro. Tight Complexity Bounds for Optimizing Composite Objectives. NeurIPS 2016, arXiv:1605.08003.
4. T. Lee, J. Roland. A strong direct product theorem for quantum query complexity. CCC 2012, arXiv:1104.4468.
5. C. H. Bennett, E. Bernstein, G. Brassard, U. Vazirani. Strengths and weaknesses of quantum computing. SIAM J. Comput. 26(5), 1997, arXiv:quant-ph/9701001.
