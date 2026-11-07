# No quantum speedup for finite-sum convex optimization in high dimension

Written 5 Nov 2026.

## Setting

Sections 1 to 3 treat Case 1 of the quantum finite-sum problem of [1], and Section 4 treats Cases 2 to 4. Case 1 is the following problem:

minimize F(x) = (1/n) Σᵢ fᵢ(x) + ψ(x) over x ∈ R^d,

where each fᵢ is convex and ℓ-smooth, ψ is μ-strongly convex and known, and F(0) − F* ≤ Δ. Write κ = ℓ/μ. An algorithm queries the quantum finite-sum oracle

O_F |x⟩|i⟩|b⟩ = |x⟩|i⟩|b ⊕ ∇fᵢ(x)⟩,

also in superposition over x and i, and must output an expected ε-optimal point, E[F(x)] ≤ F* + ε, on every instance. As in [1], x and ∇fᵢ(x) are taken with exact real arithmetic; any fixed finite encoding works the same way. As in the reduction of [1, Lemma 11], the queries are supported on a ball ‖x‖ ≤ R. Here R is any radius of at least 3√(Δ/μ), and the dimension needed below grows like R². The model of [1, Corollary 3], an ε-optimal output with probability at least 2/3, is covered as well, since the proof below only uses that the output is 3ε-optimal with probability at least 2/3.

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

**Corollary 2.** Keep the assumptions of Theorem 1, and let ε ≤ μΔ/(9ℓ). This implies ε < q³μΔ/(3ℓ), since q³/3 ≥ 0.142. We have n ≤ √(nκ)/10 and ln(μΔ/(3εℓ)) ≥ (1/2) ln(μΔ/(εℓ)). So the bound reads Ω(n + √(nκ) log(μΔ/(εℓ))).

- This is the classical lower bound of [3].
- For ε ≤ μ²Δ/ℓ², we have log(μΔ/(εℓ)) ≥ (1/2) log(Δ/ε), so the bound also matches the classical upper bound of Katyusha [2] up to a constant factor.

So in Case 1, for queries in a ball as in [1, Lemma 11], quantum queries give no asymptotic speedup once d is a large enough polynomial. With R = 3√(Δ/μ), we have R²/c² < 3κΔ(k+1)/(8nε). So, for ε ≤ μΔ/(9ℓ),

d = O((k+1)⁴ κΔ/ε) = O(κ³ Δ log⁴(μΔ/(εℓ)) / (n²ε))

suffices.

## 1. The instance

The construction keeps ℓ = 1. Let φ_c be the helper function of [1, Eq. (5)]:

- φ_c(z) = 0 for |z| ≤ c;
- φ_c(z) = 2(|z| − c)² for c < |z| ≤ 2c;
- φ_c(z) = z² − 2c² for |z| > 2c.

It is convex and C¹ with |φ_c′(z) − φ_c′(w)| ≤ 4|z − w|, and z² − 2c² ≤ φ_c(z) ≤ z².

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

- In f_{2i−1}, the terms use the disjoint groups {v_{i,0}}, {v_{i,1}, v_{i,2}}, {v_{i,3}, v_{i,4}}, …. Their generalized second derivatives are at most 2 and 4‖v_{i,r−1} − v_{i,r}‖² = 8. So ‖∇f_{2i−1}(x) − ∇f_{2i−1}(y)‖ ≤ ((1 − μ̃)/2)‖x − y‖.
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

The chain oracle XORs a binary encoding of w(S). This differs from the convention of [4] only in form. The hybrid argument and the adversary bounds behind [4] use only that a query acts on S through a unitary that depends on w(S) alone, and the XOR and modular-addition oracles simulate each other with O(1) queries.

With Lemma 3: an algorithm that outputs all N key tuples of N independent chains with probability at least 1/2 on every input makes at least N(k+1) ln(3/2)/8000 queries.

## 3. The reduction

**Candidates.** The algorithm B below draws a uniformly random orthonormal family u_{i,j,α} in R^d, for 1 ≤ i ≤ N, 0 ≤ j ≤ k and α ∈ [A]. The inputs of B are N key tuples mᵢ = (m_{i,0}, …, m_{i,k}), which B does not know, and the hidden instance of Section 1 uses v_{i,j} = u_{i,j,m_{i,j}}. For ‖x‖ ≤ R, let Sⱼ(x) = {α : |⟨x, u_{i,j,α}⟩| > c/2} and Sⁱ(x) = (S₀(x), …, S_k(x)).

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

On ‖x‖ ≤ R, this is exactly O_F, also with i in superposition. In the branch of the zero component f_n, the simulation queries a fixed dummy position (chain 1 at S = (∅, …, ∅)) and erases it in the same way. So every query of O_F costs exactly two chain queries.

**Lemma 5 (decoding).** Fix the key tuples, run the algorithm with the simulated oracle, and let x be its output. With probability at least 2/3 − 1/20, the following holds for every i and j: exactly one candidate u_{i,j,α} has |⟨x, u⟩| ≥ c/2, and that candidate has α = m_{i,j}.

*Proof.* The argument has four steps.

1. **Independence.** The whole family of candidates is uniformly distributed. So for every fixed set of keys, the true vectors form a uniformly random orthonormal family. Given the true vectors, the other candidates form a uniformly random orthonormal family of the complement W, where dim W = d − N(k+1). By Lemma 4 the algorithm sees exactly O_F of the true instance. So x depends only on the true vectors and the algorithm's randomness, and it is independent of the false candidates given the true ones.
2. **Near optimality.** By the first moment inequality, F(x) − F* < 3ε with probability at least 2/3. On that event, Lemma 2 gives |⟨x, v_{i,j}⟩| ≥ c/2 for all i and j.
3. **Norm.** On the same event, strong convexity gives ‖x*‖ ≤ √(2Δ/μ) and ‖x − x*‖ ≤ √(6ε/μ) ≤ √(2Δ). Since μ ≤ 1/200, this gives ‖x‖ < 1.6√(Δ/μ) ≤ R.
4. **Union bound.** A false candidate u is uniform on the unit sphere of W. So for a fixed x with ‖x‖ ≤ R, Pr[|⟨x, u⟩| ≥ c/2] ≤ 2 exp(−dim W · c²/(8R²)). A union bound over the N(k+1)(A − 1) false candidates, with the assumed bound on d, gives at most 1/20. ∎

*Proof of Theorem 1.* Let the algorithm make T queries, and let B be the following algorithm for N independent chains:

1. Draw the candidates.
2. Run the algorithm with the simulated oracle.
3. Decode the output as in Lemma 5.

B makes 2T chain queries. By Lemma 5, averaged over the uniform frame, it outputs all N key tuples with probability more than 0.61 on every input.

A query algorithm in the sense of [4] has finitely many basis states, so B should use finite randomness. There are A^{N(k+1)} inputs. Draw M = O(N(k+1) log A) frames independently. By the tail bound for bounded independent variables and a union bound over the inputs, some outcome of the draw has success above 0.55 on every input, averaged over its M frames. Let B pick one of these M frames uniformly, using a register of log M qubits. Lemma 4 is exact for every fixed frame, so nothing else changes.

By Lemma 3 and the strong direct product theorem, 2T ≥ N(k+1) ln(3/2)/8000.

For the explicit bound, write L = ln(μΔ/(3ε)).

- Since ln(1/q) ≤ 2/(√Q − 1), the choice of k gives k + 1 ≥ (√Q − 1)L/4 − 1/2. With k ≥ 1, this implies k + 1 ≥ (√Q − 1)L/8.
- For κ ≥ 100n, we have √Q − 1 ≥ 0.6√(κ/n) and N ≥ n/3.

So T ≥ 6·10⁻⁷ √(nκ) L. ∎

## 4. Cases 2 to 4

Cases 2 to 4 of [1] change the assumptions:

- Case 2: each fᵢ is convex and ℓ-smooth, ψ is convex, and F has a minimizer with ‖x*‖ ≤ R.
- Case 3: each fᵢ is convex with |fᵢ(x) − fᵢ(y)| ≤ L‖x − y‖, ψ is μ-strongly convex, and F(0) − F* ≤ Δ.
- Case 4: each fᵢ is convex with the same slope bound L, ψ is convex, and F has a minimizer with ‖x*‖ ≤ R.

For nonsmooth fᵢ, the oracle returns a fixed subgradient, given below for each instance. The classical lower bounds of [3] are Ω(n + R√(nℓ/ε)), Ω(n + L√(n/(με))) and Ω(n + LR√n/ε). The quantum lower bounds of [1] are Ω(n + n^{3/4}(ℓ/ε)^{1/4}R^{1/2}/log n), Ω(n + n^{3/4}(εμ)^{−1/4}L^{1/2}/log n) and Ω(n + n^{3/4}(LR/ε)^{1/2}/log n).

**Theorem 3.** Let n ≥ 600. In Case 3, R stands for √(6ε/μ)/L, as fixed below. Let R_q ≥ 2R in Case 2 and R_q ≥ 3R/2 in Cases 3 and 4, and take k, c from the constants below, in the scaled units in which ℓ = R = 1 (Case 2) or L = 1 (Cases 3 and 4), with R_q scaled the same way, s = ⌊4R_q²/c²⌋ and A = 400(k+1)²s. Suppose

d ≥ N(k+1)A + (8R_q²/c²) ln(40 N(k+1)A).

Then every quantum algorithm whose queries are supported on ‖x‖ ≤ R_q, and which outputs an expected ε-optimal point on every instance, makes at least the following number of queries.

| Case | Queries | Parameter range |
|---|---|---|
| 2 | 4·10⁻¹⁰ R√(nℓ/ε) | ε ≤ ℓR²/(768n) |
| 3 | 2·10⁻¹⁰ L√(n/(με)) | ε ≤ 1.5·10⁻⁴ L²/(nμ) and ε ≤ μΔ²/(6L²) |
| 4 | 8·10⁻¹¹ LR√n/ε | ε ≤ LR/(200√n) |

In each range the bound is at least a constant times n. So the bounds are Ω(n + R√(nℓ/ε)), Ω(n + L√(n/(με))) and Ω(n + LR√n/ε), which are the classical lower bounds of [3]. In Case 2, as in Case 1, quantum gradient queries give no speedup in high dimension. In Cases 3 and 4, the classical bounds of [3] are for algorithms with prox oracles, which can be stronger than subgradient queries; so in high dimension quantum subgradient queries do no better than classical prox queries. The same holds in the model of [1, Corollaries 4 to 6], with an ε-optimal output with probability at least 2/3, since the proof only uses that the output is 3ε-optimal with probability at least 2/3.

In these cases, an ε-optimal point only has to correlate with the vectors of half of the chains, so the strong direct product theorem is replaced by its threshold form [4, Theorem 5.5], applied to one bit per chain. A small regularizer (μ₀/2)‖x‖² keeps the output in a ball, which the decoding needs. When ψ only has to be convex, ψ = (μ₀/2)‖x‖² is allowed.

### Case 2

Scale so that ℓ = R = 1. Define the following constants:

- N = ⌊n/2⌋ and a = 1/(16n);
- k is the largest integer with (k+1)(k+2) ≤ 1/(128nε), so that k ≥ 1 when ε ≤ 1/(768n);
- C = √(9/(4N(k+1))), c = √(3ε/(k+1)) and μ₀ = 6ε.

The instance is the following:

- f_{2i−1}(x) = (1/16)(y_{i,0}² − 2Cy_{i,0} + Σ_{r even} φ_c(y_{i,r−1} − y_{i,r}));
- f_{2i}(x) = (1/16)(φ_c(y_{i,k}) + Σ_{r odd} φ_c(y_{i,r−1} − y_{i,r}));
- f_n = 0 if n is odd;
- ψ(x) = (μ₀/2)‖x‖².

This is [1, Definition 4] with other constants and the regularizer added. Each fᵢ is convex and 1-smooth: the second-derivative bounds are (1/16) · 8 and (1/16)(6 + 2√5) < 1.

Per chain, F carries G₂(y) = G(y) + (μ₀/2)‖y‖², where

G(y) = a(y₀² − 2Cy₀ + Σ_{r=1}^{k} φ_c(y_{r−1} − y_r) + φ_c(y_k)).

Let H be G with φ_c(z) replaced by z². Then H(y) = a(yᵀMy − 2Cy₀), where yᵀMy = y₀² + Σ_r (y_{r−1} − y_r)² + y_k² is the path second-difference matrix with both ends grounded. Its minimizer is ŷ_r = C(k+1−r)/(k+2), and H(y) − H(ŷ) = a(y − ŷ)ᵀM(y − ŷ). The inverse of M has diagonal entries (M⁻¹)_{tt} = (t+1)(k+1−t)/(k+2) ≤ (k+2)/4.

**Lemma 6 (Case 2).** The following hold:

- (a) F has a minimizer x* with ‖x*‖² ≤ 13/16.
- (b) If at least N/2 chains i each have some t ≤ ⌊k/2⌋ with |⟨x, v_{i,t}⟩| < c/2, then F(x) − F* > 3ε.

*Proof.* (a) Let x̂ have the coordinates ŷ on every chain and be 0 elsewhere. Then ‖x̂‖² = NC²(k+1)(2k+3)/(6(k+2)) ≤ NC²(k+1)/3 = 3/4. Also F(x*) ≤ F(x̂), with (1/n)Σfᵢ(x̂) ≤ NH(ŷ) and (1/n)Σfᵢ(x*) ≥ N(H(ŷ) − 2ac²(k+1)). These give (μ₀/2)‖x*‖² ≤ (μ₀/2)‖x̂‖² + 2Nac²(k+1). So ‖x*‖² ≤ 3/4 + N/(8n) ≤ 13/16.

(b) Take a chain i with such a t, and write δ = |yᵢ,t − ŷ_t|.

1. Since ŷ_t ≥ C/2 for t ≤ k/2, we have δ ≥ (C − c)/2.
2. Minimizing the quadratic form with one coordinate fixed gives (y − ŷ)ᵀM(y − ŷ) ≥ δ²/(M⁻¹)_{tt} ≥ 4δ²/(k+2).
3. Hence G₂(yᵢ) − min G₂ ≥ 4aδ²/(k+2) − 2ac²(k+1) − (μ₀/2)‖ŷ‖².

Sum over the bad chains, of which there are at least ⌈N/2⌉; the other chains and the part orthogonal to all chains contribute at least their minimum. For the first term use at least ⌈N/2⌉ ≥ N/2 chains. For the last two terms use at most N chains, with N(μ₀/2)‖ŷ‖² = (μ₀/2)‖x̂‖² and N · 2ac²(k+1) ≤ 3ε/16. This gives

F(x) − F* ≥ 9(1 − c/C)²/(128n(k+1)(k+2)) − 3/16 ε − (μ₀/2)‖x̂‖².

Now c²/C² = 4Nε/3 ≤ 0.001, so the first term is at least 8ε. The last term is at most 2.25ε. Hence F(x) − F* ≥ 5.5ε > 3ε. ∎

### Cases 3 and 4

Scale so that L = 1. Fix R > 0 and define the following constants:

- N = ⌊n/2⌋;
- k + 1 = ⌊R/(100√n ε)⌋, so that k ≥ 1 when ε ≤ R/(200√n);
- b = R/(2√(N(k+1))), c = b/(2(k+1)) and γ = 1/√(2(k+1)).

Let χ_c(z) = max{0, |z| − c}, with subgradient sign(z)·[|z| > c]. The oracle returns the minimum-norm subgradient, which these formulas give. The instance is the following:

- f_{2i−1}(x) = (1/√2)|b − y_{i,0}| + γ Σ_{r even} χ_c(y_{i,r−1} − y_{i,r}), with subgradient sign 0 at b = y_{i,0};
- f_{2i}(x) = γ Σ_{r odd} χ_c(y_{i,r−1} − y_{i,r});
- f_n = 0 if n is odd;
- ψ(x) = (μ₀/2)‖x‖², with μ₀ = 6ε/R².

This is [1, Definition 5] with other constants and a regularizer. Each fᵢ is convex with slope bound 1: a subgradient of f_{2i−1} has squared norm at most 1/2 + γ² · 2 · (k/2) ≤ 1, and one of f_{2i} at most γ² · 2 · (k+1)/2 = 1/2.

For Case 3, take μ₀ = μ and R = √(6ε/μ).

**Lemma 7 (Cases 3 and 4).** The following hold:

- (a) (1/n)Σfᵢ has the minimizer x° = b Σ_{i,r} v_{i,r}, with ‖x°‖ = R/2 and value 0. So F has a minimizer of norm at most R/2, and F* ≤ μ₀R²/8 = 0.75ε.
- (b) If at least N/2 chains i each have some t ≤ k with |⟨x, v_{i,t}⟩| < c/2, then F(x) − F* > 3ε.
- (c) F(0) − F* ≤ R/(4√2).

*Proof.* (a) Every term vanishes at x°. The minimizer of F = (1/n)Σfᵢ + (μ₀/2)‖x‖² has norm at most that of any minimizer of (1/n)Σfᵢ.

(b) For a chain i with such a t, the triangle inequality gives |b − y₀| + Σ_{r ≤ t} |y_{r−1} − y_r| ≥ b − c/2. Since γ ≤ 1/√2,

(1/n)(f_{2i−1} + f_{2i})(x) ≥ (γ/n)(b − c/2 − tc) ≥ γb/(2n).

Sum over at least N/2 chains, and use N ≥ n/3. This gives

F(x) − F* ≥ Nγb/(4n) − 0.75ε ≥ R/(8√6 √n (k+1)) − 0.75ε ≥ 100ε/19.6 − 0.75ε > 4ε.

(c) F(0) = (N/n)b/√2 ≤ b/(2√2) ≤ R/(4√2), and F* ≥ 0. ∎

For Case 3, (c) gives F(0) − F* ≤ Δ when R ≤ Δ, that is, when ε ≤ μΔ²/6.

### Bits of chains

Let A be even and h ≤ k, and let g_h(m) = m_h mod 2 on the chain problem of Section 2.

**Lemma 8.** Let A ≥ 400(k+1)²s.

- (a) Q_{1/4}(g_h) ≥ h + 1.
- (b) Consider an algorithm for N independent chains that outputs one bit per chain, such that the joint law of its correct bits is the same on every input. If it makes fewer than 10⁻⁷ N(h+1) queries, then the probability that at least 0.7N bits are correct is at most e^{−0.037N}.

*Proof.* (a) The hybrid argument of Lemma 3 applies: with at most h queries, the hybrid run does not depend on m_h, so it guesses the parity with probability 1/2. The final success is at most 1/2 + 1/5 < 3/4.

(b) By [4, Theorem 3.3], Adv*(g_h) ≥ Q_{1/4}(g_h)/1000 ≥ (h+1)/1000. Apply [4, Theorem 5.5] with δ = 0.01, K = 100 and threshold 0.7 ≥ (1 + √δ)/2. Its proof bounds the biases β_S = E Πᵢ∈S Yᵢ of products of correctness signs through the step Q_{(1−β_S)/2}(⊕∘f^{(|S|)}) ≤ T, which needs β_S to be a bias reached on every input. Under our assumption β_S is the same on every input, so the step is valid. A finite mixture of query algorithms is again a query algorithm, so internal randomness is allowed. The bound is e^{N/100 − N·D(0.7‖0.55)} with D(0.7‖0.55) > 0.0471. ∎

*Proof of Theorem 3.* Take h = ⌊k/2⌋ in Case 2 and h = k in Cases 3 and 4. Let Γ be the finite group of relabelings of the candidate indices that permute [A] arbitrarily at every position j ≠ h of every chain, and at position h permute [A] so that the parity of every label is kept or flipped at once. Γ acts transitively on the inputs, and g_h(π(m)) is g_h(m) or 1 − g_h(m), as fixed by π alone. B works as follows.

1. Pick a frame of candidates from a fixed finite set (chosen below) and a relabeling π ∈ Γ, both uniformly at random. Use u_{i,j,π(α)} as the candidate with label α.
2. Simulate O_F with two chain queries per query (Lemma 4), and run the algorithm.
3. For each chain i, if exactly one candidate u_{i,h,π(α)} has |⟨x, u⟩| ≥ c/2, output the parity of α. Otherwise output a fresh random bit.

**Symmetry.** On input m with relabeling π, B behaves as B without relabeling on input π(m). Its output bit flips together with g_h, so a bit is correct in one run exactly when it is correct in the other. Since π(m) is uniform over all inputs for every m, the joint law of B's correct bits is the same on every input. It equals the average over a uniform input.

**Frames.** With the relabeling in place a single good frame would do; for simplicity we argue with a set of frames. For a uniformly random frame, the success estimate below holds for every input. Draw a large finite number of frames independently. By the tail bound for bounded independent variables, the average over these frames and a uniform input stays within 0.01 of its average value for some outcome of the draw, and B uses that set.

**Success.** By the first moment inequality, F(x) − F* < 3ε with probability at least 2/3. On that event:

- By Lemmas 6 and 7, fewer than N/2 chains are bad, and every other chain has |⟨x, v_{i,h}⟩| ≥ c/2.
- By strong convexity with μ₀, ‖x‖ ≤ ‖x*‖ + √(6ε/μ₀), which is less than 2R in Case 2 and at most 3R/2 in Cases 3 and 4, so at most R_q.

With probability at least 1 − 1/20, no false candidate passes the threshold (as in Lemma 5, with R_q in place of R). Then every good chain is decoded correctly, and a bad chain is either decoded correctly or gets a coin.

**Counting.** Let m < N/2 be the number of coins. At least 0.7N bits are correct unless fewer than m − 0.3N coins are correct. For m > 0.3N this is at least 0.05N below the mean m/2, so by the tail bound for bounded independent variables it has probability at most e^{−2(0.05N)²/m} ≤ e^{−0.01N}. So the probability of at least 0.7N correct bits is at least 2/3 − 1/20 − e^{−0.01N} − 0.01 > e^{−0.037N} for N ≥ 300.

**Conclusion.** By Lemma 8, 2T ≥ 10⁻⁷ N(h+1). With the definitions of k:

- in Case 2, N(h+1) ≥ √n R/(117.6√ε);
- in Case 4, N(k+1) ≥ √n R/(600ε);
- in Case 3, with R = √(6ε/μ), N(k+1) ≥ √6 √n/(600√(με)).

Undoing the scaling gives the table. ∎

## Remarks

1. **The alphabet.** In the query problem of [1, Problem 3], each chain entry takes one of two known values. A query can then cover the four extensions of a known prefix by two entries, and quantum search on four items finds the right one with a single query. So a plain hybrid argument does not apply to the two-valued chains. The bound in [1] comes from an adversary argument and reads n√k. With A ≥ 400(k+1)²s values per entry, a query that guesses an unknown key succeeds with amplitude O(√(s/A)). Then the single chain needs k + 1 queries, and the strong direct product theorem [4] extends this to the superposition over the n components.

2. **The constants of [1, Lemma 5].** The proof of that lemma finds the minimum −μ̃C²(√Q − 1)²/16 for each chain. The next line there gives the gap at 0 as μC²(√Q − 1)²/16, with μ in place of μ̃, which may be the source of the difference. With the printed constant C = √(Δ/μ) · 4/(√Q − 1), the minimum hints at F(0) − F* = nΔ rather than Δ, and the check below finds nΔ for n = 2, 4 and 8. Using Δ/n in place of Δ in that lemma seems to restore F(0) − F* ≤ Δ. This changes only the argument of the logarithm in [1, Corollary 3]. The instance above sets C directly, so that Lemma 1 holds.

3. **Query norm.** Theorems 1 and 3 hold for every finite query radius, with d growing like its square.

## Check

`sim/finitesum_check.py`, run with `python sim/finitesum_check.py` (NumPy and SciPy), checks the following:

- Lemma 1 and Lemma 2 for five parameter sets. It pins one chain coordinate to ±c/2 and minimizes, and it computes F(0) − F*.
- Remark 2, with the constants of [1].
- Lemma 6 for four parameter sets, in the same way, and the bound on ‖x*‖.
- Lemma 7 for four parameter sets, by a linear program for each pinned coordinate.
- Convexity and smoothness in Cases 1 and 2, from second derivatives at random points, and the slope bound in Cases 3 and 4, from subgradients at random points.
- Lemma 4 on 3000 random queries, comparing the true gradients with those rebuilt from the revealed keys.

Pinning a coordinate to ±c/2 suffices for Lemmas 2 and 6, by convexity.

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
Case 2, n=2 eps=1e-06: k=61, |x*|^2=0.707 <= 13/16, gap of ceil(N/2) bad chains 17.53 eps > 3 eps
Case 2, n=4 eps=1e-05: k=12, |x*|^2=0.685 <= 13/16, gap of ceil(N/2) bad chains 9.03 eps > 3 eps
Case 2, n=8 eps=1e-06: k=29, |x*|^2=0.702 <= 13/16, gap of ceil(N/2) bad chains 9.51 eps > 3 eps
Case 2, n=600 eps=1e-08: k=34, |x*|^2=0.703 <= 13/16, gap of ceil(N/2) bad chains 8.76 eps > 3 eps
Cases 3, 4, n=2 eps=1e-05: k=706, per-chain gap 1.251e-04 >= gamma b/(2n), bad chains minus mu0 R^2/8: 11.76 eps > 3 eps
Cases 3, 4, n=4 eps=0.0001: k=49, per-chain gap 6.312e-04 >= gamma b/(2n), bad chains minus mu0 R^2/8: 5.56 eps > 3 eps
Cases 3, 4, n=8 eps=1e-05: k=352, per-chain gap 3.134e-05 >= gamma b/(2n), bad chains minus mu0 R^2/8: 5.52 eps > 3 eps
Cases 3, 4, n=600 eps=1e-06: k=407, per-chain gap 4.174e-08 >= gamma b/(2n), bad chains minus mu0 R^2/8: 5.51 eps > 3 eps
components convex, largest second-derivative eigenvalue seen 0.499 <= 1 (k=20)
Case 2 components (k=7): largest second-derivative eigenvalue seen 0.655 <= (6 + 2 sqrt 5)/16 < 1
Case 2 components (k=8): largest second-derivative eigenvalue seen 0.500 <= (6 + 2 sqrt 5)/16 < 1
Cases 3, 4 components (k=9): largest subgradient norm seen 0.949 <= 1
gradient simulation exact on 3000 queries (k=4, A=6), largest candidate set total 7
```

## References

1. Y. Zhang, C. Zhang, C. Fang, L. Wang, T. Li. Quantum Algorithms and Lower Bounds for Finite-Sum Optimization. ICML 2024, arXiv:2406.03006.
2. Z. Allen-Zhu. Katyusha: The First Direct Acceleration of Stochastic Gradient Methods. STOC 2017, arXiv:1603.05953.
3. B. Woodworth, N. Srebro. Tight Complexity Bounds for Optimizing Composite Objectives. NeurIPS 2016, arXiv:1605.08003.
4. T. Lee, J. Roland. A strong direct product theorem for quantum query complexity. CCC 2012, arXiv:1104.4468.
5. C. H. Bennett, E. Bernstein, G. Brassard, U. Vazirani. Strengths and weaknesses of quantum computing. SIAM J. Comput. 26(5), 1997, arXiv:quant-ph/9701001.
