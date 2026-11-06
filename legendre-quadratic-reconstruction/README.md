# Quadratic polynomials behind the Legendre symbol

Written 6 Nov 2026.

Given oracle access to x ↦ χ(f(x)) for an unknown polynomial f over a finite field, with χ the Legendre symbol (or another multiplicative character), the task is to find f. For linear f this is the shifted Legendre symbol problem, which van Dam, Hallgren and Ip [1] solved in quantum polynomial time. For degree d ≥ 2, Russell and Shparlinski [2] showed that O(d) quantum queries suffice, but no time-efficient quantum algorithm was known; the question is stated as open in the survey of Childs and van Dam [3]. Ivanyos, Karpinski, Santha, Saxena and Shparlinski [4] give a quantum algorithm with classical queries in time about e^{d/2} for the oracle x ↦ f(x)^e, which is about p for quadratics under the Legendre symbol, e = (p − 1)/2. For quadratics, classical collision methods in the style of [7, 8, 12] reach about √p, and quantum collision search about p^{1/3} (Section 2). Superposition access to the oracle is assumed, as in [1, 2].

**Theorem 1 (hidden constant term).** Let F be a finite field with q elements, χ a nontrivial multiplicative character of F, and f = h − D with h ∈ F[X] known of degree d ≥ 1 and D ∈ F unknown. A quantum algorithm with one oracle call (two for a non-real χ) and poly(d, log q) further operations outputs D, in the ideal circuit, with probability exactly

  Σ_{j ≥ 0} |H_j ∖ {D}|² / q²  ≥  (1 − d/q)² / d,

where H_j is the set of values y with more than j preimages under h. For a monomial h = x^d this is about 1/gcd(d, q − 1), and for every quadratic h over a field of odd characteristic it is about 1/2. In particular, a monic quadratic x² + bx + c with known b is recovered in polynomial time.

**Theorem 2 (all squarefree monic quadratics).** Let p be an odd prime and χ the Legendre symbol. A quantum algorithm recovers every monic squarefree quadratic f over F_p from the oracle x ↦ χ(f(x)) in time and query count 2^{O(√log p)}, with O(log p) quantum space and 2^{O(√log p)} classical space.

The method of Theorem 2 writes f(x) = (x + s)² − D with D ≠ 0. The function χ(f(x)) is symmetric under the reflection x ↦ −2s − x. For random offsets a₁, …, a_m with m = O(log p), the vectors

  f₀(x) = (χ(f(x + a_i)))_i,  f₁(x) = (χ(f(−x − a_i)))_i

satisfy f₁(x) = f₀(x − 2s) exactly, and f₀ is injective with high probability by the Weil bound. The injectivity makes the labels of the resulting coset states exactly uniform. This is the abelian hidden shift problem on Z_p with injective functions, equivalent to the dihedral hidden subgroup problem, which Kuperberg's sieve [5, 6] solves in time 2^{O(√log p)}. Theorem 1 then gives D, and a classical test on random points confirms f. The squarefree condition excludes f = (x + s)², where χ(f(x)) = 1 except at one point and Ω(√p) queries are necessary.

Status: Claim. The exact amplitude identity, the success probability of Theorem 1 for each measured rank, the norm of the Gauss sum, the hidden shift identity and the union bound for injectivity (with the Weil bound as a hypothesis) are in Lean. Theorem 1 and the reduction of Theorem 2 are checked by exact state-vector simulation, and the sieve and phase estimation by a label-level simulation for primes up to 2³².

## Before and after

| Category | Problem | Before | After | Scope | Status |
|---|---|---|---|---|---|
| Quantum algorithms, algebraic problems | Reconstruct a monic squarefree quadratic f over F_p from χ(f(x)), χ the Legendre symbol | O(1) quantum queries without an efficient algorithm [2]; quantum time about p with classical queries [4]; classical O(p log p) [12]; classical Õ(√p) and quantum Õ(p^{1/3}) by collision search on the reflection symmetry (Section 2) | Time and queries 2^{O(√log p)} | Superposition oracle | Claim; identities in Lean; simulation |
| Quantum algorithms, algebraic problems | Recover the constant term D of f = h − D from χ(f(x)), h known of degree d, any nontrivial character of F_q | Linear h: polynomial time [1]; degree ≥ 2: classical poly(q) from all q values for deg f ≤ ε√q [16], otherwise as above | One query and poly(d, log q) time, success probability at least (1 − d/q)²/d, exactly computable | Superposition oracle, any finite field | Claim; success probability per measured rank in Lean; simulation |

## Prior work

The linear case and its quantum algorithm are from [1], with the shifted Legendre symbol conjectured classically hard there. The query complexity of reconstructing polynomials of degree d through character values is O(d) [2], and the time-efficient version is listed as open in [3]. [4] studies the oracle x ↦ f(x)^e with classical access and gives a quantum algorithm in time e^{d/2} poly(d log q) and a randomized one in time e^d poly(d log q). Classical key-recovery algorithms for the Legendre pseudorandom function and its higher-degree variant [7, 8, 12] use collisions among many classical queries; for degree 2, [12] gives O(p log p) Legendre symbol evaluations. A classical algorithm in time poly(q) recovers a polynomial of degree at most ε√q up to square factors from the full table of χ(f(x)), x ∈ F_q, even with a small constant fraction of errors [16]; it reads all q values, while the algorithms here make poly(log q) or 2^{O(√log p)} queries. Frixons and Schrottenloher [13] apply Kuperberg's hidden shift algorithm to the linear case with classical queries. Childs, Schulman and Vazirani [14] study hidden nonlinear structures, where Legendre symbols and Kloosterman sums also appear. Decker, Ivanyos, Santha and Wocjan [9] treat hidden symmetries under group actions for oracles whose level sets are exactly the orbits, which χ(f) is not; the vectors f₀ supply such an oracle here. Kuperberg's algorithms [5, 6] and Regev's polynomial-space variant [10] solve the dihedral hidden subgroup problem in subexponential time. Kloosterman sums appear as the Fourier coefficients of χ(x² − D); a quantum algorithm prepares a state with all of them as amplitudes in polynomial time, while estimating a single one takes time about √q [11]. The reduction above does not need them. Theorem 1 extends the method of [1] from χ(x + s) to χ(h(x) − D). To our knowledge, Theorems 1 and 2 are new.

## 1. Theorem 1

Let ψ be a primitive additive character of F and g(χ, ψ) = Σ_k χ(k)ψ(k) the Gauss sum, with |g|² = q.

1. Prepare q^{−1/2} Σ_x |x⟩, query χ(f(x)) into a register, measure whether it is zero (it is not, with probability (q − #roots)/q), and apply the phase χ(f(x)) (for the Legendre symbol a sign, for other characters a phase followed by uncomputing the value with a second query).
2. Map x ↦ (y, j) with y = h(x) and j the rank of x among the roots of h(X) − y. This is reversible, since x is the j-th root of h(X) − y. It is computed by a randomized root-finding algorithm over F in poly(d, log q) time, run coherently with classically fixed random coins and with every output root checked by evaluating h; by Markov's inequality, for most choices of coins the circuit fails on a fraction of inputs that is exponentially small, which costs only an exponentially small loss of fidelity. Measure j.
3. The state is now proportional to Σ_{y ∈ H_j} χ(y − D)|y⟩. Apply the Fourier transform |y⟩ ↦ q^{−1/2} Σ_k ψ(ky)|k⟩, multiply by χ(k), apply the inverse transform |k⟩ ↦ q^{−1/2} Σ_z ψ(−kz)|z⟩ and measure.

The amplitude of the outcome D is q^{−1} times

  Σ_k χ(k)ψ(−kD) Σ_y φ(y)ψ(ky) = Σ_y φ(y) Σ_k χ(k)ψ(k(y − D)) = g(χ, ψ) Σ_y φ(y) χ⁻¹(y − D),

using Σ_k χ(k)ψ(ka) = χ⁻¹(a) g(χ, ψ) for every a, including a = 0. With φ(y) = 1_{H_j}(y) χ(y − D) the last sum is |H_j ∖ {D}|, and the norm of φ is √|H_j ∖ {D}|. So, given rank j, the outcome is D with probability |H_j ∖ {D}|/q. The rank j itself is measured with probability |H_j ∖ {D}|/N, where N = Σ_j |H_j ∖ {D}| = #{x : f(x) ≠ 0}, and N/q is the probability of step 1. Multiplying and summing over j gives Σ_j |H_j ∖ {D}|²/q². At most d ranks occur and Σ_j |H_j ∖ {D}| = N ≥ q − d, so by Cauchy-Schwarz the probability is at least (q − d)²/(d q²). A candidate D' is confirmed or rejected by comparing χ(h(x) − D') with the oracle on random points.

For h = x^d with g = gcd(d, q − 1), H_j is the subgroup of g-th powers (with 0 added for j = 0), so the probability is about 1/g. For a quadratic h in odd characteristic, the fibers have size two except at the vertex, and the probability is about 1/2. In characteristic 2, x² + c is a bijection and the probability is about 1.

## 2. Theorem 2

Write f(x) = (x + s)² − D with D ≠ 0, and put t = 2s.

1. **Injective encoding.** Choose m random offsets and set f₀(x) = (χ(f(x + a_i)))_i and f₁(x) = (χ(f(−x − a_i)))_i, each computed with m oracle calls into a value register. Since f(−x − a) = (−x − a + s)² − D = f(x − t + a), f₁(x) = f₀(x − t).
2. **Injectivity.** For x ≠ y the polynomials u(a) = f(x + a) and v(a) = f(y + a) are distinct monic squarefree quadratics, so uv has degree 4 and is not a constant times a square, and the Weil bound gives |Σ_a χ(u(a)v(a))| ≤ 3√p. The two polynomials share at most one root. Hence χ(u(a)) = χ(v(a)) for at most p/2 + 1.5√p + 1 values of a, a fraction β ≤ 1/2 + 2/√p. A union bound over pairs shows that f₀ fails to be injective for at most p²(βp)^m of the p^m offset tuples, so m = ⌈log(2p²)/log(1/β)⌉ = O(log p) gives an injective f₀ with probability at least 1/2. The bound β < 1 needs p > 16; smaller p are handled by exhaustive search.
3. **Coset states.** Preparing 2^{−1/2} Σ_{b, x} |b⟩|x⟩|f_b(x)⟩ and measuring the last register gives (|0⟩|x₀⟩ + |1⟩|x₀ + t⟩)/√2 for a uniformly random x₀. The Fourier transform on the second register and a measurement give a uniform label k and the qubit |0⟩ + ψ(kt)|1⟩: the input of the dihedral hidden subgroup problem on D_p.
4. **Sieve.** Kuperberg's algorithm [5] or his second algorithm [6] (quantum space O(log p)) finds t from 2^{O(√log p)} such states, so s = t/2.
5. **Constant term.** Theorem 1 with h(x) = (x + s)² gives D with probability about 1/2. A wrong candidate f' agrees with f on at most a fraction β of the points by the same Weil argument, so O(log p) random tests confirm the answer, and a failure (for example a non-injective f₀) is caught and the algorithm restarts.

Each coset state costs m oracle calls, since the value register is measured rather than uncomputed, so the total cost is 2^{O(√log p)}.

**Remark (one-query states).** The Fourier coefficients of χ(f) are ψ(−ks) times real Kloosterman-type sums that are even in k, so one query, a Fourier transform and a measurement of the pair {k, −k} already give a qubit |0⟩ + ψ(2ks)|1⟩. Its label then has a distribution proportional to the square of a Kloosterman sum, between 4·10⁻⁵ and 3.9 times uniform at p = 1009, and rescaling x does not change that, since the amplitude depends only on k. The injective encoding is used because it gives exactly uniform labels, the input for which [5, 6] are analysed.

**Collision baselines.** The windows W(x) = (χ(f(x + j)))_{j < L} and R(y) = (χ(f(y − j)))_{j < L} with L = O(log p) satisfy W(x) = R(−2s − x), so a collision between about √p classical samples of each gives s, and then χ(f(λz − s)) = χ(z² − D/λ²) lets a second collision against a table of (χ(z_j² − r))_j give D. This takes Õ(√p) classical time and queries. Storing p^{1/3} windows W, a random y has a matching R(y) with probability about p^{−2/3}, so Grover search finds one with about p^{1/3} queries, as in the method of Brassard, Høyer and Tapp [15]; the second collision is handled in the same way, which gives Õ(p^{1/3}) quantum time and queries.

## 3. Measurements

[`sim/dstep_check.py`](sim/dstep_check.py) ([log](sim/dstep_check.log)) runs the algorithm of Theorem 1 as an exact state vector over F_p for p up to 20011, with h = x², x³, x⁶ and random monic h of degree 2 to 5, including the rank register and its measurement. The probability of the outcome D agrees with Σ_j |H_j ∖ {D}|²/p² to 10⁻¹⁵ in every case: about 1/2 for quadratics and random h, about 1/3 and 1/6 for x³ and x⁶ when 3 and 6 divide p − 1.

[`sim/shift_check.py`](sim/shift_check.py) ([log](sim/shift_check.log)) checks f₁(x) = f₀(x − 2s) on all of F_p and the injectivity of f₀ for p = 1009, 7919, 65537: always injective at m = 3 log₂ p, in about half the instances near the m given by the union bound (26, 29, 34), never at m ≤ 16. It also checks the form of the coset states.

[`sim/sieve.py`](sim/sieve.py) ([log](sim/sieve.log)) is a label-level simulation of a Kuperberg-type sieve on Z_p followed by iterative phase estimation: combining two coset qubits gives the sum or difference of their labels with probability 1/2 each, independently of t, and only the final measurements depend on t. A random hidden t is recovered in every run for primes near 2¹⁶, 2²⁰, 2²⁴, 2²⁸ and 2³². At these sizes the number of oracle calls (10⁷ to 3·10⁸) is far above the collision baselines (about 10⁷ classical queries at 2³²); the gain is asymptotic.

## 4. Limits

- Superposition access to the oracle is needed, as in [1, 2]. With classical access only, [4] applies.
- Theorem 2 runs in subexponential, not polynomial, time; it reaches the dihedral hidden subgroup problem, for which no polynomial-time algorithm is known. Its advantage over the collision baselines is asymptotic.
- Degrees d ≥ 3 with all coefficients unknown are not covered; Theorem 1 covers any degree when only the constant term is unknown.
- Theorem 2 is stated for prime fields and the Legendre symbol; Theorem 1 holds over every finite field and for every nontrivial multiplicative character.

## 5. Formal verification

[`lean/`](lean/) is a Lean 4 library `LegendreRecon` on Mathlib with 9 theorems, no `sorry`, and only the standard axioms (propext, Classical.choice, Quot.sound), as listed by `lean/LegendreRecon/Axioms.lean`. Build with `lake build` in `lean/`.

| Part | Theorems |
|---|---|
| Σ_k χ(k)ψ(ka) = χ⁻¹(a) g(χ, ψ) for all a, over any finite field and nontrivial χ | `sum_char_mul_add` |
| Theorem 1, amplitude of the outcome D: Σ_k χ(k)ψ(−kD) Σ_y w(y)χ(y − D)ψ(ky) = g(χ, ψ) Σ_{y ≠ D} w(y) | `amplitude` |
| \|g(χ, ψ)\|² = q for primitive ψ; \|χ(u)\|² = 1 for u ≠ 0; norm of the start state | `normSq_gaussSum`, `normSq_char`, `normSq_state` |
| Theorem 1, success probability \|H ∖ {D}\|/q for the start state 1_H(y)χ(y − D), that is, for each measured rank | `success_probability` |
| Theorem 2, reflection symmetry and f₁(x) = f₀(x − 2s) | `quad_reflect`, `f1_eq_shift` |
| Theorem 2, at most q² c^m offset tuples give a non-injective f₀ when each pair agrees on at most c offsets | `card_not_injective_le` |

**Not formalized.** The quantum circuits (Fourier transform, coherent root finding, measurement of the rank), the product over the steps, the sum over ranks and the lower bound of Theorem 1; the Weil bound, used as the hypothesis on c; the dihedral hidden subgroup algorithms of [5, 6]; the final classical test.

## References

1. W. van Dam, S. Hallgren, L. Ip. Quantum algorithms for some hidden shift problems. SIAM Journal on Computing 36(3), 763-778, 2006. arXiv:quant-ph/0211140.
2. A. Russell, I. E. Shparlinski. Classical and quantum function reconstruction via character evaluation. Journal of Complexity 20, 404-422, 2004. arXiv:quant-ph/0212016.
3. A. M. Childs, W. van Dam. Quantum algorithms for algebraic problems. Reviews of Modern Physics 82, 1-52, 2010. arXiv:0812.0380.
4. G. Ivanyos, M. Karpinski, M. Santha, N. Saxena, I. E. Shparlinski. Polynomial interpolation and identity testing from high powers over finite fields. Algorithmica 80, 560-575, 2018. arXiv:1502.06631.
5. G. Kuperberg. A subexponential-time quantum algorithm for the dihedral hidden subgroup problem. SIAM Journal on Computing 35(1), 170-188, 2005. arXiv:quant-ph/0302112.
6. G. Kuperberg. Another subexponential-time quantum algorithm for the dihedral hidden subgroup problem. TQC 2013, LIPIcs 22, 20-34. arXiv:1112.3333.
7. D. Khovratovich. Key recovery attacks on the Legendre PRFs within the birthday bound. IACR ePrint 2019/862.
8. W. Beullens, T. Beyne, A. Udovenko, G. Vitto. Cryptanalysis of the Legendre PRF and generalizations. IACR Transactions on Symmetric Cryptology 2020(1), 313-330. IACR ePrint 2019/1357.
9. T. Decker, G. Ivanyos, M. Santha, P. Wocjan. Hidden symmetry subgroup problems. SIAM Journal on Computing 42(5), 1987-2007, 2013. arXiv:1107.2189.
10. O. Regev. A subexponential time algorithm for the dihedral hidden subgroup problem with polynomial space. arXiv:quant-ph/0406151, 2004.
11. P. Bruin. On quantum computation of Kloosterman sums. arXiv:1807.03600, 2018.
12. N. Kaluđerović, T. Kleinjung, D. Kostić. Improved key recovery on the Legendre PRF. ANTS XIV, Open Book Series 4, 2020, doi:10.2140/obs.2020.4.267. IACR ePrint 2020/098.
13. P. Frixons, A. Schrottenloher. Quantum security of the Legendre PRF. Mathematical Cryptology 1(2), 52-69, 2022. IACR ePrint 2021/149.
14. A. M. Childs, L. J. Schulman, U. V. Vazirani. Quantum algorithms for hidden nonlinear structures. FOCS 2007. arXiv:0705.2784.
15. G. Brassard, P. Høyer, A. Tapp. Quantum cryptanalysis of hash and claw-free functions. LATIN 1998, LNCS 1380, 163-169. arXiv:quant-ph/9705002.
16. S. Kopparty. Recovering polynomials over finite fields from noisy character values. arXiv:2601.07137, 2026.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
