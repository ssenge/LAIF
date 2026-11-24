# Multidimensional quantum factoring and discrete logarithms: one logarithmic factor less

Written 23 Nov 2026.

**Setting.** As in [1]: N ≤ 2^n, d = ⌈√(log N)⌉, and the multidimensional factoring algorithm [2], in its space-efficient form [3] and its discrete logarithm form [4], calls a quantum circuit O(√n) times. The circuit computes products of powers of d small primes b_1, …, b_d modulo N, and the classical part needs the lattice

L = {(e_1, …, e_d, f_1, …, f_r) ∈ Z^{d+r} : b_1^{e_1} ⋯ b_d^{e_d} x_1^{f_1} ⋯ x_r^{f_r} ≡ 1 (mod N)}

to have a basis of short vectors. In [1] this is proved unconditionally for random primes b_i ≤ d^{1000d}, which have O(d log d) bits.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Factoring and discrete logarithms modulo N ≤ 2^n, quantum circuit with O(√n) calls | O(n^{3/2} log³ n) gates and O(n log³ n) qubits [1, Thms 1.1 and 1.2], with O(n log² n) qubits stated in [1, Remark 1.3]; O(n^{3/2} log n) gates and O(n log n) qubits under the number-theoretic conjecture of [2, 3, 4] | O(n^{3/2} log² n) gates and O(n log² n) qubits | Claim, using the zero-free half plane Re s > 1/2 for the L-functions of all characters, proved in Lean in [5]; the inequalities of Lemma 1 checked by script |

That the hypothesis on the zeros would remove a logarithmic factor is noted in [1, Section 1.4 (1)]. Here the proof is given: with that hypothesis, random primes up to X = e^{21d}, of O(d) bits, suffice for the short basis of [1, Thm 3.18], and all other steps of [1] stay as they are.

## The second-moment bound

For a character χ modulo N and H ≥ 1 let F_{χ,H}(b) = ∏_{i ≤ d} Σ_{|h| ≤ H} χ^h(b_i), as in [1, Definition 3.6].

**Lemma 1.** Let X = e^{21d}, let b_1, …, b_d be independent and uniform among the primes up to X not dividing N, and let H ≥ e^{10d}. Assume that L(s, ψ) has no zero with Re s > 1/2 for every non-principal character ψ modulo N, primitive or not. (This holds by [5]; for an imprimitive ψ it also follows from the primitive case, since the two L-functions differ by finitely many Euler factors, whose zeros lie on Re s = 0.) Then, for d large enough,

Σ_{χ : ord(χ) ≥ e^{10d}} E[|F_{χ,H}(b)|²]^{1/2} ≤ d^{−2d} H^d.

*Proof.* By [1, Prop. 3.9] with α = 1/2, every non-principal ψ satisfies |Σ_{p ≤ X} ψ(p)| ≤ A π(X) X^{−1/2} log³(NX) for an absolute constant A. Since ψ(p) = 0 for p dividing N, at most log₂ N ≤ 2d² primes divide N, and π(X) ≥ 4d² for large d, this gives |E ψ(b_1)| ≤ 2A (d² + 21d)³ e^{−10.5d} ≤ e^{−10d} for d large. As in the proof of [1, Lemma 3.11],

E[|F_{χ,H}(b)|²] ≤ (2H + 1)^d (Σ_{|h| ≤ 2H} |E χ^h(b_1)|)^d.

If ord(χ) ≥ e^{10d}, at most 4H e^{−10d} + 1 of the h with |h| ≤ 2H make χ^h principal, and each of the other at most 4H + 1 terms is at most e^{−10d}. So the inner sum is at most 10 H e^{−10d}, and E[|F_{χ,H}(b)|²] ≤ 30^d e^{−10d²} H^{2d}. There are fewer than N ≤ e^{d²} characters, so the sum in the claim is at most e^{d²} 30^{d/2} e^{−5d²} H^d ≤ d^{−2d} H^d. ∎

Lemma 1 is stronger than the bound that [1, Prop. 3.14] gives for X = d^{1000d} through the zero-density estimate and the exceptional characters of [1, Lemmas 3.11 to 3.13]: it sums over all characters of large order, not only over those trivial on the subgroup used there. With the hypothesis no character is exceptional, and the union bound over all characters suffices.

## Theorem 1, the proof

**Short basis.** The proof of [1, Thm 3.18] uses the primes b_i only through [1, Prop. 3.14]; the main term [1, Lemmas 3.7 and 3.8], the auxiliary lattice L_M with M ≤ e^{10d} [1, Lemma 3.4] and the geometry of numbers [1, Lemmas 3.16 and 3.17] hold for all b_i in (Z/NZ)^×. With Lemma 1 in place of [1, Prop. 3.14], the lattice L has a basis of vectors of ℓ₂ norm at most e^{42(d+r)} with probability 1 − O(d^{−d}), for random primes b_i ≤ e^{21d}.

**Sampling.** A uniform integer up to X is a prime not dividing N with probability at least c/log X = c/(21d), so d⁴ samples contain d such primes with probability 1 − O(1/N), as in [1, Lemma 4.3].

**Cost.** The only step of the circuit of [3, 4] that depends on the size of the b_i is the product ∏ b_i^{t_i} with t_i ∈ {0, 1} [1, Section 4.2]. For d numbers of m bits it takes O(m d log d · log(md)) operations [1, Lemma 4.1], and a reversible circuit of the same order of gates and qubits. With m = O(d) this is O(d² log² d) = O(n log² n), in place of O(d² log³ d) for m = O(d log d) in [1]. The circuit of [3, Lemma 5] then has O(d(n log n + n log² n)) = O(n^{3/2} log² n) gates, and the qubit count is O(n log n) plus the O(n log² n) of the product, with the plain conversion of [1, Lemma 4.2] from classical to quantum circuits. The classical parts, the extra uniform element x for factoring [1, Lemma 4.5] and the discrete logarithm reduction [1, Section 4.2] are unchanged. ∎

The remaining logarithmic factor is the gap between primes of O(d) bits and the primes of O(log d) bits assumed in [2, 3, 4]. A related question, how many small primes with exponents 0 or 1 generate (Z/qZ)^× for almost all q, is studied in [6]. In Lemma 1 the bound on each character must beat the number of characters, about e^{d²}, which needs log X of order d; the case X = d^{O(1)} stays open.

## Scripts

`sim/check_bounds.py` checks the two inequalities of Lemma 1 numerically (the character bound from some d on for several values of A, and the union over e^{d²} characters for 2 ≤ d < 5000), and compares the product cost m d log d log(md) for m = log₂(d^{1000d}) and m = log₂(e^{21d}); the ratio divided by log₂ d stays near a constant.

```
python sim/check_bounds.py
A=1: 2A (d^2+21d)^3 e^(-10.5d) <= e^(-10d) for all checked d >= 51
A=10: 2A (d^2+21d)^3 e^(-10.5d) <= e^(-10d) for all checked d >= 57
A=1000: 2A (d^2+21d)^3 e^(-10.5d) <= e^(-10d) for all checked d >= 68
A=1e+06: 2A (d^2+21d)^3 e^(-10.5d) <= e^(-10d) for all checked d >= 84
e^{d^2} 30^{d/2} e^{-5d^2} <= d^{-2d} for 2 <= d < 5000
n=1024: product cost old/new divided by log2 d = 49.3
n=4096: product cost old/new divided by log2 d = 47.9
n=16384: product cost old/new divided by log2 d = 46.7
n=65536: product cost old/new divided by log2 d = 45.7
```

**Not formalized:** all of the folder. The results of [1] used above, the explicit formula behind [1, Prop. 3.9], and the circuits of [3, 4] are taken from the literature, and the hypothesis on the zeros from [5].

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. C. Pilatte. Unconditional correctness of recent quantum algorithms for factoring and computing discrete logarithms. arXiv:2404.16450, 2024.
2. O. Regev. An efficient quantum factoring algorithm. arXiv:2308.06572, 2023.
3. S. Ragavan, V. Vaikuntanathan. Space-efficient and noise-robust quantum factoring. arXiv:2310.00899, 2023.
4. M. Ekerå, J. Gärtner. Extending Regev's factoring algorithm to compute discrete logarithms. arXiv:2311.05545, 2023.
5. A Lean proof of the Riemann hypothesis and of the hypothesis for Dirichlet L-functions, November 2026. https://leanprover-community.github.io/blog/posts/riemann-hypothesis/ (theorem list: https://math.mit.edu/~drew/grh/). Lean library: https://github.com/Deicyde/riemann-hypothesis
6. On the generation of multiplicative groups by small primes. arXiv:2609.25393, 2026.
