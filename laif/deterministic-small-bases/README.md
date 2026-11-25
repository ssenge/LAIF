# Deterministic small bases: strong primality test, splitting from the exponent, power nonresidues

Written 24 Nov 2026.

**Setting.** For n > 2 let (Z/nZ)^× be the unit group. The bound on small non-members says: every proper subgroup of (Z/nZ)^× misses the residue of some positive integer a ≤ B(n) (a is not a unit modulo n, or its residue lies outside the subgroup). Under the hypothesis that all character L-functions have no zeros with Re s > 1/2, this holds with B(n) = O(log² n) [1, 2], with explicit constants in [2]. That hypothesis is proved in Lean in [3], for every modulus and imprimitive characters included. The classical results below, proved in [6, 2, 8] under that hypothesis, therefore hold without further hypotheses, given the bound of [2] and the Lean proof in [3]. The contribution of this folder is a Lean proof of the algebraic reduction from the bound on small non-members to each of them.

| | Problem | Previous best bound (unconditional, deterministic) | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Primality of n | Õ(log⁶ n) [4] | strong probable prime test with all bases a ≤ B(n): Õ(log⁴ n) bit operations, implied by [2, 6] and [3] | Lean (correctness, from the bound of [2] as a stated hypothesis); cost: Claim |
| Thm 2 | Splitting N, given a multiple 2^s m of the exponent of (Z/NZ)^× (for example φ(N)), N odd and not a prime power | polynomial under size conditions on the prime factors of N [5] | some base a ≤ B(N) gives a divisor by one gcd: deterministic, polynomial in log N and in the bit length of the multiple, implied by [2, 6] and [3] | Lean (existence of the base and the gcd step); cost: Claim |
| Cor 3 | An r-th power nonresidue modulo a prime p, for 1 < r ∣ p − 1 | no deterministic polynomial algorithm for general p and r | the least one is ≤ B(p), implied by [1, 2] and [3]; with it, r-th roots modulo p in deterministic time polynomial in log p and r [8] | Lean (existence below B(p)) |

## The common lemma

Write the multiple as 2^s m with m odd. A unit u passes when u^m = 1 or u^{2^j m} = −1 for some j < s.

**Lemma 1.** Let N = n₁ n₂ with n₁, n₂ > 2 coprime. Then the passing units lie in a proper subgroup of (Z/NZ)^×.

*Proof.* Let j₀ be the largest j ≤ s for which some unit b has b^{2^j m} = −1 (j = 0 qualifies, with b = −1, since m is odd). Let H be the set of units u with u^{2^{j₀} m} = ±1, a subgroup. A passing unit lies in H: if u^m = 1, then u^{2^{j₀} m} = 1; if u^{2^j m} = −1, then j ≤ j₀ by the choice of j₀, and u^{2^{j₀} m} is (−1)^{2^{j₀−j}} = ±1. By the Chinese remainder theorem take c ≡ b modulo n₁ and c ≡ 1 modulo n₂. Then c^{2^{j₀} m} ≡ −1 modulo n₁ and ≡ 1 modulo n₂, so it is neither 1 nor −1, and c ∉ H. ∎

## Theorem 1, the proof

Let n > 2 be odd, n − 1 = 2^s m with m odd, and suppose n is composite and passes for all bases a ≤ B(n). A base that passes is a unit modulo n. If some unit u has u^{n−1} ≠ 1, the units with u^{n−1} = 1 form a proper subgroup that contains every passing unit. Otherwise every unit satisfies u^{n−1} = 1, and such n is squarefree [7], so n = p · (n/p) for its least prime factor p, with coprime factors above 2, and Lemma 1 applies. In both cases the bound on small non-members gives a base a ≤ B(n) outside the subgroup, which does not pass. ∎

**Cost.** Each of the B(n) = O(log² n) bases takes O(log n) multiplications modulo n, so the test takes O(log³ n · M(log n)) = Õ(log⁴ n) bit operations, with M(k) the cost of multiplying k-bit integers.

## Theorem 2 and Corollary 3

**Theorem 2** (the reduction of [6]). With a multiple 2^s m of the exponent of (Z/NZ)^× and N = n₁ n₂ as in Lemma 1, some base a ≤ B(N) is not a unit modulo N, or has y = a^{2^j m} with y² = 1 and y ≠ ±1 for some j < s. In the first case gcd(a, N) is a proper divisor, since the base can be taken below N; in the second, gcd(y − 1, N) is one.

*Proof.* Lemma 1 and the bound on small non-members give a base a outside the subgroup of Lemma 1. If a is a unit, it does not pass, while a^{2^s m} = 1. The last j with a^{2^j m} ≠ 1 gives y. If y − 1 were a unit, (y − 1)(y + 1) = y² − 1 = 0 would force y = −1, and y − 1 ≢ 0 since y ≠ 1; so 1 < gcd(y − 1, N) < N. ∎

An odd N that is a prime power is detected by integer root extraction, so Theorem 2 splits every odd composite N given φ(N), λ(N) or any multiple of λ(N), with O(B(N) · (s + log m)) multiplications modulo N.

**Corollary 3.** The r-th powers form a proper subgroup of (Z/pZ)^× when 1 < r ∣ p − 1, since a prime q ∣ r gives a unit of order q, so the r-th power map is not injective and hence not onto. The bound on small non-members gives a nonresidue a ≤ B(p), and capping B at p − 1 makes it a unit. The root-extraction algorithm of [8] needs such a nonresidue and runs in time polynomial in log p and r.

## Scripts

`sim/check_bases.py` checks, by brute force, the bound B(n) = 2 (ln n)² on small ranges: the least strong witness of every odd composite n < 20000, a splitting base of Theorem 2 for every odd N < 3000 with two coprime factors above 2 (given λ(N), with the gcd asserted to be a proper divisor), and the least r-th power nonresidue for primes p < 20000 and prime r ∣ p − 1.

```
python sim/check_bases.py
(1) least strong witness <= 2 ln^2 n for odd composite n < 20000; largest 3 at n = 15841
(2) a splitting base <= 2 ln^2 N found for all 1044 odd N < 3000 with two coprime factors > 2
(3) least r-th power nonresidue <= 2 ln^2 p for primes p < 20000, prime r | p - 1; largest 29 at p = 18191, r = 2
```

## Lean

The library `SmallBases` in `lean/` (Lean 4, toolchain and Mathlib revision pinned in `lean-toolchain` and `lake-manifest.json`) states the bound on small non-members as the hypothesis `SmallNonmember B` (a `def ... : Prop`, citing [2]) and proves, with only the standard axioms (`lean/axioms.txt`):

* `liars_le_proper`: Lemma 1.
* `split_of_fermat`: an odd composite n > 2 with u^{n−1} = 1 for all units is a product of two coprime factors above 2.
* `prime_of_strongPass`: Theorem 1, correctness.
* `exists_split`, `gcd_split`: Theorem 2, the base (below N) and the gcd step.
* `exists_nonresidue`: Corollary 3, the nonresidue below B(p).
* `smallNonmember_sub_one`, `SmallNonmember.min`: the hypothesis holds with B(n) = n − 1, so it has content, and B can be capped at n − 1.

**Not formalized:** the bit-operation counts, the prime-power test, the root-extraction algorithm of [8], and the bound of [2] itself, which enters as the hypothesis `SmallNonmember`.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. N. C. Ankeny. The least quadratic non residue. Annals of Mathematics 55, 1952.
2. E. Bach. Explicit bounds for primality testing and related problems. Mathematics of Computation 55 (191), 355-380, 1990.
3. A Lean proof of the Riemann hypothesis and of the hypothesis for Dirichlet L-functions, November 2026. https://leanprover-community.github.io/blog/posts/riemann-hypothesis/ Lean library: https://github.com/Deicyde/riemann-hypothesis
4. H. W. Lenstra Jr., C. Pomerance. Primality testing with Gaussian periods. Journal of the European Mathematical Society 21, 2019.
5. F. Morain, G. Renault, B. Smith. Deterministic factoring with oracles. arXiv:1802.08444, 2018.
6. G. L. Miller. Riemann's hypothesis and tests for primality. Journal of Computer and System Sciences 13, 1976.
7. Mathlib, `Nat.IsCarmichael.squarefree` (the squarefree part of Korselt's criterion).
8. L. Adleman, K. Manders, G. Miller. On taking roots in finite fields. 18th Annual Symposium on Foundations of Computer Science, 1977.
