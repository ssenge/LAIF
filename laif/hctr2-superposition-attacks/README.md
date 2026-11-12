# HCTR2 and its beyond-birthday variants under superposition queries

Written 5 Nov 2026.

**Paper:** [`paper/main.pdf`](paper/main.pdf), with its source in [`paper/`](paper/).

HCTR2 [1] is a length-preserving tweakable wide-block cipher built from AES and the POLYVAL hash, used for disk and filename encryption, for example in Linux. CHCTR and HCTR2-TwKD [2] and HCTR++ [3] are recent variants with security beyond the birthday bound against classical attackers, proposed in the context of the NIST accordion mode project [4]. This folder gives attacks on all four when the attacker can query the encryption (and for HCTR++ also the decryption) in quantum superposition, the Q2 model of Kaplan, Leurent, Leverrier and Naya-Plasencia [5].

**Theorem 1.** In the Q2 model, with one fixed tweak, Simon's algorithm recovers
- the POLYVAL key of HCTR2 with about n + 2 expected quantum encryption queries of 2 blocks,
- both POLYVAL keys of CHCTR (as an unordered pair) with about 2n + 2 queries of 3 blocks,
- both 2n-bit hash keys h1, h2 of HCTR++ with about 2n + 2 encryption and 2n + 2 decryption queries of 3 blocks,
- the POLYVAL key of HCTR2-TwKD for the attacked tweak with about n + 2 queries, far below its limit of 2^{n/3} block cipher calls per tweak, since a query on 2 blocks costs 2 calls.

For n = 128 these are about 130, 258, 516 and 130 queries. In the ideal cipher model, the bound holds except with probability below 2^{-57} over the cipher. The subgroups do not depend on the tweak, so the queries may also use a different tweak each, such as a nonce (for HCTR2-TwKD, a different inner tweak), with a union bound over the tweaks used. For HCTR++ with a fresh tweak for every query, the failure probability becomes about 516·2^{−61} < 2^{−51}.

**Theorem 2 (universal forgery).** Once the keys are recovered, let S_ℓ be the subgroup of Lemmas 1 to 3 at a target length ℓ, computed from them (S_P for HCTR++). For every target plaintext P of length ℓ its ciphertext is Enc(P ⊕ s) ⊕ s, for any nonzero s ∈ S_ℓ, so one classical query on a different plaintext gives it. The same holds for decryption. S_ℓ is nontrivial for every nonempty rest for HCTR2 (including a partial last block), for a rest of at least two full blocks for CHCTR, and for a rest of at least two full hash blocks of 2n bits for HCTR++, through shifts on the last two blocks. For HCTR2-TwKD it holds under the attacked tweak. In all cases the keys recovered are the hash keys, not the block cipher keys.

Status: Claim. The shift identities, the subgroups, the key recovery, the deterministic part of the uniqueness bounds and the sampling identity of Simon's algorithm, for the output distribution given by its formula, are in Lean. The shift identities are also tested with AES at full size, and the whole attack in exact simulation and in Qiskit at small block sizes.

## Before and after

| Category | Problem | Before | After | Scope | Status |
|---|---|---|---|---|---|
| Quantum cryptanalysis, superposition queries | Key recovery and universal forgery for CHCTR | Security 2n/3 bits (multi-user) against classical attackers, for a multi-user strong pseudorandom AES [2]; no quantum attack known to us | About 2n + 2 quantum queries | Q2 model, one tweak, messages of 3 blocks or more; ideal cipher for the query bound | Claim; algebra and sampling lemma in Lean; AES test at n = 128 |
| Quantum cryptanalysis, superposition queries | Key recovery and universal forgery for HCTR++ | Security beyond the birthday bound against classical attackers in the ideal cipher model [3]; no quantum attack known to us | About 4n + 4 quantum queries (encryption and decryption) | Q2 model, one tweak; forgery for a rest of 2 hash blocks or more | As above |
| Quantum cryptanalysis, superposition queries | Key recovery and universal forgery for HCTR2-TwKD, one tweak | Security 2n/3 bits with at most 2^{n/3} block cipher calls per tweak [2] | About n + 2 quantum queries under that tweak | Q2 model | As above |
| Quantum cryptanalysis, superposition queries | Key recovery and universal forgery for HCTR2 | Birthday bound n/2 bits [1] | About n + 2 quantum queries | Q2 model | As above |

All security claims of [1, 2, 3] are for classical attackers, and the attacks here do not contradict them. They show that these bounds do not extend to superposition queries. In the Q1 model (classical queries, quantum computation), which is the one the NIST requirements [4, Section 2.2.5] ask for, nothing here applies; Simon's algorithm in that model is studied in [13]. To our knowledge, the quantum security of HCTR2 has not been considered before; [11] notes this.

**Prior work.** Simon's algorithm in the Q2 model goes back to Kuwakado and Morii [9] and to [5]. For hash-encrypt-hash schemes, Rahman and Paul [6] attacked HCTR, HCH and Tweakable HCTR, Ghosh and Sarkar [7] CMC, EME, XCB, TET and FAST, and Mao, Wang and Hu [8] HCTR, HCH, PEP and HEH. The attacks on HCTR2 and on HCTR2-TwKD, which is HCTR2 for a fixed T₀, are direct transfers of [6]. To our knowledge, no attack in the Q2 model has been given for HCTR2, CHCTR, HCTR2-TwKD or HCTR++. What is new here is the subgroup for the cascade, in the kernel of λ₁ ⊕ λ₂, the subgroup for HCTR++ through its fresh rekeying, the key recovery from one element of the subgroup, and the uniqueness bounds in the ideal cipher model, which give the query bounds without a heuristic assumption on the scheme.

## 1. Setup

Blocks are elements of K = GF(2ⁿ), n = 128. For a fixed tweak T and a message N of l full blocks, the POLYVAL hash is H(T, N) = c_T ⊕ λ(N), with λ(N) = Σᵢ Nᵢ w^{l−i+1} and w = h·x^{−n}, where h is the hash key [1, Section 3]. So λ is linear over GF(2) and c_T depends on T and l only.

HCTR2 encrypts P = M ‖ N as MM = M ⊕ H(T, N), UU = E(MM), S = MM ⊕ UU ⊕ L, V = N ⊕ XCTR(S), U = UU ⊕ H(T, V), with h = E(0), L = E(1) and XCTR(S) = E(S ⊕ 1) ‖ E(S ⊕ 2) ‖ … [1]. CHCTR is HCTR2 under K₂ applied to HCTR2 under K₁, with the same tweak [2]. HCTR2-TwKD is HCTR2 under a key derived from one part T₀ of the tweak, with the other part as the inner tweak [2, Section 3.4]. HCTR++ [3, Figure 4] hashes the rest R of the message with a 2n-bit hash under h1, uses one half of the hash to mask the first block and the other half to select a fresh AES key for it, derives a keystream from the result, again with fresh keys for every block, and hashes the encrypted rest with h2. This follows the revision of [3] of 9 March 2026, as distributed with the reference code [14]. The first version of the design did not decrypt correctly [10]; the revision used here does, and decryption is the same map with h1 and h2 exchanged. Later revisions of [3] are not considered. For the 2n-bit hash, the reference code uses POLYVAL over GF(2^{2n}) with field polynomial x²⁵⁶ + x²⁵⁴ + x²⁵¹ + x²⁴⁶ + 1 and the encoding of HCTR2, and the attack uses the same. In the ideal cipher model, the key derived by HCTR2-TwKD gives a uniform permutation independent of the master cipher unless it equals the master key, which has negligible probability.

In the Q2 model the attacker has the unitary |x⟩|z⟩ ↦ |x⟩|z ⊕ Enc(T, x)⟩ for a classical T. CNOT gates from x into the output then give g(x) = Enc(T, x) ⊕ x. To keep only the rest of g, the output qubits of the first block start in |+⟩ⁿ, which the XOR leaves unchanged.

## 2. Shift identities

**Lemma 1 (HCTR2).** For all M, N, δ of l blocks: Enc(M ⊕ λ(δ), N ⊕ δ) = Enc(M, N) ⊕ (λ(δ), δ), and the same for decryption.

*Proof.* MM is unchanged, so UU, S and the keystream are. Then V changes by δ, and U = UU ⊕ H(T, V) by λ(δ). ∎

**Lemma 2 (CHCTR).** Let S_C = {(λ₁(δ), δ) : λ₁(δ) = λ₂(δ)}. Then Enc(x ⊕ s) = Enc(x) ⊕ s for s ∈ S_C. For l = 2 and w₁ ≠ w₂,
S_C = {(d·w₁w₂, d, d·(w₁ ⊕ w₂)) : d ∈ K}, of dimension n.

*Proof.* Lemma 1 for the first layer gives the output shift (λ₁(δ), δ) = (λ₂(δ), δ), and Lemma 1 for the second layer turns it into the same shift. For l = 2, λᵢ(δ) = δ₁wᵢ² ⊕ δ₂wᵢ, and in characteristic 2, λ₁(δ) ⊕ λ₂(δ) = (w₁ ⊕ w₂)(δ₁(w₁ ⊕ w₂) ⊕ δ₂). So δ₂ = δ₁(w₁ ⊕ w₂), and then λ₁(δ) = δ₁w₁² ⊕ δ₁(w₁ ⊕ w₂)w₁ = δ₁w₁w₂. ∎

**Lemma 3 (HCTR++).** Write a 2n-bit value as (first half, second half), and let Λᵢ be the linear part of the hash under hᵢ.
(a) For S_P = {((Λ₁δ)₀, δ) : Λ₁δ = Λ₂δ, (Λ₁δ)₁ = 0}: Enc(x ⊕ s) = Enc(x) ⊕ s. For a rest of two hash blocks, S_P = {(a, d, d·(w₁ ⊕ w₂)) : d·w₁w₂ = (a, 0)}, of dimension n.
(b) For S₁ = {((Λ₁δ)₀, δ) : (Λ₁δ)₁ = 0}, the rest of Enc(x) ⊕ x is S₁-invariant. For a rest of one hash block, S₁ = {(a, d) : d·w₁ = (a, 0)}. Decryption is the same map with h1 and h2 exchanged.

*Proof.* The masked first block and the half that selects the key are unchanged, so the rekeyed block and the keystream are. The rest of the output changes by δ. In (a) the second hash changes by Λ₂δ = (a, 0), so the half that selects the inverse key is unchanged and the first output block changes by a. ∎

So in every case g(x) = Enc(x) ⊕ x (in (b) its rest) is invariant under a subgroup S, and S determines the keys.

## 3. Simon's algorithm with a known dimension

One Simon sample y of f on GF(2)^D has Pr[y ∈ Y] = |Y^⊥|^{−1} Σ_{t ∈ Y^⊥} p(t) for every subspace Y, where p(t) = Pr_x[f(x ⊕ t) = f(x)].

**Lemma 4.** If f is S-invariant, every sample lies in S^⊥. Let ε = max_{t ∉ S} p(t) and d = dim S^⊥. For a subspace Y ⊂ S^⊥ of dimension j < d, Pr[y ∈ Y] ≤ 2^{j−d} + ε.

**Theorem 5.** Sample until the samples span a space of dimension d, and output its orthogonal complement. The output is exactly S. If ε ≤ 1/8, the expected number of samples is at most Σ_{i=1}^{d} 1/(1 − 2^{−i} − ε) ≤ d + 1.61 + 6dε. Sharper bounds for random functions are in [12]; the bound here needs only ε of the given function.

The dimension d is known in advance from Lemmas 1 to 3, so the algorithm never outputs a wrong subgroup. For HCTR2, D = 2n and d = n. For CHCTR and HCTR++ (b), D = 3n and d = 2n.

## 4. Uniqueness in the ideal cipher model

For a permutation π of {0,1}ⁿ let Δ(π) = max_{a≠0, b} #{y : π(y) ⊕ π(y ⊕ a) = b}, and Φ(π) = max_v #{y : y ⊕ π(y) = v}.

**Lemma 6.** For a uniform permutation and 1 ≤ m ≤ 2^{n−2}: Pr[Δ ≥ 2m] ≤ 2^{2n}/m! and Pr[Φ ≥ m] ≤ 2^{n+m}/m!. For two independent ones, the number of q with π(q) ⊕ π′(q ⊕ k) = μ is at least m for some (k, μ) with probability at most 2^{2n+m}/m!.

*Proof.* Solutions of π(y) ⊕ π(y ⊕ a) = b come in pairs {y, y ⊕ a}. For m fixed disjoint pairs, revealing π pair by pair forces the second value of each, with probability at most 2^{−(n−1)} each, and there are at most (2^{n−1})^m/m! sets of pairs. The other two bounds are the same count with single points. ∎

**Proposition 7 (HCTR2).** ε ≤ Δ(E)/2ⁿ, so ε < 2n/2ⁿ except with probability 2^{2n}/n! < 2^{−460}.

*Proof.* With y = MM, g = Enc ⊕ id equals (S ⊕ L ⊕ λ(XCTR(S)), XCTR(S)), a function of S = y ⊕ E(y) ⊕ L that is injective in S. A shift t = (a, δ) ∉ S changes y by u = a ⊕ λ(δ) ≠ 0, and p(t) = #{y : E(y) ⊕ E(y ⊕ u) = u}/2ⁿ. ∎

**Proposition 8 (CHCTR).** For w₁ ≠ w₂: ε ≤ (Δ(E₁) + Φ(E₂)Δ(E₂))/2ⁿ, so ε < (2n + 2n²)/2ⁿ < 2^{−112} except with probability below 2^{−127}, which includes w₁ = w₂.

*Proof.* The quotient coordinates are y = MM₁ and z = λ₁(N) ⊕ λ₂(N), onto K² since w₁ ≠ w₂. With X₁ the first keystream, m = E₁(y) ⊕ z ⊕ (λ₁ ⊕ λ₂)(X₁) ⊕ c the middle value of the second layer and A = X₁ ⊕ X₂(S₂(m)), one has g = (E₂(m) ⊕ y ⊕ z ⊕ λ₂(A) ⊕ c′, A). Let the shift be (u, w) ≠ 0. If u = 0, a collision needs S₂(m) = S₂(m ⊕ w), and m is uniform as z varies: at most Δ(E₂)/2ⁿ. If u ≠ 0 and S₁(y) = S₁(y ⊕ u), then E₁(y) ⊕ E₁(y ⊕ u) = u: at most Δ(E₁)/2ⁿ. Otherwise the first keystream blocks of layer 1 differ by some Δ₁ ≠ 0. For fixed y, m′ = m ⊕ κ_y, and the second output part forces S₂(m) ⊕ S₂(m′) = γ for a γ fixed by y, with γ ≠ 0. Then σ = S₂(m) ⊕ 1 solves E₂(σ) ⊕ E₂(σ ⊕ γ) = Δ₁, which has at most Δ(E₂) solutions, each coming from at most Φ(E₂) values of m. ∎

**Proposition 9 (HCTR++).** In the ideal cipher model, with the master key K one of the keys of the family, for the one-block rest on encryption (and on decryption), ε ≤ 2^{1−n/2} except with probability below 2^{−57}.

*Proof sketch.* The quotient coordinates are the masked first block and the half that selects the key, and g is the keystream of the rekeyed block cc. A collision either has the same cc, which is a differential of one rekeyed AES or a cross differential of two, bounded through Lemma 6 with m = 2n, or two different values of cc with the same keystream. The number Γ of values of cc involved in such keystream collisions has expectation below 4. Two different cc give equations at four points of the ideal cipher, which are distinct except for one structured family of at most 2^κ partners per cc, with E[2^κ] ≤ 2. Four distinct points give probability at most 1/((2ⁿ − 7)(2ⁿ − 9)), since six values E_K(1), …, E_K(6) are fixed by the subkeys, Values of cc with a point of key K and such an input are counted in Γ; for fixed (r, j) such a point is a degree-2 equation in the derived key, so their expected number is O(2^{−n}). Markov's inequality gives Γ < 2^{n/2} except with probability 2^{2−n/2}, and the remaining terms 2^{2−2n} and 2^{−900} come from the rare keys and the same-cc case. ∎

With these bounds, Theorem 5 gives the counts of Theorem 1, up to an additive term below 2^{−50}.

## 5. The attacks

1. Prepare the oracle for g with one fixed tweak and messages of the stated length, and run Theorem 5. This gives S.
2. HCTR2 and TwKD: w = a/δ for any (a, δ) ∈ S with δ ≠ 0, and h = w·xⁿ. CHCTR: from (a, d₁, d₂) ∈ S with d₁ ≠ 0, s = d₂/d₁ = w₁ ⊕ w₂ and p = a/d₁ = w₁w₂, so {w₁, w₂} are the roots of X² ⊕ sX ⊕ p. HCTR++: w₁ = (a, 0)/d from encryption, w₂ from decryption.
3. Forgery: for a target P and s ∈ S \ {0}, Enc(P) = Enc(P ⊕ s) ⊕ s (Theorem 2). For HCTR++ S_P is computed from w₁ and w₂.

The post-processing is Gaussian elimination on D ≤ 3n bits and a few field operations.

## 6. Measurements

[`sim/toy.py`](sim/toy.py), log in [`sim/toy.log`](sim/toy.log), uses n-bit blocks with random permutations as the block ciphers and POLYVAL as Horner evaluation in GF(2ⁿ) (GF(2^{2n}) for HCTR++). For HCTR++ the rekeyed ciphers form a family with the master cipher as one member, as in the ideal cipher model. It checks the shift identities everywhere, computes ε exhaustively over the cosets of S, forms the exact distribution of one Simon sample, and runs the procedure of Theorem 5 300 times on that distribution. Ranges are minimum to maximum. The bound is the sum of Theorem 5, finite for ε < 1/2. For the recovery step the toy keys exclude h = 0 for HCTR2 and hᵢ = 0 or h₁ = h₂ for CHCTR.

| Scheme | n | D | dim S | ε | Mean samples | Bound of Theorem 5 | S and keys recovered |
|---|---|---|---|---|---|---|---|
| HCTR2 | 3 to 8 | 2n | n | 0.023 to 0.250, equal to Δ(E)/2ⁿ each time | 4.90 to 9.81 | 6.83 to 9.90 | all |
| CHCTR | 3 to 6 | 3n | n | 0.094 to 0.500 | 9.36 to 13.67 | none at n = 3 (ε = 1/2), then 13.77 to 21.00 | all |
| HCTR++, 2 blocks | 3 | 5n | n | 0.438 | 14.05 | 37.91 | all |
| HCTR++, 1 block, enc and dec | 3 to 5 | 3n | n | 0.061 to 0.313 | 8.75 to 12.08 | 11.81 to 14.01 | all |

[`sim/fullsize.py`](sim/fullsize.py), log in [`sim/fullsize.log`](sim/fullsize.log), implements HCTR2, CHCTR and HCTR++ with AES and the real POLYVAL. The HCTR2 implementation reproduces all 350 AES-256 test vectors of the reference repository of [1] (run with the path to `HCTR2_AES256.json`). For random keys, tweaks and inputs it checks Enc(x ⊕ s) = Enc(x) ⊕ s and Dec(y ⊕ s) = Dec(y) ⊕ s at n = 128, the invariance of Lemma 3 (b) on encryption and decryption, the key recovery from one element of S for all three schemes, and Theorem 2 for HCTR2 with partial last blocks and for CHCTR and HCTR++ with rests of up to four blocks and three hash blocks.

[`sim/qiskit_check.py`](sim/qiskit_check.py), log in [`sim/qiskit_check.log`](sim/qiskit_check.log), runs Simon's circuit gate by gate in the noiseless statevector simulator of Qiskit Aer, with the encryption oracle (the decryption oracle for the decryption run of HCTR++) built from its truth table, the CNOT gates and the |+⟩ trick of Section 1, at n = 3 with 12 to 18 qubits. Every measured y is orthogonal to S, and S and the keys are recovered.

## 7. Limits

- The attacks need superposition access to the keyed encryption (Q2). Disk and filename encryption, the main uses of HCTR2, do not give such access in practice.
- The query bounds assume the ideal cipher model for AES, as the classical proofs of [3] do, while [2] assumes a multi-user strong pseudorandom permutation. The algorithm itself never outputs a wrong subgroup, so a weaker uniqueness bound would only increase the number of queries.
- [2] defines CHCTR and HCTR2-TwKD for an abstract polynomial hash; the attacks use POLYVAL as in HCTR2. The definition of HCTR++ follows [3, Figure 4] in its revision of 9 March 2026 and the reference code [14], which fixes the 2n-bit hash as POLYVAL over GF(2^{2n}). The attack on HCTR++ needs the hash to be linear over GF(2) in the message for a fixed tweak and length, and the key recovery needs it to be polynomial.
- Keys with w₁ = w₂ for CHCTR, or w₁ = 0 or w₂ = 0 for HCTR++, are excluded; these events have probability at most about 2^{−n}. HCTR2 needs no condition on h.

## 8. Formal verification

[`lean/`](lean/) is a Lean 4 library `SimonHCTR` on Mathlib, with 38 main theorems, no `sorry`, and only the standard axioms (propext, Classical.choice, Quot.sound), listed by `lean/SimonHCTR/Axioms.lean`. Build with `lake build` in `lean/`.

| Part | Theorems |
|---|---|
| Lemma 1 (HCTR2), over any commutative ring of characteristic 2, with arbitrary E, L, keystream and additive hash | `HCTR2Key.enc_shift`, `dec_shift`, `dec_enc`, `enc_dec` |
| Lemma 2 (CHCTR) | `chctrEnc_shift`, `chctrDec_shift` |
| Lemma 3 (HCTR++), (a) and (b), decryption as encryption with the hash keys exchanged | `HCTRppKey.enc_shift`, `enc_rest_shift`, `dec_enc`, `dec_shift`, `dec_rest_shift` |
| Subgroups and key recovery, over a field of characteristic 2 | `recover_one`, `recover_one'`, `lamPoly_two_eq_iff`, `lamPoly_two_of`, `quadratic_roots`, `recover_two`, `recover_two_roots`, `quotMap_eq_zero_iff`, `quotMap_surjective` |
| Proposition 7, deterministic part | `HCTR2Key.g_eq`, `Gfun_injective`, `g_collision_iff` |
| Proposition 8, deterministic part (the three cases) | `chctr_g_eq`, `chctr_collision_cases` |
| Proposition 9, the split of a collision into equal and different cc | `HCTRppKey.enc_rest_add`, `collision_cases` |
| Simon sampling, Lemma 4 | `Simon.simonProb_eq`, `sum_simonProb`, `card_mul_card_perp`, `simonProb_eq_zero`, `sum_simonProb_le`, `sum_simonProb_le'` |
| Theorem 5, the sum | `lasVegas_sum_le`, `lasVegas_sum_le_two` |
| Lemma 6, the numbers at n = 128 | `Tail.tail_delta`, `tail_cross`, `tail_hctrpp` |

`sum_simonProb` is the identity Pr[y ∈ Y] = |Y^⊥|^{−1} Σ_{t ∈ Y^⊥} p(t) for the exact output distribution of one Simon sample, written as real sums over GF(2)^D, and `sum_simonProb_le` holds for every subspace Y.

**Not formalized.** The quantum circuit and its output distribution as a physical process (the distribution is taken as the formula of `simonProb_eq`), the expected number of samples as a stopping time, the probability bounds of Lemma 6 and of Propositions 7 to 9 over random permutations, AES and POLYVAL themselves (the hash enters as an additive map, or as a polynomial for key recovery), and the length and tweak encodings.

## References

1. P. Crowley, N. Huckleberry, E. Biggers. Length-preserving encryption with HCTR2. Cryptology ePrint Archive 2021/1441.
2. Y. L. Chen, Y. Hiraga, N. Mouha, Y. Naito, Y. Sasaki, T. Sugawara. Beyond-Birthday-Bound Security with HCTR2: Cascaded Construction and Tweak-based Key Derivation. ASIACRYPT 2025, Cryptology ePrint Archive 2026/085.
3. G. Öztürk, O. Koçak, O. Yayla. HCTR++: A Beyond Birthday Bound Secure HCTR2 Variant. Cryptology ePrint Archive 2026/383.
4. Y. L. Chen, M. Davidson, M. Dworkin et al. Requirements for cryptographic accordions. NIST IR 8552, 2025.
5. M. Kaplan, G. Leurent, A. Leverrier, M. Naya-Plasencia. Breaking symmetric cryptosystems using quantum period finding. CRYPTO 2016.
6. M. Rahman, G. Paul. Quantum attacks on HCTR and its variants. IEEE Transactions on Quantum Engineering 1, 2020. Cryptology ePrint Archive 2020/802.
7. S. Ghosh, P. Sarkar. Breaking tweakable enciphering schemes using Simon's algorithm. Designs, Codes and Cryptography 89, 2021.
8. S. Mao, P. Wang, L. Hu. Research on tweakable enciphering schemes under Simon's quantum algorithm attack. Journal of Cyber Security 9(2), 2024.
9. H. Kuwakado, M. Morii. Quantum distinguisher between the 3-round Feistel cipher and the random permutation. ISIT 2010.
10. M. Khairallah. A note on HCTR++. Cryptology ePrint Archive 2026/591.
11. D. Chang, Y. Hiraga, K. Minematsu, N. Mouha, Y. Naito, Y. Sasaki, T. Shiba, T. Sugawara. Extended analysis of key committing security of HCTR2. SAC 2026.
12. X. Bonnetain. Tight bounds for Simon's algorithm. LATINCRYPT 2021.
13. X. Bonnetain, A. Hosoyamada, M. Naya-Plasencia, Y. Sasaki, A. Schrottenloher. Quantum attacks without superposition queries: the offline Simon's algorithm. ASIACRYPT 2019.
14. G. Öztürk. HCTR++ reference implementation. https://github.com/gulnihalozturk/hctrpp, 2026.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
