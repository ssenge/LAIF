import Mathlib

/-!
# Shift identities for HCTR2, CHCTR and HCTR++

Blocks live in a commutative ring `K` of characteristic two (in the application
`K = GF(2^n)`), so that `a + a = 0` and addition is exclusive or. A message of
`l` full blocks is a function `Fin l → K`.

* HCTR2 is modelled with an arbitrary block function `E`, a mask `L`, an arbitrary
  keystream `X : K → (Fin l → K)` (the XCTR keystream as a function of `S`) and an
  affine hash `H N = c + lam N` with `lam` additive.
* CHCTR is HCTR2 under a second independent key applied to the output of HCTR2
  under a first key.
* HCTR++ is modelled with hash values in `K × K` (first half, second half), a
  rekeyed block function `F r p`, its inverse `G`, and an arbitrary keystream
  function `KS` of the middle value `cc`.

The main statements are `HCTR2Key.enc_shift`, `HCTR2Key.dec_shift`,
`chctrEnc_shift`, `chctrDec_shift`, `HCTRppKey.enc_shift` and
`HCTRppKey.enc_rest_shift` (Lemmas 1, 2, 3 of the notes).
-/

namespace SimonHCTR

section CharTwo

variable {K : Type*} [CommRing K] [CharP K 2]

theorem add_add_cancel_right (a b : K) : a + b + b = a := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem add_add_cancel_left' (a b : K) : a + (a + b) = b := by
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- In characteristic two every vector of blocks is its own negative. -/
theorem vec_add_self {ι : Type*} (v : ι → K) : v + v = 0 := by
  funext i; simp [CharTwo.add_self_eq_zero]

/-- In characteristic two every vector of double blocks is its own negative. -/
theorem vec2_add_self {ι : Type*} (v : ι → K × K) : v + v = 0 := by
  funext i; ext <;> simp [CharTwo.add_self_eq_zero]

theorem four_eq_zero : (4 : K) = 0 := by
  have : (4 : K) = 2 * 2 := by norm_num
  rw [this, CharTwo.two_eq_zero, mul_zero]

theorem six_eq_zero : (6 : K) = 0 := by
  have : (6 : K) = 2 * 3 := by norm_num
  rw [this, CharTwo.two_eq_zero, zero_mul]

theorem eight_eq_zero : (8 : K) = 0 := by
  have : (8 : K) = 2 * 4 := by norm_num
  rw [this, CharTwo.two_eq_zero, zero_mul]

end CharTwo

/-- Normalization modulo two: ring normal form, then even numerals are zero. -/
macro "char2_norm" : tactic => `(tactic| (ring_nf; try simp only [CharTwo.two_eq_zero, four_eq_zero, six_eq_zero, eight_eq_zero, mul_zero, zero_mul, neg_zero, sub_zero, zero_sub, add_zero, zero_add, sub_self]))

/-- `char2_lc e` proves an equation in a commutative ring of characteristic two that
follows from the linear combination `e` of hypotheses, up to even multiples. -/
macro "char2_lc" e:(ppSpace colGt term)? : tactic =>
  match e with
  | some e => `(tactic| (linear_combination (norm := char2_norm) $e:term))
  | none => `(tactic| (linear_combination (norm := char2_norm)))

/-! ## HCTR2 -/

/-- The data of one HCTR2 instance for a fixed tweak and messages of `1 + l` blocks:
block function `E` with inverse `Einv`, mask `L`, keystream `X` (XCTR as a function
of the value `S`), and the hash `H N = c + lam N` with additive part `lam`. -/
structure HCTR2Key (K : Type*) [CommRing K] (l : ℕ) where
  E : K → K
  Einv : K → K
  L : K
  X : K → (Fin l → K)
  c : K
  lam : (Fin l → K) →+ K

namespace HCTR2Key

variable {K : Type*} [CommRing K] [CharP K 2] {l : ℕ} (k : HCTR2Key K l)

/-- The hash `H(T, N) = c + lam N` for the fixed tweak `T`. -/
def H (N : Fin l → K) : K := k.c + k.lam N

/-- The middle value `S = MM + E MM + L`. -/
def Sval (MM : K) : K := MM + k.E MM + k.L

/-- HCTR2 encryption of `(M, N)`: `MM = M + H N`, `UU = E MM`, `S = MM + UU + L`,
`V = N + X S`, `U = UU + H V`; the output is `(U, V)`. -/
def enc (M : K) (N : Fin l → K) : K × (Fin l → K) :=
  let MM := M + k.H N
  let UU := k.E MM
  let S := MM + UU + k.L
  let V := N + k.X S
  (UU + k.H V, V)

/-- HCTR2 decryption of `(U, V)`: `UU = U + H V`, `MM = Einv UU`, `S = MM + UU + L`,
`N = V + X S`, `M = MM + H N`; the output is `(M, N)`. -/
def dec (U : K) (V : Fin l → K) : K × (Fin l → K) :=
  let UU := U + k.H V
  let MM := k.Einv UU
  let S := MM + UU + k.L
  let N := V + k.X S
  (MM + k.H N, N)

omit [CharP K 2] in
theorem H_add (N δ : Fin l → K) : k.H (N + δ) = k.H N + k.lam δ := by
  simp [H, map_add, add_assoc]

/-- Lemma 1 (HCTR2, encryption): `Enc(M + lam δ, N + δ) = Enc(M, N) + (lam δ, δ)`. -/
theorem enc_shift (M : K) (N δ : Fin l → K) :
    k.enc (M + k.lam δ) (N + δ) = k.enc M N + (k.lam δ, δ) := by
  have hMM : M + k.lam δ + k.H (N + δ) = M + k.H N := by
    rw [H_add]
    calc M + k.lam δ + (k.H N + k.lam δ) = M + k.H N + k.lam δ + k.lam δ := by abel
      _ = M + k.H N := add_add_cancel_right _ _
  simp only [enc, hMM]
  ext
  · simp only [Prod.fst_add]
    rw [add_right_comm N δ, H_add]; abel
  · simp only [Prod.snd_add]
    exact add_right_comm _ _ _

/-- Lemma 1 (HCTR2, decryption): `Dec(U + lam δ, V + δ) = Dec(U, V) + (lam δ, δ)`. -/
theorem dec_shift (U : K) (V δ : Fin l → K) :
    k.dec (U + k.lam δ) (V + δ) = k.dec U V + (k.lam δ, δ) := by
  have hUU : U + k.lam δ + k.H (V + δ) = U + k.H V := by
    rw [H_add]
    calc U + k.lam δ + (k.H V + k.lam δ) = U + k.H V + k.lam δ + k.lam δ := by abel
      _ = U + k.H V := add_add_cancel_right _ _
  simp only [dec, hUU]
  ext
  · simp only [Prod.fst_add]
    rw [add_right_comm V δ, H_add]; abel
  · simp only [Prod.snd_add]
    exact add_right_comm _ _ _

/-- Decryption inverts encryption when `Einv` is a left inverse of `E`. -/
theorem dec_enc (hE : ∀ m, k.Einv (k.E m) = m) (M : K) (N : Fin l → K) :
    k.dec (k.enc M N).1 (k.enc M N).2 = (M, N) := by
  simp only [enc, dec]
  set MM := M + k.H N
  have h1 : k.E MM + k.H (N + k.X (MM + k.E MM + k.L)) + k.H (N + k.X (MM + k.E MM + k.L))
      = k.E MM := add_add_cancel_right _ _
  rw [h1, hE]
  have h2 : N + k.X (MM + k.E MM + k.L) + k.X (MM + k.E MM + k.L) = N := by
    rw [add_assoc, vec_add_self, add_zero]
  rw [h2]
  simp [MM, add_add_cancel_right]

/-- Encryption inverts decryption when `Einv` is a right inverse of `E`. -/
theorem enc_dec (hE : ∀ u, k.E (k.Einv u) = u) (U : K) (V : Fin l → K) :
    k.enc (k.dec U V).1 (k.dec U V).2 = (U, V) := by
  simp only [enc, dec]
  set UU := U + k.H V
  have h1 : k.Einv UU + k.H (V + k.X (k.Einv UU + UU + k.L)) + k.H (V + k.X (k.Einv UU + UU + k.L))
      = k.Einv UU := add_add_cancel_right _ _
  rw [h1, hE]
  have h2 : V + k.X (k.Einv UU + UU + k.L) + k.X (k.Einv UU + UU + k.L) = V := by
    rw [add_assoc, vec_add_self, add_zero]
  rw [h2]
  simp [UU, add_add_cancel_right]

end HCTR2Key

/-! ## CHCTR -/

section CHCTR

variable {K : Type*} [CommRing K] [CharP K 2] {l : ℕ}

/-- CHCTR encryption: HCTR2 under the key `k2` applied to HCTR2 under the key `k1`,
with the same tweak in both layers. -/
def chctrEnc (k1 k2 : HCTR2Key K l) (M : K) (N : Fin l → K) : K × (Fin l → K) :=
  k2.enc (k1.enc M N).1 (k1.enc M N).2

/-- CHCTR decryption: HCTR2 decryption under `k1` applied to HCTR2 decryption under `k2`. -/
def chctrDec (k1 k2 : HCTR2Key K l) (U : K) (V : Fin l → K) : K × (Fin l → K) :=
  k1.dec (k2.dec U V).1 (k2.dec U V).2

/-- Lemma 2 (CHCTR, encryption): for `δ` with `lam₁ δ = lam₂ δ`,
`Enc(M + lam₁ δ, N + δ) = Enc(M, N) + (lam₁ δ, δ)`. -/
theorem chctrEnc_shift (k1 k2 : HCTR2Key K l) (M : K) (N δ : Fin l → K)
    (h : k1.lam δ = k2.lam δ) :
    chctrEnc k1 k2 (M + k1.lam δ) (N + δ) = chctrEnc k1 k2 M N + (k1.lam δ, δ) := by
  unfold chctrEnc
  rw [k1.enc_shift, Prod.fst_add, Prod.snd_add, h, k2.enc_shift]

/-- Lemma 2 (CHCTR, decryption): for `δ` with `lam₁ δ = lam₂ δ`,
`Dec(U + lam₁ δ, V + δ) = Dec(U, V) + (lam₁ δ, δ)`. -/
theorem chctrDec_shift (k1 k2 : HCTR2Key K l) (U : K) (V δ : Fin l → K)
    (h : k1.lam δ = k2.lam δ) :
    chctrDec k1 k2 (U + k1.lam δ) (V + δ) = chctrDec k1 k2 U V + (k1.lam δ, δ) := by
  unfold chctrDec
  rw [h, k2.dec_shift, Prod.fst_add, Prod.snd_add, ← h, k1.dec_shift]

end CHCTR

/-! ## HCTR++ -/

/-- The data of one HCTR++ instance for a fixed tweak and messages of one block of `K`
followed by `l` double blocks of `K × K`: hash constants `c1, c2` and additive parts
`Λ1, Λ2` of the two `2n`-bit hashes, the rekeyed block function `F r p`, its inverse
`G r` and the keystream `KS cc` (which stands for the hash of `cc` followed by the
rekeyed counter blocks). A value of `K × K` is (first half, second half). -/
structure HCTRppKey (K : Type*) [CommRing K] (l : ℕ) where
  c1 : K × K
  c2 : K × K
  Λ1 : (Fin l → K × K) →+ K × K
  Λ2 : (Fin l → K × K) →+ K × K
  F : K → K → K
  G : K → K → K
  KS : K → (Fin l → K × K)

namespace HCTRppKey

variable {K : Type*} [CommRing K] [CharP K 2] {l : ℕ} (k : HCTRppKey K l)

/-- HCTR++ encryption of `(b1, R)`: `x1 = c1 + Λ1 R`, `pp1 = b1 + x1.1`, `re = x1.2`,
`cc = F re pp1`, `out = R + KS cc`, `x2 = c2 + Λ2 out`, `out1 = G x2.2 cc + x2.1`;
the output is `(out1, out)`. -/
def enc (b1 : K) (R : Fin l → K × K) : K × (Fin l → K × K) :=
  let x1 := k.c1 + k.Λ1 R
  let pp1 := b1 + x1.1
  let re := x1.2
  let cc := k.F re pp1
  let out := R + k.KS cc
  let x2 := k.c2 + k.Λ2 out
  (k.G x2.2 cc + x2.1, out)

/-- The instance with the two hashes exchanged. HCTR++ decryption is encryption of
the exchanged instance (`dec_enc` below), so every statement about encryption gives
the corresponding statement about decryption with `Λ1` and `Λ2` exchanged. -/
def swap : HCTRppKey K l :=
  { k with c1 := k.c2, c2 := k.c1, Λ1 := k.Λ2, Λ2 := k.Λ1 }

/-- HCTR++ decryption: the encryption map of the instance with `h1` and `h2` exchanged. -/
def dec (out1 : K) (out : Fin l → K × K) : K × (Fin l → K × K) := k.swap.enc out1 out

/-- Decryption inverts encryption when `G r` is a left inverse and a right inverse of
`F r`. -/
theorem dec_enc (hGF : ∀ r p, k.G r (k.F r p) = p) (hFG : ∀ r q, k.F r (k.G r q) = q)
    (b1 : K) (R : Fin l → K × K) :
    k.dec (k.enc b1 R).1 (k.enc b1 R).2 = (b1, R) := by
  simp only [dec, swap, enc]
  set cc := k.F (k.c1 + k.Λ1 R).2 (b1 + (k.c1 + k.Λ1 R).1)
  have h1 : k.G (k.c2 + k.Λ2 (R + k.KS cc)).2 cc + (k.c2 + k.Λ2 (R + k.KS cc)).1
      + (k.c2 + k.Λ2 (R + k.KS cc)).1 = k.G (k.c2 + k.Λ2 (R + k.KS cc)).2 cc :=
    add_add_cancel_right _ _
  rw [h1, hFG]
  have h2 : R + k.KS cc + k.KS cc = R := by rw [add_assoc, vec2_add_self, add_zero]
  rw [h2, hGF, add_add_cancel_right]

/-- Lemma 3 (a) (HCTR++): if `Λ1 δ = Λ2 δ` and the second half of `Λ1 δ` is zero,
then `Enc(b1 + (Λ1 δ).1, R + δ) = Enc(b1, R) + ((Λ1 δ).1, δ)`.
By `dec_enc`, decryption is `enc` of `swap`, so the same statement with `Λ1` and
`Λ2` exchanged holds for decryption (see `dec_shift`). -/
theorem enc_shift (b1 : K) (R δ : Fin l → K × K)
    (h : k.Λ1 δ = k.Λ2 δ) (h2 : (k.Λ1 δ).2 = 0) :
    k.enc (b1 + (k.Λ1 δ).1) (R + δ) = k.enc b1 R + ((k.Λ1 δ).1, δ) := by
  simp only [enc]
  have hpp : b1 + (k.Λ1 δ).1 + (k.c1 + k.Λ1 (R + δ)).1 = b1 + (k.c1 + k.Λ1 R).1 := by
    rw [map_add, Prod.fst_add, Prod.fst_add, Prod.fst_add]
    calc b1 + (k.Λ1 δ).1 + ((k.c1).1 + ((k.Λ1 R).1 + (k.Λ1 δ).1))
        = b1 + ((k.c1).1 + (k.Λ1 R).1) + (k.Λ1 δ).1 + (k.Λ1 δ).1 := by abel
      _ = _ := add_add_cancel_right _ _
  have hre : (k.c1 + k.Λ1 (R + δ)).2 = (k.c1 + k.Λ1 R).2 := by
    rw [map_add, Prod.snd_add, Prod.snd_add, h2, add_zero, Prod.snd_add]
  rw [hpp, hre]
  set cc := k.F (k.c1 + k.Λ1 R).2 (b1 + (k.c1 + k.Λ1 R).1)
  have hout : R + δ + k.KS cc = R + k.KS cc + δ := add_right_comm _ _ _
  rw [hout]
  have h2' : (k.Λ2 δ).2 = 0 := h ▸ h2
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, map_add, Prod.snd_add, h2', add_zero]
    rw [h]; abel
  · simp

/-- Lemma 3 (b) (HCTR++): if the second half of `Λ1 δ` is zero, the rest of the
ciphertext satisfies `(Enc(b1 + (Λ1 δ).1, R + δ)).2 = (Enc(b1, R)).2 + δ`. -/
theorem enc_rest_shift (b1 : K) (R δ : Fin l → K × K) (h2 : (k.Λ1 δ).2 = 0) :
    (k.enc (b1 + (k.Λ1 δ).1) (R + δ)).2 = (k.enc b1 R).2 + δ := by
  simp only [enc]
  have hpp : b1 + (k.Λ1 δ).1 + (k.c1 + k.Λ1 (R + δ)).1 = b1 + (k.c1 + k.Λ1 R).1 := by
    rw [map_add, Prod.fst_add, Prod.fst_add, Prod.fst_add]
    calc b1 + (k.Λ1 δ).1 + ((k.c1).1 + ((k.Λ1 R).1 + (k.Λ1 δ).1))
        = b1 + ((k.c1).1 + (k.Λ1 R).1) + (k.Λ1 δ).1 + (k.Λ1 δ).1 := by abel
      _ = _ := add_add_cancel_right _ _
  have hre : (k.c1 + k.Λ1 (R + δ)).2 = (k.c1 + k.Λ1 R).2 := by
    rw [map_add, Prod.snd_add, Prod.snd_add, h2, add_zero, Prod.snd_add]
  rw [hpp, hre]
  exact add_right_comm _ _ _

/-- Lemma 3 (a) for HCTR++ decryption: if `Λ1 δ = Λ2 δ` and the second half of `Λ2 δ`
is zero, then `Dec(b + (Λ2 δ).1, R + δ) = Dec(b, R) + ((Λ2 δ).1, δ)`. -/
theorem dec_shift (b : K) (R δ : Fin l → K × K)
    (h : k.Λ1 δ = k.Λ2 δ) (h2 : (k.Λ2 δ).2 = 0) :
    k.dec (b + (k.Λ2 δ).1) (R + δ) = k.dec b R + ((k.Λ2 δ).1, δ) :=
  k.swap.enc_shift b R δ h.symm h2

/-- Lemma 3 (b) for HCTR++ decryption, with the second hash `Λ2`. -/
theorem dec_rest_shift (b : K) (R δ : Fin l → K × K) (h2 : (k.Λ2 δ).2 = 0) :
    (k.dec (b + (k.Λ2 δ).1) (R + δ)).2 = (k.dec b R).2 + δ :=
  k.swap.enc_rest_shift b R δ h2

end HCTRppKey

end SimonHCTR
