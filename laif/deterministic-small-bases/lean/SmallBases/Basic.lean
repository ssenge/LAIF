import Mathlib

/-!
# Deterministic bases for the strong probable prime test and for splitting

Let `B : ℕ → ℕ`. The hypothesis `SmallNonmember B` says that every proper subgroup of
`(ZMod n)ˣ` misses some residue of a positive integer `a ≤ B n`. Under the hypothesis on the
zeros of Dirichlet L-functions it holds with `B n = O((log n)²)`.

From it:

* `prime_of_strongPass`: an odd `n > 2` that passes the strong probable prime test for every base
  `1 ≤ a ≤ B n` is prime;
* `exists_split`: if `N = n₁ n₂` with coprime `n₁, n₂ > 2` and `2 ^ s * m` (with `m` odd) is a
  multiple of the exponent of `(ZMod N)ˣ`, then some base `1 ≤ a ≤ B N` either shares a factor
  with `N` or yields a square root of `1` other than `± 1`;
* `gcd_split`: such a square root gives a divisor of `N` other than `1` and `N`;
* `exists_nonresidue`: for a prime `p` and `1 < r ∣ p - 1`, some `1 ≤ a ≤ B p` is not an `r`-th
  power modulo `p`;
* `smallNonmember_sub_one`, `SmallNonmember.min`: the hypothesis holds with `B n = n - 1`, and
  `B` may be capped at `n - 1`.
-/

namespace SmallBases

/-- Every proper subgroup of `(ZMod n)ˣ`, for `n > 2`, misses the residue of some positive
integer `a ≤ B n`: either `a` is not a unit modulo `n`, or its unit is not in the subgroup.
Under the hypothesis that Dirichlet L-functions have no zeros with real part above `1/2`, this
holds with `B n = O((log n)²)`, with explicit constants in [E. Bach, Explicit bounds for
primality testing and related problems, Math. Comp. 55 (1990), 355-380]. -/
def SmallNonmember (B : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 2 < n → ∀ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ →
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ B n ∧ ∀ h : IsUnit (a : ZMod n), h.unit ∉ H

/-- A unit outside a proper subgroup has a representative in `[1, n - 1]`. -/
lemma exists_small_of_ne_top {n : ℕ} (hn : 2 < n) {H : Subgroup (ZMod n)ˣ} (hH : H ≠ ⊤) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ n - 1 ∧ ∀ h : IsUnit (a : ZMod n), h.unit ∉ H := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨v, hv⟩ : ∃ v, v ∉ H := by
    by_contra h; push Not at h; exact hH (eq_top_iff.mpr fun v _ => h v)
  have hcast : (((v : ZMod n).val : ℕ) : ZMod n) = v := ZMod.natCast_zmod_val _
  refine ⟨(v : ZMod n).val, ?_, ?_, fun h => ?_⟩
  · rw [Nat.one_le_iff_ne_zero, Ne, ZMod.val_eq_zero]; exact v.ne_zero
  · have := ZMod.val_lt (v : ZMod n); omega
  · have : h.unit = v := Units.ext (by rw [IsUnit.unit_spec, hcast])
    rw [this]; exact hv

/-- The hypothesis has content: it holds with `B n = n - 1`. -/
theorem smallNonmember_sub_one : SmallNonmember (fun n => n - 1) :=
  fun _ hn _ hH => exists_small_of_ne_top hn hH

/-- The bound may always be capped at `n - 1`. -/
theorem SmallNonmember.min {B : ℕ → ℕ} (hB : SmallNonmember B) :
    SmallNonmember (fun n => min (B n) (n - 1)) := by
  intro n hn H hH
  obtain ⟨a, ha1, haB, hout⟩ := hB n hn H hH
  by_cases ha : a ≤ n - 1
  · exact ⟨a, ha1, le_min haB ha, hout⟩
  · obtain ⟨a', h1, h2, h3⟩ := exists_small_of_ne_top hn hH
    exact ⟨a', h1, le_min (by omega) h2, h3⟩

/-- The strong probable prime condition for `x` with `n - 1 = 2 ^ s * m`. -/
def Passes {R : Type*} [Monoid R] [HasDistribNeg R] (s m : ℕ) (x : R) : Prop :=
  x ^ m = 1 ∨ ∃ j < s, x ^ (2 ^ j * m) = -1

/-- `n` passes the strong probable prime test to base `a`. -/
def StrongPass (n a s m : ℕ) : Prop := Passes s m (a : ZMod n)

/-- The units whose `k`-th power is `± 1`. -/
def pmOne {R : Type*} [CommRing R] (k : ℕ) : Subgroup Rˣ where
  carrier := {u | (u : R) ^ k = 1 ∨ (u : R) ^ k = -1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq, Units.val_mul, mul_pow] at *
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> simp [hu, hv]
  inv_mem' := by
    intro u hu
    simp only [Set.mem_setOf_eq] at *
    have h : ((u⁻¹ : Rˣ) : R) ^ k * (u : R) ^ k = 1 := by
      rw [← mul_pow, Units.inv_mul, one_pow]
    rcases hu with hu | hu
    · left; simpa [hu] using h
    · right; rw [hu, mul_neg_one, neg_eq_iff_eq_neg] at h; exact h

lemma pow_of_passes {R : Type*} [Monoid R] [HasDistribNeg R] {s m : ℕ} {x : R}
    (h : Passes s m x) : x ^ (2 ^ s * m) = 1 := by
  rcases h with h | ⟨j, hj, h⟩
  · rw [mul_comm, pow_mul, h, one_pow]
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hj
    rw [show 2 ^ (j + t + 1) * m = 2 ^ j * m * 2 ^ (t + 1) by ring, pow_mul, h]
    exact Even.neg_one_pow ⟨2 ^ t, by ring⟩

lemma isUnit_of_passes {R : Type*} [CommMonoid R] [HasDistribNeg R] {s m : ℕ} (hm : Odd m)
    {x : R} (h : Passes s m x) : IsUnit x := by
  have hm0 : m ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hm)
  rcases h with h | ⟨j, -, h⟩
  · exact (isUnit_pow_iff hm0).mp (by rw [h]; exact isUnit_one)
  · exact (isUnit_pow_iff (n := 2 ^ j * m) (mul_ne_zero (pow_ne_zero _ two_ne_zero) hm0)).mp
      (by rw [h]; exact isUnit_one.neg)

/-- The units of `ZMod (n₁ * n₂)` that pass the strong condition lie in a proper subgroup, when
`n₁` and `n₂` are coprime and both exceed `2`. -/
theorem liars_le_proper {n₁ n₂ : ℕ} (hcop : n₁.Coprime n₂) (h₁ : 2 < n₁) (h₂ : 2 < n₂)
    {s m : ℕ} (hm : Odd m) :
    ∃ H : Subgroup (ZMod (n₁ * n₂))ˣ, H ≠ ⊤ ∧
      ∀ u : (ZMod (n₁ * n₂))ˣ, Passes s m (u : ZMod (n₁ * n₂)) → u ∈ H := by
  classical
  have : Fact (2 < n₁) := ⟨h₁⟩
  have : Fact (2 < n₂) := ⟨h₂⟩
  set N := n₁ * n₂
  let P : ℕ → Prop := fun j => ∃ u : (ZMod N)ˣ, (u : ZMod N) ^ (2 ^ j * m) = -1
  have hP0 : P 0 := ⟨-1, by simp [hm.neg_one_pow]⟩
  set j₀ := Nat.findGreatest P s
  have hPj : P j₀ := Nat.findGreatest_spec (P := P) (Nat.zero_le s) hP0
  have hmax : ∀ j, j < s → P j → j ≤ j₀ := fun j hj hPj' =>
    Nat.le_findGreatest hj.le hPj'
  refine ⟨pmOne (2 ^ j₀ * m), ?_, ?_⟩
  · -- a unit that is `-1` modulo `n₁` side and `1` modulo `n₂` after the power
    obtain ⟨b, hb⟩ := hPj
    let e := ZMod.chineseRemainder hcop
    let x : ZMod N := e.symm ((e b).1, 1)
    let y : ZMod N := e.symm ((e (↑b⁻¹ : ZMod N)).1, 1)
    have hxy : x * y = 1 := by
      apply e.injective
      rw [map_mul, map_one]
      simp only [x, y, RingEquiv.apply_symm_apply]
      ext
      · simp only [Prod.fst_mul, Prod.fst_one]
        rw [← Prod.fst_mul, ← map_mul, Units.mul_inv, map_one, Prod.fst_one]
      · simp
    have hxu : IsUnit x := isUnit_iff_exists_inv.mpr ⟨y, hxy⟩
    intro htop
    have hmem : hxu.unit ∈ pmOne (R := ZMod N) (2 ^ j₀ * m) := htop ▸ Subgroup.mem_top _
    have hex : e (x ^ (2 ^ j₀ * m)) = (-1, 1) := by
      rw [map_pow]
      simp only [x, RingEquiv.apply_symm_apply]
      ext
      · show (e (b : ZMod N)).1 ^ (2 ^ j₀ * m) = -1
        rw [← Prod.pow_fst, ← map_pow, hb]
        simp
      · simp
    change ((hxu.unit : ZMod N) ^ (2 ^ j₀ * m) = 1 ∨ (hxu.unit : ZMod N) ^ (2 ^ j₀ * m) = -1) at hmem
    rw [IsUnit.unit_spec] at hmem
    rcases hmem with h | h
    · rw [h, map_one] at hex
      exact ZMod.neg_one_ne_one (congrArg Prod.fst hex).symm
    · rw [h, map_neg, map_one] at hex
      exact ZMod.neg_one_ne_one (n := n₂) (by simpa using (congrArg Prod.snd hex))
  · intro u hu
    change ((u : ZMod N) ^ (2 ^ j₀ * m) = 1 ∨ (u : ZMod N) ^ (2 ^ j₀ * m) = -1)
    rcases hu with hu | ⟨j, hj, hu⟩
    · left; rw [mul_comm, pow_mul, hu, one_pow]
    · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (hmax j hj ⟨u, hu⟩)
      rw [ht]
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · right; simpa [h0] using hu
      · left
        obtain ⟨t', rfl⟩ := Nat.exists_eq_add_of_lt hpos
        rw [show 2 ^ (j + (0 + t' + 1)) * m = 2 ^ j * m * 2 ^ (t' + 1) by ring, pow_mul, hu]
        exact Even.neg_one_pow ⟨2 ^ t', by ring⟩

/-- An odd composite `n > 2` with `u ^ (n - 1) = 1` for all units splits as a product of two
coprime factors above `2`. -/
lemma split_of_fermat {n : ℕ} (hn : 2 < n) (hodd : Odd n) (hp : ¬ n.Prime)
    (hF : ∀ u : (ZMod n)ˣ, (u : ZMod n) ^ (n - 1) = 1) :
    ∃ n₁ n₂, n = n₁ * n₂ ∧ n₁.Coprime n₂ ∧ 2 < n₁ ∧ 2 < n₂ := by
  have hC : n.IsCarmichael := by
    refine ⟨hn, hp, fun b hb => ?_⟩
    have hb0 : b ≠ 0 := by
      rintro rfl; simp at hb; omega
    rw [Nat.probablePrime_iff_zmod_one n hb0]
    simpa using hF (ZMod.unitOfCoprime b hb)
  have hsq := hC.squarefree
  set p := n.minFac
  have hpp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  obtain ⟨q, hq⟩ := hpn
  have hpodd : Odd p := hodd.of_dvd_nat ⟨q, hq⟩
  have hqodd : Odd q := hodd.of_dvd_nat ⟨p, by rw [hq, mul_comm]⟩
  have hp2 : 2 < p := by
    rcases hpp.two_le.lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at hpodd; exact absurd hpodd (by decide)
  have hq1 : q ≠ 1 := by rintro rfl; rw [mul_one] at hq; exact hp (hq ▸ hpp)
  have hq0 : q ≠ 0 := by rintro rfl; omega
  have hq2 : 2 < q := by
    rcases hqodd with ⟨k, hk⟩; omega
  refine ⟨p, q, hq, ?_, hp2, hq2⟩
  rw [Nat.Prime.coprime_iff_not_dvd hpp]
  rintro ⟨r, rfl⟩
  have := hsq p ⟨r, by rw [hq]; ring⟩
  exact hpp.one_lt.ne' (Nat.isUnit_iff.mp this)

/-- An odd `n > 2` that passes the strong probable prime test for every base `1 ≤ a ≤ B n`
is prime. -/
theorem prime_of_strongPass {B : ℕ → ℕ} (hB : SmallNonmember B) {n s m : ℕ} (hn : 2 < n)
    (hodd : Odd n) (hsm : n - 1 = 2 ^ s * m) (hm : Odd m)
    (hpass : ∀ a, 1 ≤ a → a ≤ B n → StrongPass n a s m) : n.Prime := by
  classical
  by_contra hp
  obtain ⟨H, hH, hlie⟩ : ∃ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ ∧
      ∀ u : (ZMod n)ˣ, Passes s m (u : ZMod n) → u ∈ H := by
    by_cases hF : ∀ u : (ZMod n)ˣ, (u : ZMod n) ^ (n - 1) = 1
    · obtain ⟨n₁, n₂, rfl, hcop, h₁, h₂⟩ := split_of_fermat hn hodd hp hF
      exact liars_le_proper hcop h₁ h₂ hm
    · push_neg at hF
      obtain ⟨v, hv⟩ := hF
      refine ⟨(powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker, ?_, ?_⟩
      · intro htop
        have : v ∈ (powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker := htop ▸ Subgroup.mem_top v
        rw [MonoidHom.mem_ker, powMonoidHom_apply] at this
        exact hv (by rw [← Units.val_pow_eq_pow_val, this, Units.val_one])
      · intro u hu
        rw [MonoidHom.mem_ker, powMonoidHom_apply]
        ext
        rw [Units.val_pow_eq_pow_val, hsm, pow_of_passes hu, Units.val_one]
  obtain ⟨a, ha1, haB, hout⟩ := hB n hn H hH
  have hpa := hpass a ha1 haB
  have hu : IsUnit (a : ZMod n) := isUnit_of_passes hm hpa
  exact hout hu (hlie _ (by rw [IsUnit.unit_spec]; exact hpa))

/-- With a multiple `2 ^ s * m` of the exponent of `(ZMod N)ˣ`, `N = n₁ n₂` with coprime factors
above `2`, some base `1 ≤ a ≤ B N` with `a < N` is not a unit, or has a power `y` with
`y ^ 2 = 1` and `y ≠ ± 1`. -/
theorem exists_split {B : ℕ → ℕ} (hB : SmallNonmember B) {n₁ n₂ s m : ℕ}
    (hcop : n₁.Coprime n₂) (h₁ : 2 < n₁) (h₂ : 2 < n₂) (hm : Odd m)
    (hL : ∀ u : (ZMod (n₁ * n₂))ˣ, (u : ZMod (n₁ * n₂)) ^ (2 ^ s * m) = 1) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ B (n₁ * n₂) ∧ a < n₁ * n₂ ∧ (¬ IsUnit (a : ZMod (n₁ * n₂)) ∨
      ∃ j < s, ((a : ZMod (n₁ * n₂)) ^ (2 ^ j * m)) ^ 2 = 1 ∧
        (a : ZMod (n₁ * n₂)) ^ (2 ^ j * m) ≠ 1 ∧ (a : ZMod (n₁ * n₂)) ^ (2 ^ j * m) ≠ -1) := by
  classical
  obtain ⟨H, hH, hlie⟩ := liars_le_proper hcop h₁ h₂ (s := s) hm
  obtain ⟨a, ha1, haB, hout⟩ := hB.min (n₁ * n₂) (by nlinarith) H hH
  refine ⟨a, ha1, haB.trans (min_le_left _ _), by have := haB.trans (min_le_right _ _); omega, ?_⟩
  by_cases hu : IsUnit (a : ZMod (n₁ * n₂))
  · right
    set x : ZMod (n₁ * n₂) := (a : ZMod (n₁ * n₂))
    have hnp : ¬ Passes s m x := fun h => hout hu (hlie _ (by rw [IsUnit.unit_spec]; exact h))
    have hx1 : x ^ (2 ^ s * m) = 1 := by
      have := hL hu.unit; rwa [IsUnit.unit_spec] at this
    have hex : ∃ j, x ^ (2 ^ j * m) = 1 := ⟨s, hx1⟩
    set k := Nat.find hex
    have hk : x ^ (2 ^ k * m) = 1 := Nat.find_spec hex
    have hks : k ≤ s := Nat.find_min' hex hx1
    have hk0 : k ≠ 0 := by
      intro h0; apply hnp; left; simpa [h0] using hk
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hjs : j < s := by omega
    refine ⟨j, hjs, ?_, ?_, ?_⟩
    · rw [← pow_mul, show 2 ^ j * m * 2 = 2 ^ k * m by rw [hj, pow_succ]; ring, hk]
    · exact Nat.find_min hex (show j < k by omega)
    · intro h; exact hnp (Or.inr ⟨j, hjs, h⟩)
  · left; exact hu

/-- A square root of `1` other than `± 1` modulo `N` gives a divisor of `N` other than `1`
and `N`. -/
theorem gcd_split {N : ℕ} [NeZero N] {y : ZMod N} (hy : y ^ 2 = 1) (h1 : y ≠ 1) (h2 : y ≠ -1) :
    Nat.gcd (y - 1).val N ≠ 1 ∧ Nat.gcd (y - 1).val N ≠ N := by
  have hcast : (((y - 1).val : ℕ) : ZMod N) = y - 1 := ZMod.natCast_zmod_val _
  constructor
  · intro hc
    have hunit : IsUnit (y - 1) := by
      rw [← hcast]; exact (ZMod.isUnit_iff_coprime _ N).mpr hc
    have hprod : (y - 1) * (y + 1) = 0 := by
      have : (y - 1) * (y + 1) = y ^ 2 - 1 := by ring
      rw [this, hy, sub_self]
    have : y + 1 = 0 := (hunit.mul_right_eq_zero).mp hprod
    exact h2 (eq_neg_of_add_eq_zero_left this)
  · intro hc
    have hd : N ∣ (y - 1).val := by
      have := Nat.gcd_dvd_left (y - 1).val N; rwa [hc] at this
    have : (((y - 1).val : ℕ) : ZMod N) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [hcast, sub_eq_zero] at this
    exact h1 this

/-- For a prime `p` and `1 < r` dividing `p - 1`, some `1 ≤ a ≤ B p` is not an `r`-th power
modulo `p`. -/
theorem exists_nonresidue {B : ℕ → ℕ} (hB : SmallNonmember B) {p r : ℕ} [hp : Fact p.Prime]
    (hp2 : 2 < p) (hr : 1 < r) (hrp : r ∣ p - 1) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ B p ∧ ∀ y : ZMod p, y ^ r ≠ a := by
  classical
  set f : (ZMod p)ˣ →* (ZMod p)ˣ := powMonoidHom r
  have hns : ¬ Function.Surjective f := by
    rw [← Finite.injective_iff_surjective]
    intro hinj
    obtain ⟨q, hq, hqr⟩ := Nat.exists_prime_and_dvd (show r ≠ 1 by omega)
    have hcard : q ∣ Nat.card (ZMod p)ˣ := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
      exact hqr.trans hrp
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hcard
    have hgr : f g = f 1 := by
      simp only [f, powMonoidHom_apply, one_pow]
      exact orderOf_dvd_iff_pow_eq_one.mp (hg ▸ hqr)
    have := hinj hgr
    rw [this, orderOf_one] at hg
    exact hq.one_lt.ne hg
  have hH : f.range ≠ ⊤ := by
    intro htop; apply hns; intro y
    exact MonoidHom.mem_range.mp (htop ▸ Subgroup.mem_top y)
  obtain ⟨a, ha1, haB, hout⟩ := hB.min p hp2 f.range hH
  refine ⟨a, ha1, haB.trans (min_le_left _ _), ?_⟩
  have h0 : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd; have := Nat.le_of_dvd (by omega) hd; have := haB.trans (min_le_right _ _); omega
  · intro y hy
    have hyu : IsUnit y := by
      rw [isUnit_iff_ne_zero]
      rintro rfl
      rw [zero_pow (by omega)] at hy
      exact h0 hy.symm
    have hau : IsUnit (a : ZMod p) := isUnit_iff_ne_zero.mpr h0
    apply hout hau
    refine ⟨hyu.unit, ?_⟩
    ext
    simp [f, hy]

end SmallBases
