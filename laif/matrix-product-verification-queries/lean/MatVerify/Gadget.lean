import MatVerify.Model

/-!
# The code gadget

Vectors over `ZMod 2` indexed by three blocks, of sizes `u`, `u`, `r`. For seeds `Q, R, S` take
the rows `G = [I, Rᵀ + Q Sᵀ, Q]` and `H = [R, I, S]`. Rows of `G` and `H` are orthogonal for every
seed, the dual vectors `a`, `b` are explicit, and a counting argument gives a seed such that no
nonzero vector of weight below `d` is orthogonal to all rows of `G` or to all rows of `H`.
-/

namespace MatVerify

open Finset

/-- Hamming weight. -/
def wt {ι : Type} [Fintype ι] (v : ι → ZMod 2) : ℕ := (univ.filter fun t => v t ≠ 0).card

/-- The object used by the reduction. -/
structure Gadget (n u d N : ℕ) where
  G : Fin u → Fin n → ZMod 2
  H : Fin u → Fin n → ZMod 2
  a : Fin N → Fin n → ZMod 2
  b : Fin N → Fin n → ZMod 2
  GH : ∀ i j, ∑ t, G i t * H j t = 0
  aH : ∀ x j, ∑ t, a x t * H j t = 0
  Gb : ∀ i y, ∑ t, G i t * b y t = 0
  ab : ∀ x y, ∑ t, a x t * b y t = if x = y then 1 else 0
  Gd : ∀ v : Fin n → ZMod 2, v ≠ 0 → wt v < d → ∃ i, ∑ t, G i t * v t ≠ 0
  Hd : ∀ v : Fin n → ZMod 2, v ≠ 0 → wt v < d → ∃ j, ∑ t, H j t * v t ≠ 0

/-! ### Counting by translation -/

lemma fiber_bound {Ω E : Type} [Fintype Ω] [AddCommGroup Ω] [DecidableEq Ω]
    [Fintype E] [AddCommGroup E] [DecidableEq E]
    (φ : Ω → E) (Δ : E → Ω) (h : ∀ ω e, φ (ω + Δ e) = φ ω + e) :
    (univ.filter fun ω => φ ω = 0).card * Fintype.card E ≤ Fintype.card Ω := by
  rw [← Finset.card_univ (α := E), ← card_product, ← Finset.card_univ (α := Ω)]
  apply card_le_card_of_injOn (fun p => p.1 + Δ p.2) (fun _ _ => mem_univ _)
  rintro ⟨ω, e⟩ h1 ⟨ω', e'⟩ h2 heq
  simp only [coe_product, Set.mem_prod, mem_coe, mem_filter, mem_univ, true_and, and_true]
    at h1 h2
  simp only at heq
  have h3 := congrArg φ heq
  rw [h, h, h1, h2, zero_add, zero_add] at h3
  subst h3
  simp only [Prod.mk.injEq, and_true]
  exact add_right_cancel heq

/-! ### Blocks and seeds -/

abbrev Blk (u r : ℕ) := Fin u ⊕ (Fin u ⊕ Fin r)

abbrev Seed (u r : ℕ) :=
  (Fin u → Fin r → ZMod 2) × (Fin u → Fin u → ZMod 2) × (Fin u → Fin r → ZMod 2)

variable {u r : ℕ}

def gRow (ω : Seed u r) (i : Fin u) : Blk u r → ZMod 2
  | .inl l => if i = l then 1 else 0
  | .inr (.inl j) => ω.2.1 j i + ∑ t, ω.1 i t * ω.2.2 j t
  | .inr (.inr t) => ω.1 i t

def hRow (ω : Seed u r) (j : Fin u) : Blk u r → ZMod 2
  | .inl i => ω.2.1 j i
  | .inr (.inl l) => if j = l then 1 else 0
  | .inr (.inr t) => ω.2.2 j t

def aVec (ω : Seed u r) (x : Fin r) : Blk u r → ZMod 2
  | .inl _ => 0
  | .inr (.inl j) => ω.2.2 j x
  | .inr (.inr t) => if x = t then 1 else 0

def bVec (ω : Seed u r) (y : Fin r) : Blk u r → ZMod 2
  | .inl i => ω.1 i y
  | .inr (.inl _) => 0
  | .inr (.inr t) => if y = t then 1 else 0

lemma gRow_hRow (ω : Seed u r) (i j : Fin u) : ∑ t, gRow ω i t * hRow ω j t = 0 := by
  simp only [Fintype.sum_sum_type, gRow, hRow, ite_mul, mul_ite, one_mul, zero_mul, mul_one,
    mul_zero, sum_ite_eq, mem_univ, ite_true]
  generalize ω.2.1 j i = x
  generalize ∑ t, ω.1 i t * ω.2.2 j t = y
  revert x y
  decide

lemma aVec_hRow (ω : Seed u r) (x : Fin r) (j : Fin u) : ∑ t, aVec ω x t * hRow ω j t = 0 := by
  simp only [Fintype.sum_sum_type, aVec, hRow, ite_mul, mul_ite, one_mul, zero_mul, mul_one,
    mul_zero, sum_ite_eq, sum_const_zero, zero_add, mem_univ, ite_true]
  exact CharTwo.add_self_eq_zero _

lemma gRow_bVec (ω : Seed u r) (i : Fin u) (y : Fin r) : ∑ t, gRow ω i t * bVec ω y t = 0 := by
  simp only [Fintype.sum_sum_type, gRow, bVec, ite_mul, mul_ite, one_mul, zero_mul, mul_one,
    mul_zero, sum_ite_eq, sum_const_zero, zero_add, mem_univ, ite_true]
  exact CharTwo.add_self_eq_zero _

lemma aVec_bVec (ω : Seed u r) (x y : Fin r) :
    ∑ t, aVec ω x t * bVec ω y t = if x = y then 1 else 0 := by
  simp only [Fintype.sum_sum_type, aVec, bVec, mul_ite, zero_mul, mul_one,
    mul_zero, sum_ite_eq, sum_const_zero, zero_add, mem_univ, ite_true]

/-! ### A fixed nonzero vector is bad for few seeds -/

/-- `G v` as a function of the seed. -/
def phiG (v : Blk u r → ZMod 2) (ω : Seed u r) : Fin u → ZMod 2 :=
  fun i => ∑ t, gRow ω i t * v t

/-- `H v` as a function of the seed. -/
def phiH (v : Blk u r → ZMod 2) (ω : Seed u r) : Fin u → ZMod 2 :=
  fun j => ∑ t, hRow ω j t * v t

lemma zmod2_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  revert x; decide

lemma card_fun_seed : Fintype.card (Fin u → ZMod 2) = 2 ^ u := by
  simp [ZMod.card]

lemma phiG_bound (v : Blk u r → ZMod 2) (hv : v ≠ 0) :
    (univ.filter fun ω : Seed u r => phiG v ω = 0).card * 2 ^ u ≤ Fintype.card (Seed u r) := by
  rw [← card_fun_seed]
  by_cases h2 : ∃ l, v (.inr (.inl l)) ≠ 0
  · obtain ⟨l, hl⟩ := h2
    have hl1 := zmod2_ne_zero hl
    refine fiber_bound (phiG v) (fun e => (0, fun j i => if j = l then e i else 0, 0)) ?_
    intro ω e
    funext i
    simp only [phiG, Fintype.sum_sum_type, gRow, Pi.add_apply, Prod.fst_add, Prod.snd_add,
      Pi.zero_apply, add_zero, add_mul, ite_mul, zero_mul, sum_add_distrib, sum_ite_eq',
      mem_univ, ite_true, hl1, mul_one]
    abel
  by_cases h3 : ∃ t, v (.inr (.inr t)) ≠ 0
  · obtain ⟨t₀, ht⟩ := h3
    have ht1 := zmod2_ne_zero ht
    push Not at h2
    refine fiber_bound (phiG v) (fun e => (fun i t => if t = t₀ then e i else 0, 0, 0)) ?_
    intro ω e
    funext i
    simp only [phiG, Fintype.sum_sum_type, gRow, Pi.add_apply, Prod.fst_add, Prod.snd_add,
      Pi.zero_apply, add_zero, h2, mul_zero, sum_const_zero, add_mul, ite_mul, zero_mul,
      sum_add_distrib, sum_ite_eq', mem_univ, ite_true, ht1, mul_one]
    abel
  · push Not at h2 h3
    have hne : ∃ l, v (.inl l) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hv
      funext t
      rcases t with l | j | t
      · exact hcon l
      · exact h2 j
      · exact h3 t
    obtain ⟨l, hl⟩ := hne
    have hempty : (univ.filter fun ω : Seed u r => phiG v ω = 0) = ∅ := by
      apply filter_eq_empty_iff.2
      intro ω _ h0
      apply hl
      have := congrFun h0 l
      simpa [phiG, Fintype.sum_sum_type, gRow, h2, h3] using this
    rw [hempty]
    simp

lemma phiH_bound (v : Blk u r → ZMod 2) (hv : v ≠ 0) :
    (univ.filter fun ω : Seed u r => phiH v ω = 0).card * 2 ^ u ≤ Fintype.card (Seed u r) := by
  rw [← card_fun_seed]
  by_cases h1 : ∃ l, v (.inl l) ≠ 0
  · obtain ⟨l, hl⟩ := h1
    have hl1 := zmod2_ne_zero hl
    refine fiber_bound (phiH v) (fun e => (0, fun j i => if i = l then e j else 0, 0)) ?_
    intro ω e
    funext j
    simp only [phiH, Fintype.sum_sum_type, hRow, Pi.add_apply, Prod.fst_add, Prod.snd_add,
      Pi.zero_apply, add_zero, add_mul, ite_mul, zero_mul, sum_add_distrib, sum_ite_eq',
      mem_univ, ite_true, hl1, mul_one]
    abel
  by_cases h3 : ∃ t, v (.inr (.inr t)) ≠ 0
  · obtain ⟨t₀, ht⟩ := h3
    have ht1 := zmod2_ne_zero ht
    push Not at h1
    refine fiber_bound (phiH v) (fun e => (0, 0, fun j t => if t = t₀ then e j else 0)) ?_
    intro ω e
    funext j
    simp only [phiH, Fintype.sum_sum_type, hRow, Pi.add_apply, Prod.fst_add, Prod.snd_add,
      Pi.zero_apply, add_zero, h1, mul_zero, sum_const_zero, zero_add, add_mul, ite_mul, zero_mul,
      sum_add_distrib, sum_ite_eq', mem_univ, ite_true, ht1, mul_one]
    abel
  · push Not at h1 h3
    have hne : ∃ l, v (.inr (.inl l)) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hv
      funext t
      rcases t with l | j | t
      · exact h1 l
      · exact hcon j
      · exact h3 t
    obtain ⟨l, hl⟩ := hne
    have hempty : (univ.filter fun ω : Seed u r => phiH v ω = 0) = ∅ := by
      apply filter_eq_empty_iff.2
      intro ω _ h0
      apply hl
      have := congrFun h0 l
      simpa [phiH, Fintype.sum_sum_type, hRow, h1, h3] using this
    rw [hempty]
    simp

/-! ### Union bound -/

lemma exists_seed (d : ℕ)
    (hB : (univ.filter fun v : Blk u r → ZMod 2 => v ≠ 0 ∧ wt v < d).card * 2 < 2 ^ u) :
    ∃ ω : Seed u r, ∀ v : Blk u r → ZMod 2, v ≠ 0 → wt v < d → phiG v ω ≠ 0 ∧ phiH v ω ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set B := univ.filter fun v : Blk u r → ZMod 2 => v ≠ 0 ∧ wt v < d with hBdef
  have hcover : (univ : Finset (Seed u r)) ⊆ B.biUnion fun v =>
      (univ.filter fun ω : Seed u r => phiG v ω = 0) ∪
        (univ.filter fun ω : Seed u r => phiH v ω = 0) := by
    intro ω _
    obtain ⟨v, hv, hw, himp⟩ := hcon ω
    simp only [mem_biUnion, mem_union, mem_filter, mem_univ, true_and]
    refine ⟨v, by simp [hBdef, hv, hw], ?_⟩
    by_cases h0 : phiG v ω = 0
    · exact Or.inl h0
    · exact Or.inr (himp h0)
  have hle : (Fintype.card (Seed u r)) * 2 ^ u ≤ B.card * 2 * Fintype.card (Seed u r) := by
    calc (Fintype.card (Seed u r)) * 2 ^ u
        ≤ (B.biUnion fun v => (univ.filter fun ω : Seed u r => phiG v ω = 0) ∪
            (univ.filter fun ω : Seed u r => phiH v ω = 0)).card * 2 ^ u := by
          apply Nat.mul_le_mul_right
          rw [← Finset.card_univ]
          exact card_le_card hcover
      _ ≤ (∑ v ∈ B, ((univ.filter fun ω : Seed u r => phiG v ω = 0).card +
            (univ.filter fun ω : Seed u r => phiH v ω = 0).card)) * 2 ^ u := by
          apply Nat.mul_le_mul_right
          exact card_biUnion_le.trans (sum_le_sum fun _ _ => card_union_le _ _)
      _ ≤ ∑ v ∈ B, (2 * Fintype.card (Seed u r)) := by
          rw [sum_mul]
          apply sum_le_sum
          intro v hv
          have hv0 : v ≠ 0 := (mem_filter.1 hv).2.1
          have h1 := phiG_bound v hv0
          have h2 := phiH_bound v hv0
          rw [add_mul]
          omega
      _ = B.card * 2 * Fintype.card (Seed u r) := by
          rw [sum_const, smul_eq_mul, mul_assoc]
  have hpos : 0 < Fintype.card (Seed u r) := Fintype.card_pos
  have h5 : Fintype.card (Seed u r) * 2 ^ u ≤ Fintype.card (Seed u r) * (B.card * 2) := by
    rw [mul_comm (Fintype.card (Seed u r)) (B.card * 2)]
    exact hle
  have := Nat.le_of_mul_le_mul_left h5 hpos
  omega

/-! ### Counting light vectors -/

lemma card_light_le {ι : Type} [Fintype ι] [DecidableEq ι] (n d : ℕ)
    (hn : Fintype.card ι = n) (hd : d ≤ n) :
    (univ.filter fun v : ι → ZMod 2 => wt v < d).card * 32 ^ (n - d) ≤ 33 ^ n := by
  have h1 : (univ.filter fun v : ι → ZMod 2 => wt v < d).card ≤ ∑ i ∈ range d, n.choose i := by
    calc (univ.filter fun v : ι → ZMod 2 => wt v < d).card
        ≤ ((range d).biUnion fun i => powersetCard i (univ : Finset ι)).card := by
          apply card_le_card_of_injOn (fun v => univ.filter fun t => v t ≠ 0)
          · intro v hv
            have hv' : wt v < d := (mem_filter.1 hv).2
            simp only [coe_biUnion, Set.mem_iUnion, mem_coe, mem_powersetCard, subset_univ,
              true_and, mem_range]
            exact ⟨_, hv', rfl⟩
          · intro v _ v' _ heq
            funext t
            have ht := Finset.ext_iff.1 heq t
            simp only [mem_filter, mem_univ, true_and] at ht
            by_cases h0 : v t = 0
            · rw [h0]
              by_contra hne
              exact (ht.2 (fun h => hne h.symm)) h0
            · rw [zmod2_ne_zero h0, zmod2_ne_zero (ht.1 h0)]
      _ ≤ ∑ i ∈ range d, (powersetCard i (univ : Finset ι)).card := card_biUnion_le
      _ = ∑ i ∈ range d, n.choose i := by
          apply sum_congr rfl
          intro i _
          rw [card_powersetCard, Finset.card_univ, hn]
  have h2 : (∑ i ∈ range d, n.choose i) * 32 ^ (n - d) ≤ 33 ^ n := by
    have h33 : (33 : ℕ) ^ n = ∑ m ∈ range (n + 1), 1 ^ m * 32 ^ (n - m) * n.choose m := by
      have := add_pow (1 : ℕ) 32 n
      simpa using this
    rw [h33, sum_mul]
    calc ∑ i ∈ range d, n.choose i * 32 ^ (n - d)
        ≤ ∑ i ∈ range d, 1 ^ i * 32 ^ (n - i) * n.choose i := by
          apply sum_le_sum
          intro i hi
          have : i < d := mem_range.1 hi
          rw [one_pow, one_mul, mul_comm]
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ ≤ _ := sum_le_sum_of_subset (fun i hi => by
          have := mem_range.1 hi
          exact mem_range.2 (by omega))
  exact (Nat.mul_le_mul_right _ h1).trans h2

lemma pow_param (d s : ℕ) (hs : s < 128) :
    33 ^ (128 * d + s) ≤ 2 ^ (11 * d + 6) * 32 ^ (127 * d + s) := by
  have h1 : (33 : ℕ) ^ 128 ≤ 2 ^ 11 * 32 ^ 127 := by norm_num
  have h2 : ∀ s < 128, (33 : ℕ) ^ s ≤ 2 ^ 6 * 32 ^ s := by decide
  calc 33 ^ (128 * d + s) = (33 ^ 128) ^ d * 33 ^ s := by rw [pow_add, pow_mul]
    _ ≤ (2 ^ 11 * 32 ^ 127) ^ d * (2 ^ 6 * 32 ^ s) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left h1 d) (h2 s hs)
    _ = 2 ^ (11 * d + 6) * 32 ^ (127 * d + s) := by
        rw [pow_add 2, pow_add 32, pow_mul 2, pow_mul 32, mul_pow]
        ring

/-! ### The gadget on `Fin n` -/

lemma wt_comp {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (v : κ → ZMod 2) :
    wt (v ∘ e) = wt v := by
  unfold wt
  apply card_equiv e
  intro t
  simp

lemma hsum' {n u N : ℕ} (e : Fin n ≃ Blk u N) (x : Blk u N → ZMod 2) (v : Fin n → ZMod 2) :
    ∑ t, x (e t) * v t = ∑ t, x t * (v ∘ e.symm) t := by
  rw [← e.sum_comp fun t => x t * (v ∘ e.symm) t]
  simp

theorem exists_gadget (n : ℕ) (hn : 256 ≤ n) :
    ∃ d u N, 2 ≤ d ∧ n ≤ 256 * d ∧ d ≤ N ∧ N ≤ n ∧ Nonempty (Gadget n u d N) := by
  set d := n / 128 with hd
  set s := n % 128 with hs
  have hns : n = 128 * d + s := (Nat.div_add_mod n 128).symm
  have hs128 : s < 128 := Nat.mod_lt _ (by norm_num)
  have hd2 : 2 ≤ d := by omega
  set u := 11 * d + 8 with hu
  set N := n - 2 * u with hN
  refine ⟨d, u, N, hd2, by omega, by omega, by omega, ?_⟩
  have hcard : Fintype.card (Blk u N) = n := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hlight := card_light_le (ι := Blk u N) n d hcard (by omega)
  have hpow : n - d = 127 * d + s := by omega
  have h33 : (33 : ℕ) ^ n ≤ 2 ^ (11 * d + 6) * 32 ^ (n - d) := by
    rw [hpow]
    conv_lhs => rw [hns]
    exact pow_param d s hs128
  have hle : (univ.filter fun v : Blk u N → ZMod 2 => wt v < d).card ≤ 2 ^ (11 * d + 6) :=
    Nat.le_of_mul_le_mul_right (hlight.trans h33) (by positivity)
  have hB : (univ.filter fun v : Blk u N → ZMod 2 => v ≠ 0 ∧ wt v < d).card * 2 < 2 ^ u := by
    have hsub : (univ.filter fun v : Blk u N → ZMod 2 => v ≠ 0 ∧ wt v < d).card ≤
        (univ.filter fun v : Blk u N → ZMod 2 => wt v < d).card :=
      card_le_card fun v hv => by
        simp only [mem_filter, mem_univ, true_and] at hv ⊢
        exact hv.2
    have h4 : (2 : ℕ) ^ u = 2 ^ (11 * d + 6) * 4 := by
      rw [hu, show 11 * d + 8 = 11 * d + 6 + 2 by ring, pow_add]
      norm_num
    have hpos : 0 < (2 : ℕ) ^ (11 * d + 6) := by positivity
    omega
  obtain ⟨ω, hω⟩ := exists_seed d hB
  let e : Fin n ≃ Blk u N := (Fintype.equivFinOfCardEq hcard).symm
  have hsum : ∀ f : Blk u N → ZMod 2, ∑ t, f (e t) = ∑ x, f x := fun f => e.sum_comp f
  refine ⟨⟨fun i t => gRow ω i (e t), fun j t => hRow ω j (e t),
    fun x t => aVec ω x (e t), fun y t => bVec ω y (e t), ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i j
    rw [hsum fun x => gRow ω i x * hRow ω j x]
    exact gRow_hRow ω i j
  · intro x j
    rw [hsum fun t => aVec ω x t * hRow ω j t]
    exact aVec_hRow ω x j
  · intro i y
    rw [hsum fun t => gRow ω i t * bVec ω y t]
    exact gRow_bVec ω i y
  · intro x y
    rw [hsum fun t => aVec ω x t * bVec ω y t]
    exact aVec_bVec ω x y
  · intro v hv hw
    have hv' : v ∘ e.symm ≠ 0 := by
      intro h0
      apply hv
      funext t
      simpa using congrFun h0 (e t)
    have hw' : wt (v ∘ e.symm) < d := by rwa [wt_comp]
    have h := (hω _ hv' hw').1
    by_contra hcon
    push Not at hcon
    apply h
    funext i
    have := hcon i
    rw [hsum' e] at this
    exact this
  · intro v hv hw
    have hv' : v ∘ e.symm ≠ 0 := by
      intro h0
      apply hv
      funext t
      simpa using congrFun h0 (e t)
    have hw' : wt (v ∘ e.symm) < d := by rwa [wt_comp]
    have h := (hω _ hv' hw').2
    by_contra hcon
    push Not at hcon
    apply h
    funext i
    have := hcon i
    rw [hsum' e] at this
    exact this

end MatVerify
