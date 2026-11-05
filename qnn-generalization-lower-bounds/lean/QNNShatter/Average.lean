import QNNShatter.AntiConcentration

/-!
# Averaging the kernel weight over random matrices

For an `m × T` matrix `A` with entries in `{0, …, M}` and a weight `ρ : ℤ → [0, ∞]` with
`ρ 0 = 1` and `∑_{z ≠ 0} ρ z = τ`, let

  `S(A) = ∑_{k ∈ ℤ^m, k ≠ 0, Aᵀ k = 0} ∏ j, ρ (k j)`.

Summing over all `(M+1)^(mT)` matrices,

* `∑_A S(A) ≤ (M+1)^(mT) · ((1+τ)^m - 1) / (M+1)^T`, and
* for `M = 1`, `∑_A S(A) ≤ 2^(mT) · ∑_{v=1}^m C(m,v) τ^v q(v)^T` with
  `q(v) = C(v, ⌊v/2⌋) / 2^v`.

So some `A` has `S(A) < 1` as soon as the corresponding right side, divided by the number of
matrices, is below `1`. Sums are taken in `[0, ∞]`, so no summability hypothesis is needed.
-/

open Finset
open scoped ENNReal

namespace QNNShatter

noncomputable section

/-- The sum over `ℤ^m` (or any `α^m`) of a product weight is the product of the sums. -/
theorem tsum_fin_prod {α : Type*} : ∀ (m : ℕ) (f : Fin m → α → ℝ≥0∞),
    ∑' k : Fin m → α, ∏ j, f j (k j) = ∏ j, ∑' z, f j z
  | 0, f => by simp
  | m + 1, f => by
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => α)).tsum_eq]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left, tsum_fin_prod m (fun j => f j.succ), ENNReal.tsum_mul_right]

variable {m T M : ℕ}

/-- `Aᵀ k = 0` for an `m × T` matrix `A` with entries in `{0, …, M}`. -/
def InKer (A : Fin m → Fin T → Fin (M + 1)) (k : Fin m → ℤ) : Prop :=
  ∀ i, ∑ j, k j * ((A j i : ℕ) : ℤ) = 0

instance (A : Fin m → Fin T → Fin (M + 1)) (k : Fin m → ℤ) : Decidable (InKer A k) := by
  unfold InKer; infer_instance

/-- `S(A) = ∑_{k ∈ ℤ^m, k ≠ 0, Aᵀ k = 0} ∏ j, ρ (k j)`. -/
def S (ρ : ℤ → ℝ≥0∞) (A : Fin m → Fin T → Fin (M + 1)) : ℝ≥0∞ :=
  ∑' k : Fin m → ℤ, if k ≠ 0 ∧ InKer A k then ∏ j, ρ (k j) else 0

/-- The columns of `A` are independent: the number of matrices with `Aᵀ k = 0` is the `T`-th
power of the number of columns `a` with `∑ j, k j * a j = 0`. -/
theorem card_inKer (k : Fin m → ℤ) :
    (univ.filter fun A : Fin m → Fin T → Fin (M + 1) => InKer A k).card
      = (solutions M k 0).card ^ T := by
  have h : (solutions M k 0).card ^ T
      = (Fintype.piFinset fun _ : Fin T => solutions M k 0).card := by
    rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
  rw [h]
  refine Finset.card_nbij' (fun A i j => A j i) (fun B j i => B i j) ?_ ?_ ?_ ?_
  · intro A hA
    rw [mem_coe, mem_filter] at hA
    rw [mem_coe, Fintype.mem_piFinset]
    intro i
    rw [mem_solutions]
    exact hA.2 i
  · intro B hB
    rw [mem_coe, Fintype.mem_piFinset] at hB
    rw [mem_coe, mem_filter]
    exact ⟨mem_univ _, fun i => mem_solutions.1 (hB i)⟩
  · intro A _; rfl
  · intro B _; rfl

/-- Exchanging the finite sum over matrices with the sum over `k`. -/
theorem sum_S (ρ : ℤ → ℝ≥0∞) :
    ∑ A : Fin m → Fin T → Fin (M + 1), S ρ A
      = ∑' k : Fin m → ℤ, if k ≠ 0 then
          ((univ.filter fun A : Fin m → Fin T → Fin (M + 1) => InKer A k).card : ℝ≥0∞)
            * ∏ j, ρ (k j) else 0 := by
  unfold S
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr fun k => ?_
  by_cases hk : k ≠ 0
  · rw [if_pos hk]
    simp only [and_iff_right hk]
    rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
  · simp [hk]

/-- `∑_{k ∈ ℤ^m, k ≠ 0} ∏ j, ρ (k j) = (1 + τ)^m - 1`. -/
theorem tsum_prod_ne_zero (ρ : ℤ → ℝ≥0∞) (hρ0 : ρ 0 = 1) (τ : ℝ≥0∞)
    (hτ : ∑' z, (if z = 0 then 0 else ρ z) = τ) :
    ∑' k : Fin m → ℤ, (if k ≠ 0 then ∏ j, ρ (k j) else 0) = (1 + τ) ^ m - 1 := by
  have hsum : ∑' z, ρ z = 1 + τ := by
    rw [ENNReal.tsum_eq_add_tsum_ite 0, hρ0, ← hτ]
    exact congrArg (1 + ·) (tsum_congr fun z => by split_ifs <;> rfl)
  have hall := tsum_fin_prod m (fun _ => ρ)
  simp only [hsum, prod_const, card_univ, Fintype.card_fin] at hall
  rw [ENNReal.tsum_eq_add_tsum_ite 0] at hall
  simp only [Pi.zero_apply, hρ0, prod_const_one] at hall
  refine ENNReal.eq_sub_of_add_eq ENNReal.one_ne_top ?_
  rw [add_comm, ← hall]
  congr 1
  exact tsum_congr fun k => by by_cases hk : k = 0 <;> simp [hk]

/-- From a bound on the total over a finite nonempty set, some value is below `1`. -/
theorem exists_lt_one_of_sum_le {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ≥0∞)
    (B : ℝ≥0∞) (hB : B < 1) (h : ∑ a, f a ≤ Fintype.card α * B) : ∃ a, f a < 1 := by
  by_contra hne
  push Not at hne
  have h1 : (Fintype.card α : ℝ≥0∞) ≤ ∑ a, f a := by
    calc (Fintype.card α : ℝ≥0∞) = ∑ _a : α, (1 : ℝ≥0∞) := by simp
      _ ≤ ∑ a, f a := Finset.sum_le_sum fun a _ => hne a
  have hc0 : (Fintype.card α : ℝ≥0∞) ≠ 0 := by simp
  have hct : (Fintype.card α : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h2 : (Fintype.card α : ℝ≥0∞) * B < Fintype.card α := by
    calc (Fintype.card α : ℝ≥0∞) * B = B * Fintype.card α := mul_comm _ _
      _ < 1 * Fintype.card α := ENNReal.mul_lt_mul_left hc0 hct hB
      _ = Fintype.card α := one_mul _
  exact absurd (h1.trans h) (not_le.2 h2)

theorem card_matrices :
    Fintype.card (Fin m → Fin T → Fin (M + 1)) = (M + 1) ^ (m * T) := by
  simp [← pow_mul, mul_comm]

/-! ### Entries in `{0, …, M}` -/

/-- For `k ≠ 0`, at most a `(M+1)^(-T)` fraction of the matrices has `Aᵀ k = 0`. -/
theorem card_inKer_mul_le (k : Fin m → ℤ) (hk : k ≠ 0) :
    (univ.filter fun A : Fin m → Fin T → Fin (M + 1) => InKer A k).card * (M + 1) ^ T
      ≤ (M + 1) ^ (m * T) := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, k j ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  have h1 := card_solutions_le_fin M k j₀ hj₀ 0
  have hm : 1 ≤ m := j₀.pos
  rw [card_inKer, ← mul_pow, pow_mul]
  apply Nat.pow_le_pow_left
  calc (solutions M k 0).card * (M + 1) ≤ (M + 1) ^ (m - 1) * (M + 1) :=
        Nat.mul_le_mul_right _ h1
    _ = (M + 1) ^ m := by rw [← pow_succ]; congr 1; omega

/-- Total of `S(A)` over all matrices with entries in `{0, …, M}`, multiplied out. -/
theorem sum_S_le_reuse_mul (ρ : ℤ → ℝ≥0∞) (hρ0 : ρ 0 = 1) (τ : ℝ≥0∞)
    (hτ : ∑' z, (if z = 0 then 0 else ρ z) = τ) :
    (M + 1 : ℝ≥0∞) ^ T * ∑ A : Fin m → Fin T → Fin (M + 1), S ρ A
      ≤ (M + 1 : ℝ≥0∞) ^ (m * T) * ((1 + τ) ^ m - 1) := by
  rw [sum_S, ← ENNReal.tsum_mul_left, ← tsum_prod_ne_zero ρ hρ0 τ hτ, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases hk : k ≠ 0
  · rw [if_pos hk, if_pos hk]
    have h := card_inKer_mul_le (T := T) (M := M) k hk
    have h' : (M + 1 : ℝ≥0∞) ^ T
        * ((univ.filter fun A : Fin m → Fin T → Fin (M + 1) => InKer A k).card : ℝ≥0∞)
        ≤ (M + 1 : ℝ≥0∞) ^ (m * T) := by
      rw [mul_comm]; exact_mod_cast h
    calc (M + 1 : ℝ≥0∞) ^ T
          * (((univ.filter fun A : Fin m → Fin T → Fin (M + 1) => InKer A k).card : ℝ≥0∞)
            * ∏ j, ρ (k j))
        = ((M + 1 : ℝ≥0∞) ^ T
          * ((univ.filter fun A : Fin m → Fin T → Fin (M + 1) => InKer A k).card : ℝ≥0∞))
            * ∏ j, ρ (k j) := by ring
      _ ≤ (M + 1 : ℝ≥0∞) ^ (m * T) * ∏ j, ρ (k j) := by gcongr
  · simp [hk]

/-- **Average of `S(A)`, entries in `{0, …, M}`.** The mean of `S(A)` over all matrices
`A ∈ {0, …, M}^(m × T)` is at most `((1+τ)^m - 1) / (M+1)^T`. -/
theorem avg_S_le_reuse (ρ : ℤ → ℝ≥0∞) (hρ0 : ρ 0 = 1) (τ : ℝ≥0∞)
    (hτ : ∑' z, (if z = 0 then 0 else ρ z) = τ) :
    (∑ A : Fin m → Fin T → Fin (M + 1), S ρ A)
        / (Fintype.card (Fin m → Fin T → Fin (M + 1)) : ℝ≥0∞)
      ≤ ((1 + τ) ^ m - 1) / (M + 1 : ℝ≥0∞) ^ T := by
  have h := sum_S_le_reuse_mul (m := m) (T := T) (M := M) ρ hρ0 τ hτ
  have hne0 : (M + 1 : ℝ≥0∞) ^ T ≠ 0 := pow_ne_zero _ (by simp)
  have hnet : (M + 1 : ℝ≥0∞) ^ T ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  rw [card_matrices]
  refine ENNReal.div_le_of_le_mul ?_
  push_cast
  have h2 : ∑ A : Fin m → Fin T → Fin (M + 1), S ρ A
      ≤ (M + 1 : ℝ≥0∞) ^ (m * T) * ((1 + τ) ^ m - 1) / (M + 1 : ℝ≥0∞) ^ T := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl hnet), mul_comm]
    exact h
  calc ∑ A : Fin m → Fin T → Fin (M + 1), S ρ A
      ≤ (M + 1 : ℝ≥0∞) ^ (m * T) * ((1 + τ) ^ m - 1) / (M + 1 : ℝ≥0∞) ^ T := h2
    _ = ((1 + τ) ^ m - 1) / (M + 1 : ℝ≥0∞) ^ T * (M + 1 : ℝ≥0∞) ^ (m * T) := by
      simp only [div_eq_mul_inv]; ring

/-- **Existence, entries in `{0, …, M}`.** If `((1+τ)^m - 1) / (M+1)^T < 1`, some matrix
`A ∈ {0, …, M}^(m × T)` has `S(A) < 1`. -/
theorem exists_S_lt_one_reuse (ρ : ℤ → ℝ≥0∞) (hρ0 : ρ 0 = 1) (τ : ℝ≥0∞)
    (hτ : ∑' z, (if z = 0 then 0 else ρ z) = τ)
    (hlt : ((1 + τ) ^ m - 1) / (M + 1 : ℝ≥0∞) ^ T < 1) :
    ∃ A : Fin m → Fin T → Fin (M + 1), S ρ A < 1 := by
  refine exists_lt_one_of_sum_le _ _ hlt ?_
  have h := avg_S_le_reuse (m := m) (T := T) (M := M) ρ hρ0 τ hτ
  have hc0 : (Fintype.card (Fin m → Fin T → Fin (M + 1)) : ℝ≥0∞) ≠ 0 := by simp
  have hct : (Fintype.card (Fin m → Fin T → Fin (M + 1)) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [ENNReal.div_le_iff hc0 hct] at h
  exact h.trans_eq (mul_comm _ _)

/-! ### Entries in `{0, 1}` -/

/-- `q(v) = C(v, ⌊v/2⌋) / 2^v`. -/
def q (v : ℕ) : ℝ≥0∞ := (v.choose (v / 2) : ℝ≥0∞) / 2 ^ v

/-- The support `{j | k j ≠ 0}` of `k`. -/
def supp (k : Fin m → ℤ) : Finset (Fin m) := univ.filter fun j => k j ≠ 0

theorem supp_eq_empty_iff (k : Fin m → ℤ) : supp k = ∅ ↔ k = 0 := by
  rw [supp, Finset.filter_eq_empty_iff]
  constructor
  · intro h; funext j; simpa using h (mem_univ j)
  · intro h j _; simp [h]

/-- Anti-concentration with zero coordinates: if `k` has `v` nonzero entries, at most
`2^(m-v) C(v, ⌊v/2⌋)` vectors `a ∈ {0,1}^m` satisfy `∑ j, k j * a j = 0`. -/
theorem card_solutions_two_mul_le (k : Fin m → ℤ) :
    (solutions 1 k 0).card * 2 ^ (supp k).card ≤ 2 ^ m * (supp k).card.choose ((supp k).card / 2) := by
  set s := supp k with hs
  let ks : s → ℤ := fun j => k j
  have hks : ∀ j, ks j ≠ 0 := fun j => by
    have := j.2
    simp only [hs, supp, mem_filter, mem_univ, true_and] at this
    exact this
  have hA := card_solutions_two_le ks hks 0
  rw [Fintype.card_coe] at hA
  have hinj : (solutions 1 k 0).card
      ≤ (solutions 1 ks 0 ×ˢ (univ : Finset ({j // j ∉ s} → Fin 2))).card := by
    refine Finset.card_le_card_of_injOn
      (fun a => ((fun j : s => a j), (fun j : {j // j ∉ s} => a j))) ?_ ?_
    · intro a ha
      have ha' := mem_solutions.1 ha
      simp only [coe_product, coe_univ, Set.mem_prod, mem_coe, mem_solutions, Set.mem_univ,
        and_true]
      rw [Finset.sum_coe_sort s (fun j => k j * ((a j : ℕ) : ℤ)), hs, supp,
        Finset.sum_filter_of_ne (fun j _ hj => left_ne_zero_of_mul hj)]
      exact ha'
    · intro a _ b _ h
      simp only [Prod.mk.injEq] at h
      funext j
      by_cases hj : j ∈ s
      · exact congrFun h.1 ⟨j, hj⟩
      · exact congrFun h.2 ⟨j, hj⟩
  have hcard : (solutions 1 ks 0 ×ˢ (univ : Finset ({j // j ∉ s} → Fin 2))).card
      = (solutions 1 ks 0).card * 2 ^ (m - s.card) := by
    rw [card_product, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype_compl,
      Fintype.card_coe, Fintype.card_fin]
  have hle : s.card ≤ m := by
    calc s.card ≤ (univ : Finset (Fin m)).card := card_le_univ s
      _ = m := by simp
  calc (solutions 1 k 0).card * 2 ^ s.card
      ≤ (solutions 1 ks 0).card * 2 ^ (m - s.card) * 2 ^ s.card := by
        rw [← hcard]; exact Nat.mul_le_mul_right _ hinj
    _ = (solutions 1 ks 0).card * 2 ^ m := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    _ ≤ s.card.choose (s.card / 2) * 2 ^ m := Nat.mul_le_mul_right _ hA
    _ = 2 ^ m * s.card.choose (s.card / 2) := mul_comm _ _

/-- For `M = 1`, the number of matrices with `Aᵀ k = 0` is at most `2^(mT) q(v)^T`, where `v` is
the number of nonzero entries of `k`. -/
theorem card_inKer_two_le (k : Fin m → ℤ) :
    ((univ.filter fun A : Fin m → Fin T → Fin 2 => InKer A k).card : ℝ≥0∞)
      ≤ 2 ^ (m * T) * q (supp k).card ^ T := by
  rw [card_inKer, Nat.cast_pow, pow_mul, ← mul_pow]
  refine pow_le_pow_left₀ zero_le ?_ T
  have h := card_solutions_two_mul_le k
  have hne0 : (2 : ℝ≥0∞) ^ (supp k).card ≠ 0 := pow_ne_zero _ (by simp)
  have hnet : (2 : ℝ≥0∞) ^ (supp k).card ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  rw [q, ← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl hnet)]
  exact_mod_cast h

/-- The weight of the vectors `k` with support exactly `s` is `τ^|s|`. -/
theorem tsum_supp_eq (ρ : ℤ → ℝ≥0∞) (hρ0 : ρ 0 = 1) (τ : ℝ≥0∞)
    (hτ : ∑' z, (if z = 0 then 0 else ρ z) = τ) (s : Finset (Fin m)) :
    ∑' k : Fin m → ℤ, (if supp k = s then ∏ j, ρ (k j) else 0) = τ ^ s.card := by
  let g : Fin m → ℤ → ℝ≥0∞ := fun j z =>
    if j ∈ s then (if z = 0 then 0 else ρ z) else (if z = 0 then 1 else 0)
  have hpt : ∀ k : Fin m → ℤ, (if supp k = s then ∏ j, ρ (k j) else 0) = ∏ j, g j (k j) := by
    intro k
    by_cases h : supp k = s
    · rw [if_pos h]
      refine Finset.prod_congr rfl fun j _ => ?_
      have hj : j ∈ s ↔ k j ≠ 0 := by rw [← h]; simp [supp]
      by_cases hk : k j = 0
      · have : j ∉ s := by rw [hj]; simpa using hk
        simp [g, this, hk, hρ0]
      · have : j ∈ s := hj.2 hk
        simp [g, this, hk]
    · rw [if_neg h]
      have : ∃ j, ¬ (j ∈ supp k ↔ j ∈ s) := by
        by_contra hc
        push Not at hc
        exact h (Finset.ext hc)
      obtain ⟨j, hj⟩ := this
      refine (Finset.prod_eq_zero (mem_univ j) ?_).symm
      simp only [supp, mem_filter, mem_univ, true_and] at hj
      by_cases hs : j ∈ s
      · have : k j = 0 := by tauto
        simp [g, hs, this]
      · have : k j ≠ 0 := by tauto
        simp [g, hs, this]
  simp_rw [hpt]
  rw [tsum_fin_prod m g]
  have hg : ∀ j, ∑' z, g j z = if j ∈ s then τ else 1 := by
    intro j
    by_cases hs : j ∈ s
    · simp only [g, hs, if_true]; exact hτ
    · simp [g, hs]
  simp_rw [hg]
  rw [Finset.prod_ite_mem, univ_inter, prod_const]

/-- Grouping the vectors `k ≠ 0` by the size of their support. -/
theorem tsum_group_supp (ρ : ℤ → ℝ≥0∞) (hρ0 : ρ 0 = 1) (τ : ℝ≥0∞)
    (hτ : ∑' z, (if z = 0 then 0 else ρ z) = τ) (g : ℕ → ℝ≥0∞) :
    ∑' k : Fin m → ℤ, (if k ≠ 0 then g (supp k).card * ∏ j, ρ (k j) else 0)
      = ∑ v ∈ Icc 1 m, (m.choose v : ℝ≥0∞) * τ ^ v * g v := by
  have hpt : ∀ k : Fin m → ℤ, (if k ≠ 0 then g (supp k).card * ∏ j, ρ (k j) else 0)
      = ∑ s : Finset (Fin m), (if s.card ≠ 0 then g s.card else 0)
          * (if supp k = s then ∏ j, ρ (k j) else 0) := by
    intro k
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq univ (supp k), if_pos (mem_univ _)]
    by_cases hk : k = 0
    · have : (supp k).card = 0 := by rw [card_eq_zero, supp_eq_empty_iff]; exact hk
      rw [if_neg (not_not.2 hk), this]
      simp
    · have : (supp k).card ≠ 0 := by
        rw [Ne, card_eq_zero, supp_eq_empty_iff]; exact hk
      simp [hk, this]
  simp_rw [hpt]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp_rw [ENNReal.tsum_mul_left, tsum_supp_eq ρ hρ0 τ hτ]
  rw [← Finset.powerset_univ,
    Finset.sum_powerset_apply_card (fun n => (if n ≠ 0 then g n else 0) * τ ^ n),
    card_univ, Fintype.card_fin]
  have hsub : Icc 1 m ⊆ range (m + 1) := by
    intro v hv; simp only [mem_Icc] at hv; simp only [mem_range]; omega
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun v hv => ?_
    have hv0 : v ≠ 0 := by simp only [mem_Icc] at hv; omega
    rw [if_pos hv0, nsmul_eq_mul]
    ring
  · intro v hv hv'
    have : v = 0 := by simp only [mem_Icc, mem_range] at hv hv'; omega
    simp [this]

/-- Total of `S(A)` over all `0/1` matrices, multiplied out. -/
theorem sum_S_le_binary_mul (ρ : ℤ → ℝ≥0∞) (hρ0 : ρ 0 = 1) (τ : ℝ≥0∞)
    (hτ : ∑' z, (if z = 0 then 0 else ρ z) = τ) :
    ∑ A : Fin m → Fin T → Fin 2, S ρ A
      ≤ 2 ^ (m * T) * ∑ v ∈ Icc 1 m, (m.choose v : ℝ≥0∞) * τ ^ v * q v ^ T := by
  rw [sum_S, ← tsum_group_supp ρ hρ0 τ hτ (fun v => q v ^ T), ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases hk : k ≠ 0
  · rw [if_pos hk, if_pos hk]
    calc ((univ.filter fun A : Fin m → Fin T → Fin 2 => InKer A k).card : ℝ≥0∞) * ∏ j, ρ (k j)
        ≤ (2 ^ (m * T) * q (supp k).card ^ T) * ∏ j, ρ (k j) := by
          gcongr; exact card_inKer_two_le k
      _ = 2 ^ (m * T) * (q (supp k).card ^ T * ∏ j, ρ (k j)) := by ring
  · simp [hk]

/-- **Average of `S(A)`, entries in `{0, 1}`.** The mean of `S(A)` over all matrices
`A ∈ {0,1}^(m × T)` is at most `∑_{v=1}^m C(m,v) τ^v q(v)^T` with `q(v) = C(v, ⌊v/2⌋) / 2^v`. -/
theorem avg_S_le_binary (ρ : ℤ → ℝ≥0∞) (hρ0 : ρ 0 = 1) (τ : ℝ≥0∞)
    (hτ : ∑' z, (if z = 0 then 0 else ρ z) = τ) :
    (∑ A : Fin m → Fin T → Fin 2, S ρ A) / (Fintype.card (Fin m → Fin T → Fin 2) : ℝ≥0∞)
      ≤ ∑ v ∈ Icc 1 m, (m.choose v : ℝ≥0∞) * τ ^ v * q v ^ T := by
  refine ENNReal.div_le_of_le_mul ?_
  rw [card_matrices (M := 1), mul_comm]
  push_cast
  exact sum_S_le_binary_mul ρ hρ0 τ hτ

/-- **Existence, entries in `{0, 1}`.** If `∑_{v=1}^m C(m,v) τ^v q(v)^T < 1`, some matrix
`A ∈ {0,1}^(m × T)` has `S(A) < 1`. -/
theorem exists_S_lt_one_binary (ρ : ℤ → ℝ≥0∞) (hρ0 : ρ 0 = 1) (τ : ℝ≥0∞)
    (hτ : ∑' z, (if z = 0 then 0 else ρ z) = τ)
    (hlt : ∑ v ∈ Icc 1 m, (m.choose v : ℝ≥0∞) * τ ^ v * q v ^ T < 1) :
    ∃ A : Fin m → Fin T → Fin 2, S ρ A < 1 := by
  refine exists_lt_one_of_sum_le _ _ hlt ?_
  rw [card_matrices (M := 1)]
  push_cast
  exact sum_S_le_binary_mul ρ hρ0 τ hτ

end

end QNNShatter
