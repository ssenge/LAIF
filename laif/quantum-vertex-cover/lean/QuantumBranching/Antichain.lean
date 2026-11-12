import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Antichains and macro steps

`card_le_of_sum_le` is the count behind the size of a tree: a family of total weight at most
`K * B0`, whose members all weigh more than `B0 * exp (-δ)`, has at most `K * exp δ` members.

`FinTree` is a finite rooted tree given by parent pointers and depths. A macro decomposition is a set
`R` of nodes that contains the root. The macro root `macroRoot R a` of a node `a` is its nearest
ancestor in `R`, and the boundary of `r ∈ R` is the set of the other members of `R` whose parent has
macro root `r`. All of this is computed from `R`.

`lemma0` is Lemma 0: under the local inequality over boundaries, every antichain has sum of `B` at
most `(D + 1) * s * K * B root`. The proof sums over macro depth, through `sum_level_le`. It never uses
the antichain property, and `macro_sum_le` states the bound for every set of nodes.
-/

open Finset

namespace QuantumBranching

section Count

variable {α : Type*}

/-- The count from a weight bound. -/
theorem card_le_of_sum_le (X : Finset α) (B : α → ℝ) {K B0 δ : ℝ} (hB0 : 0 < B0)
    (hsum : ∑ a ∈ X, B a ≤ K * B0) (hlow : ∀ a ∈ X, B0 * Real.exp (-δ) < B a) :
    (X.card : ℝ) ≤ K * Real.exp δ := by
  have h1 : (X.card : ℝ) * (B0 * Real.exp (-δ)) ≤ ∑ a ∈ X, B a := by
    have := Finset.card_nsmul_le_sum X B (B0 * Real.exp (-δ)) (fun a ha => (hlow a ha).le)
    simpa [nsmul_eq_mul] using this
  have h2 : (X.card : ℝ) * Real.exp (-δ) ≤ K := by
    have : (X.card : ℝ) * Real.exp (-δ) * B0 ≤ K * B0 := by nlinarith
    exact le_of_mul_le_mul_right this hB0
  have h3 : Real.exp (-δ) * Real.exp δ = 1 := by rw [← Real.exp_add]; simp
  calc (X.card : ℝ) = (X.card : ℝ) * (Real.exp (-δ) * Real.exp δ) := by rw [h3, mul_one]
    _ = (X.card : ℝ) * Real.exp (-δ) * Real.exp δ := by ring
    _ ≤ K * Real.exp δ := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le

/-- The strict form, for a nonempty family. -/
theorem card_lt_of_sum_le (X : Finset α) (B : α → ℝ) {K B0 δ : ℝ} (hB0 : 0 < B0)
    (hne : X.Nonempty) (hsum : ∑ a ∈ X, B a ≤ K * B0)
    (hlow : ∀ a ∈ X, B0 * Real.exp (-δ) < B a) :
    (X.card : ℝ) < K * Real.exp δ := by
  have h1 : (X.card : ℝ) * (B0 * Real.exp (-δ)) < ∑ a ∈ X, B a := by
    have := Finset.sum_lt_sum_of_nonempty hne hlow
    simpa [nsmul_eq_mul] using this
  have h2 : (X.card : ℝ) * Real.exp (-δ) < K := by
    have : (X.card : ℝ) * Real.exp (-δ) * B0 < K * B0 := by nlinarith
    exact lt_of_mul_lt_mul_right this hB0.le
  have h3 : Real.exp (-δ) * Real.exp δ = 1 := by rw [← Real.exp_add]; simp
  calc (X.card : ℝ) = (X.card : ℝ) * (Real.exp (-δ) * Real.exp δ) := by rw [h3, mul_one]
    _ = (X.card : ℝ) * Real.exp (-δ) * Real.exp δ := by ring
    _ < K * Real.exp δ := mul_lt_mul_of_pos_right h2 (Real.exp_pos _)

/-- The strict form, for a positive constant. An empty family has no strict bound when `K = 0`. -/
theorem card_lt_of_sum_le_of_pos (X : Finset α) (B : α → ℝ) {K B0 δ : ℝ} (hB0 : 0 < B0) (hK : 0 < K)
    (hsum : ∑ a ∈ X, B a ≤ K * B0) (hlow : ∀ a ∈ X, B0 * Real.exp (-δ) < B a) :
    (X.card : ℝ) < K * Real.exp δ := by
  rcases X.eq_empty_or_nonempty with rfl | hne
  · simpa using mul_pos hK (Real.exp_pos δ)
  · exact card_lt_of_sum_le X B hB0 hne hsum hlow

end Count

/-- A finite rooted tree, by parent pointers and depths. The parent of the root is the root. -/
structure FinTree (α : Type*) where
  /-- The nodes. -/
  nodes : Finset α
  /-- The root. -/
  root : α
  /-- The parent of a node. -/
  parent : α → α
  /-- The depth of a node. -/
  depth : α → ℕ
  root_mem : root ∈ nodes
  parent_mem : ∀ a ∈ nodes, parent a ∈ nodes
  parent_root : parent root = root
  depth_root : depth root = 0
  depth_parent : ∀ a ∈ nodes, a ≠ root → depth a = depth (parent a) + 1

namespace FinTree

variable {α : Type*} (T : FinTree α)

/-- `a` is an ancestor of `b`, or `b` itself. -/
def Anc (a b : α) : Prop := ∃ k : ℕ, T.parent^[k] b = a

/-- A set of nodes with no node a proper ancestor of another. -/
def IsAntichain (X : Finset α) : Prop := ∀ a ∈ X, ∀ b ∈ X, T.Anc a b → a = b

theorem eq_root_of_depth_eq_zero {a : α} (ha : a ∈ T.nodes) (h : T.depth a = 0) : a = T.root := by
  by_contra hne
  have := T.depth_parent a ha hne
  omega

theorem iterate_mem {b : α} (hb : b ∈ T.nodes) (k : ℕ) : T.parent^[k] b ∈ T.nodes := by
  induction k with
  | zero => simpa using hb
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact T.parent_mem _ ih

/-- Going up `k` steps lowers the depth by `k`, down to zero. -/
theorem depth_iterate {b : α} (hb : b ∈ T.nodes) (k : ℕ) :
    T.depth (T.parent^[k] b) = T.depth b - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hm := T.iterate_mem hb k
    by_cases hr : T.parent^[k] b = T.root
    · rw [hr, T.parent_root, T.depth_root]
      rw [hr, T.depth_root] at ih
      omega
    · have := T.depth_parent _ hm hr
      omega

/-- Nodes at one depth form an antichain. -/
theorem isAntichain_of_depth (X : Finset α) (hX : X ⊆ T.nodes) (j : ℕ)
    (hd : ∀ a ∈ X, T.depth a = j) : T.IsAntichain X := by
  rintro a ha b hb ⟨k, rfl⟩
  have hbn := hX hb
  have h1 := T.depth_iterate hbn k
  rw [hd _ ha, hd _ hb] at h1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hj : j = 0 := by omega
    have hbr := T.eq_root_of_depth_eq_zero hbn (by rw [hd _ hb, hj])
    subst hbr
    have : ∀ m, T.parent^[m] T.root = T.root := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Function.iterate_succ_apply', ih, T.parent_root]
    exact this k

variable [DecidableEq α] (R : Finset α)

/-- Going up at most `k` steps to the first node of `R`. -/
def rootSearch : ℕ → α → α
  | 0, a => a
  | k + 1, a => if a ∈ R then a else rootSearch k (T.parent a)

/-- The nearest ancestor of `a` in `R`, or `a` itself if `a ∈ R`. -/
def macroRoot (a : α) : α := T.rootSearch R (T.depth a) a

/-- The boundary of the macro step of `r`: the other members of `R` whose parent lies in that step. -/
def boundary (r : α) : Finset α :=
  R.filter fun c => c ≠ T.root ∧ T.macroRoot R (T.parent c) = r

/-- The members of `R` at macro depth `j`. -/
def level : ℕ → Finset α
  | 0 => {T.root}
  | j + 1 => R.filter fun c => c ≠ T.root ∧ T.macroRoot R (T.parent c) ∈ level j

variable {R}

theorem macroRoot_of_mem {a : α} (ha : a ∈ R) : T.macroRoot R a = a := by
  unfold macroRoot
  cases T.depth a with
  | zero => rfl
  | succ k => simp [rootSearch, ha]

theorem macroRoot_of_not_mem (hroot : T.root ∈ R) {a : α} (han : a ∈ T.nodes) (ha : a ∉ R) :
    T.macroRoot R a = T.macroRoot R (T.parent a) := by
  have hne : a ≠ T.root := fun h => ha (h ▸ hroot)
  have hd := T.depth_parent a han hne
  unfold macroRoot
  rw [hd]
  simp [rootSearch, ha]

theorem macroRoot_spec (hroot : T.root ∈ R) (k : ℕ) :
    ∀ a ∈ T.nodes, T.depth a = k →
      T.macroRoot R a ∈ R ∧ T.depth (T.macroRoot R a) ≤ T.depth a := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro a han hk
    by_cases ha : a ∈ R
    · rw [T.macroRoot_of_mem ha]
      exact ⟨ha, le_rfl⟩
    · have hne : a ≠ T.root := fun h => ha (h ▸ hroot)
      have hd := T.depth_parent a han hne
      rw [T.macroRoot_of_not_mem hroot han ha]
      obtain ⟨h1, h2⟩ := ih (T.depth (T.parent a)) (by omega) _ (T.parent_mem a han) rfl
      exact ⟨h1, by omega⟩

theorem macroRoot_mem (hroot : T.root ∈ R) {a : α} (ha : a ∈ T.nodes) : T.macroRoot R a ∈ R :=
  (T.macroRoot_spec hroot _ a ha rfl).1

theorem level_subset (hroot : T.root ∈ R) (j : ℕ) : T.level R j ⊆ R := by
  cases j with
  | zero => simpa [level] using hroot
  | succ j => exact Finset.filter_subset _ _

/-- Every member of `R` has a macro depth, at most its depth in the tree. -/
theorem exists_level (hroot : T.root ∈ R) (hR : R ⊆ T.nodes) (k : ℕ) :
    ∀ r ∈ R, T.depth r = k → ∃ j ≤ k, r ∈ T.level R j := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro r hr hk
    by_cases hrt : r = T.root
    · exact ⟨0, Nat.zero_le _, by simp [level, hrt]⟩
    · have hrn := hR hr
      have hd := T.depth_parent r hrn hrt
      have hpn := T.parent_mem r hrn
      obtain ⟨hm, hle⟩ := T.macroRoot_spec hroot _ _ hpn rfl
      obtain ⟨j, hj, hjm⟩ := ih (T.depth (T.macroRoot R (T.parent r))) (by omega) _ hm rfl
      refine ⟨j + 1, by omega, ?_⟩
      simp only [level, Finset.mem_filter]
      exact ⟨hr, hrt, hjm⟩

/-- The hypotheses of Lemma 0, for the decomposition given by `R`. -/
structure MacroSteps (B : α → ℝ) (s : ℕ) (K : ℝ) (R : Finset α) : Prop where
  root_mem : T.root ∈ R
  subset : R ⊆ T.nodes
  B_nonneg : ∀ a ∈ T.nodes, 0 ≤ B a
  K_nonneg : 0 ≤ K
  /-- Each macro step has at most `s` nodes. -/
  card_le : ∀ r ∈ R, (T.nodes.filter fun a => T.macroRoot R a = r).card ≤ s
  /-- Each node of a macro step has `B a ≤ K * B r`. -/
  le_root : ∀ a ∈ T.nodes, B a ≤ K * B (T.macroRoot R a)
  /-- The local inequality over the boundary. -/
  local_le : ∀ r ∈ R, ∑ c ∈ T.boundary R r, B c ≤ B r

variable {B : α → ℝ} {s : ℕ} {K : ℝ}

/-- The roots at a fixed macro depth have sum of `B` at most `B root`. -/
theorem sum_level_le (h : T.MacroSteps B s K R) (j : ℕ) :
    ∑ r ∈ T.level R j, B r ≤ B T.root := by
  induction j with
  | zero => simp [level]
  | succ j ih =>
    have hmaps : ∀ c ∈ T.level R (j + 1), T.macroRoot R (T.parent c) ∈ T.level R j := by
      intro c hc
      simp only [level, Finset.mem_filter] at hc
      exact hc.2.2
    have hfib := Finset.sum_fiberwise_of_maps_to hmaps B
    rw [← hfib]
    refine le_trans (Finset.sum_le_sum fun p hp => ?_) ih
    have hpR := T.level_subset h.root_mem j hp
    have heq : (T.level R (j + 1)).filter (fun c => T.macroRoot R (T.parent c) = p)
        = T.boundary R p := by
      ext c
      simp only [level, boundary, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hc, hne, _⟩, he⟩
        exact ⟨hc, hne, he⟩
      · rintro ⟨hc, hne, he⟩
        exact ⟨⟨hc, hne, he ▸ hp⟩, he⟩
    rw [heq]
    exact h.local_le p hpR

/-- The contribution of one macro depth. -/
theorem sum_filter_level_le (h : T.MacroSteps B s K R) {X : Finset α} (hX : X ⊆ T.nodes) (j : ℕ) :
    ∑ a ∈ X.filter (fun a => T.macroRoot R a ∈ T.level R j), B a ≤ s * K * B T.root := by
  have hmaps : ∀ a ∈ X.filter (fun a => T.macroRoot R a ∈ T.level R j),
      T.macroRoot R a ∈ T.level R j := fun a ha => (Finset.mem_filter.mp ha).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps B]
  have hroot0 : 0 ≤ B T.root := h.B_nonneg _ T.root_mem
  have hone : ∀ r ∈ T.level R j,
      ∑ a ∈ (X.filter (fun a => T.macroRoot R a ∈ T.level R j)).filter
        (fun a => T.macroRoot R a = r), B a ≤ s * K * B r := by
    intro r hr
    have hrR := T.level_subset h.root_mem j hr
    have hrn := h.subset hrR
    have hval : ∀ a ∈ (X.filter (fun a => T.macroRoot R a ∈ T.level R j)).filter
        (fun a => T.macroRoot R a = r), B a ≤ K * B r := by
      intro a ha
      have ha' := Finset.mem_filter.mp ha
      have hax := (Finset.mem_filter.mp ha'.1).1
      rw [← ha'.2]
      exact h.le_root a (hX hax)
    have hcard : ((X.filter (fun a => T.macroRoot R a ∈ T.level R j)).filter
        (fun a => T.macroRoot R a = r)).card ≤ s := by
      refine le_trans (Finset.card_le_card ?_) (h.card_le r hrR)
      intro a ha
      have ha' := Finset.mem_filter.mp ha
      have hax := (Finset.mem_filter.mp ha'.1).1
      exact Finset.mem_filter.mpr ⟨hX hax, ha'.2⟩
    have hsum := Finset.sum_le_card_nsmul _ _ _ hval
    have hKB : 0 ≤ K * B r := mul_nonneg h.K_nonneg (h.B_nonneg r hrn)
    rw [nsmul_eq_mul] at hsum
    have hc : (((X.filter (fun a => T.macroRoot R a ∈ T.level R j)).filter
        (fun a => T.macroRoot R a = r)).card : ℝ) ≤ s := by exact_mod_cast hcard
    nlinarith [mul_le_mul_of_nonneg_right hc hKB]
  refine le_trans (Finset.sum_le_sum hone) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (T.sum_level_le h j)
    (mul_nonneg (Nat.cast_nonneg _) h.K_nonneg)

/-- The sum over any set of nodes, by macro depth. -/
theorem macro_sum_le (h : T.MacroSteps B s K R) {D : ℕ} (hD : ∀ a ∈ T.nodes, T.depth a ≤ D)
    {X : Finset α} (hX : X ⊆ T.nodes) :
    ∑ a ∈ X, B a ≤ ((D : ℝ) + 1) * s * K * B T.root := by
  have hone : ∀ a ∈ X, B a ≤ ∑ j ∈ Finset.range (D + 1),
      if T.macroRoot R a ∈ T.level R j then B a else 0 := by
    intro a ha
    have han := hX ha
    have hm := T.macroRoot_mem h.root_mem han
    obtain ⟨j, hj, hjm⟩ := T.exists_level h.root_mem h.subset _ _ hm rfl
    have hle : j ≤ D := le_trans hj (hD _ (h.subset hm))
    have hnn : ∀ i ∈ Finset.range (D + 1), 0 ≤ if T.macroRoot R a ∈ T.level R i then B a else 0 := by
      intro i _
      split_ifs
      · exact h.B_nonneg a han
      · exact le_rfl
    have := Finset.single_le_sum hnn (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
    simpa [hjm] using this
  calc ∑ a ∈ X, B a
      ≤ ∑ a ∈ X, ∑ j ∈ Finset.range (D + 1), if T.macroRoot R a ∈ T.level R j then B a else 0 :=
        Finset.sum_le_sum hone
    _ = ∑ j ∈ Finset.range (D + 1), ∑ a ∈ X.filter (fun a => T.macroRoot R a ∈ T.level R j), B a := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_filter]
    _ ≤ ∑ _j ∈ Finset.range (D + 1), (s : ℝ) * K * B T.root :=
        Finset.sum_le_sum fun j _ => T.sum_filter_level_le h hX j
    _ = ((D : ℝ) + 1) * s * K * B T.root := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring

/-- **Lemma 0.** A macro decomposition gives the antichain bound with constant `(D + 1) * s * K`. -/
theorem lemma0 (h : T.MacroSteps B s K R) {D : ℕ} (hD : ∀ a ∈ T.nodes, T.depth a ≤ D)
    {X : Finset α} (hX : X ⊆ T.nodes) (_hanti : T.IsAntichain X) :
    ∑ a ∈ X, B a ≤ ((D : ℝ) + 1) * s * K * B T.root :=
  T.macro_sum_le h hD hX

omit [DecidableEq α] in
/-- A set of nodes that all weigh more than `B0 * exp (-δ)` has at most `(D + 1) * K * exp δ` members,
when antichains have sum at most `K * B0`: split by depth. -/
theorem card_le_of_antichain_bound {B0 δ : ℝ} (hB0 : 0 < B0) {D : ℕ}
    (hD : ∀ a ∈ T.nodes, T.depth a ≤ D)
    (hM1 : ∀ X ⊆ T.nodes, T.IsAntichain X → ∑ a ∈ X, B a ≤ K * B0)
    {X : Finset α} (hX : X ⊆ T.nodes) (hlow : ∀ a ∈ X, B0 * Real.exp (-δ) < B a) :
    (X.card : ℝ) ≤ ((D : ℝ) + 1) * (K * Real.exp δ) := by
  have hmaps : ∀ a ∈ X, T.depth a ∈ Finset.range (D + 1) := fun a ha =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hD a (hX ha)))
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hone : ∀ j ∈ Finset.range (D + 1),
      (((X.filter fun a => T.depth a = j).card : ℕ) : ℝ) ≤ K * Real.exp δ := by
    intro j _
    have hsub : (X.filter fun a => T.depth a = j) ⊆ T.nodes :=
      (Finset.filter_subset _ _).trans hX
    refine card_le_of_sum_le _ B hB0
      (hM1 _ hsub (T.isAntichain_of_depth _ hsub j fun a ha => (Finset.mem_filter.mp ha).2)) ?_
    exact fun a ha => hlow a (Finset.mem_filter.mp ha).1
  calc (X.card : ℝ) = ∑ j ∈ Finset.range (D + 1), ((X.filter fun a => T.depth a = j).card : ℝ) := by
        rw [hcard]; push_cast; rfl
    _ ≤ ∑ _j ∈ Finset.range (D + 1), K * Real.exp δ := Finset.sum_le_sum hone
    _ = ((D : ℝ) + 1) * (K * Real.exp δ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

end FinTree

end QuantumBranching
