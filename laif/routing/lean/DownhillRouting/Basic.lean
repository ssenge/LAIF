import Mathlib

/-!
# Downhill split routing

A node splits its traffic for one destination over a set of next nodes. The relation `R v w` says that `v` sends a
positive share to `w`.

* `noLoop_of_downhill`: if every split goes to a node with a strictly smaller distance, no route returns to a node
  it has visited, and on a finite node set every route ends (`wellFounded_of_downhill`).
* `noLoop_twoLevel`: the two-level rule. A node with an exact distance sends only to nodes with an exact and
  strictly smaller one; a node without sends only to nodes with a strictly smaller cell distance.
* `prune`: dropping the shares below a threshold `t` and renormalizing gives shares that sum to one, are zero or at
  least `t`, and are positive only where the original share was, whenever `N * t ≤ 1` for `N` successors.
* `dist_sub_le`: if every advertised link value is within `ε` of the true one, every path value is within
  `ε` times its number of links, and so is the least value over any finite set of paths of at most `h` links.
-/

namespace DownhillRouting

section Loops

variable {V : Type*} (R : V → V → Prop)

/-- Along any route of positive splits the potential strictly decreases. -/
theorem potential_lt_of_transGen {α : Type*} [Preorder α] (φ : V → α) (h : ∀ v w, R v w → φ w < φ v)
    {v w : V} (hvw : Relation.TransGen R v w) : φ w < φ v := by
  induction hvw with
  | single hab => exact h _ _ hab
  | tail _ hbc ih => exact (h _ _ hbc).trans ih

/-- Downhill splits have no loops. -/
theorem noLoop_of_downhill {α : Type*} [Preorder α] (φ : V → α) (h : ∀ v w, R v w → φ w < φ v) (v : V) :
    ¬ Relation.TransGen R v v :=
  fun hv => lt_irrefl _ (potential_lt_of_transGen R φ h hv)

/-- On a finite node set, downhill splits admit no infinite route: the reversed split relation is well founded. -/
theorem wellFounded_of_downhill [Finite V] {α : Type*} [Preorder α] (φ : V → α)
    (h : ∀ v w, R v w → φ w < φ v) : WellFounded (fun w v => R v w) := by
  have hT : WellFounded (fun w v => Relation.TransGen R v w) := by
    have : IsTrans V (fun w v => Relation.TransGen R v w) :=
      ⟨fun a b c hab hbc => Relation.TransGen.trans hbc hab⟩
    have : Std.Irrefl (fun w v => Relation.TransGen R v w) := ⟨fun a ha => noLoop_of_downhill R φ h a ha⟩
    exact Finite.wellFounded_of_trans_of_irrefl _
  exact Subrelation.wf (fun {w v} hR => Relation.TransGen.single hR) hT

/-- The two-level rule is loop-free: `exact v` says that `v` holds an exact distance `Z v` to the destination,
`F` is the distance to the destination's cell. -/
theorem noLoop_twoLevel (exact : V → Prop) (Z F : V → ℝ)
    (hin : ∀ v w, R v w → exact v → exact w ∧ Z w < Z v)
    (hout : ∀ v w, R v w → ¬ exact v → F w < F v) (v : V) : ¬ Relation.TransGen R v v := by
  classical
  -- potential: (0, Z) with an exact distance, (1, F) without, ordered lexicographically
  let φ : V → Lex (ℕ × ℝ) := fun u => if exact u then toLex (0, Z u) else toLex (1, F u)
  refine noLoop_of_downhill R φ (fun a b hab => ?_) v
  by_cases ha : exact a
  · obtain ⟨hb, hz⟩ := hin a b hab ha
    simp only [φ, ha, hb, ite_true]
    exact Prod.Lex.toLex_strictMono (Prod.mk_lt_mk_of_le_of_lt le_rfl hz)
  · have hf := hout a b hab ha
    simp only [φ, ha, ite_false]
    by_cases hb : exact b
    · simp only [hb, ite_true]
      exact Prod.Lex.lt_iff.2 (Or.inl (by norm_num))
    · simp only [hb, ite_false]
      exact Prod.Lex.toLex_strictMono (Prod.mk_lt_mk_of_le_of_lt le_rfl hf)

end Loops

section Prune

variable {N : ℕ}

/-- Shares after pruning below `t`, before renormalization. -/
noncomputable def kept (t : ℝ) (a : Fin N → ℝ) (i : Fin N) : ℝ := if a i < t then 0 else a i

/-- Shares after pruning and renormalization. -/
noncomputable def prune (t : ℝ) (a : Fin N → ℝ) (i : Fin N) : ℝ := kept t a i / ∑ j, kept t a j

/-- If `N * t ≤ 1` and the shares sum to one, some share is at least `t`, so the kept total is positive. -/
theorem kept_sum_pos (t : ℝ) (ht : 0 < t) (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1)
    (hNt : (N : ℝ) * t ≤ 1) : 0 < ∑ j, kept t a j := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hsum
    · exact h
  obtain ⟨i, hi⟩ : ∃ i, t ≤ a i := by
    by_contra hc
    push Not at hc
    have : ∑ i, a i < ∑ _i : Fin N, t :=
      Finset.sum_lt_sum_of_nonempty ⟨⟨0, hN⟩, Finset.mem_univ _⟩ (fun i _ => hc i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  have hk : ∀ j, 0 ≤ kept t a j := fun j => by unfold kept; split_ifs <;> simp [ha j]
  have hpos : 0 < kept t a i := by
    simp only [kept, not_lt.2 hi, ite_false]
    linarith
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun j _ => hk j) (Finset.mem_univ i))

theorem prune_sum (t : ℝ) (ht : 0 < t) (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1)
    (hNt : (N : ℝ) * t ≤ 1) : ∑ i, prune t a i = 1 := by
  unfold prune
  rw [← Finset.sum_div]
  exact div_self (kept_sum_pos t ht a ha hsum hNt).ne'

/-- Every share after pruning is zero or at least the threshold. -/
theorem prune_zero_or_ge (t : ℝ) (ht : 0 < t) (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1)
    (hNt : (N : ℝ) * t ≤ 1) (i : Fin N) : prune t a i = 0 ∨ t ≤ prune t a i := by
  have hS := kept_sum_pos t ht a ha hsum hNt
  have hle : ∑ j, kept t a j ≤ 1 := by
    rw [← hsum]
    exact Finset.sum_le_sum (fun j _ => by unfold kept; split_ifs <;> simp [ha j])
  unfold prune
  by_cases h : a i < t
  · left; simp [kept, h]
  · right
    push Not at h
    have hki : kept t a i = a i := by simp [kept, not_lt.2 h]
    rw [hki, le_div_iff₀ hS]
    calc t * ∑ j, kept t a j ≤ a i * ∑ j, kept t a j := mul_le_mul_of_nonneg_right h hS.le
      _ ≤ a i * 1 := mul_le_mul_of_nonneg_left hle (ha i)
      _ = a i := mul_one _

/-- Pruning sends only where the original split sent: downhill splits stay downhill. -/
theorem prune_pos_imp (t : ℝ) (ht : 0 < t) (a : Fin N → ℝ) (i : Fin N) (h : 0 < prune t a i) : 0 < a i := by
  by_cases hi : a i < t
  · simp [prune, kept, hi] at h
  · push Not at hi
    linarith

end Prune

section Triggered

variable {E : Type*}

/-- Path value: sum of link values along a list of links. -/
def pathValue (c : E → ℝ) (P : List E) : ℝ := (P.map c).sum

/-- Advertised values within `ε` of the true ones change a path value by at most `ε` per link. -/
theorem pathValue_sub_le (c c' : E → ℝ) (ε : ℝ) (hc : ∀ e, |c' e - c e| ≤ ε) (P : List E) :
    |pathValue c' P - pathValue c P| ≤ P.length * ε := by
  induction P with
  | nil => simp [pathValue]
  | cons e P ih =>
    simp only [pathValue, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    calc |c' e + (P.map c').sum - (c e + (P.map c).sum)|
        = |(c' e - c e) + ((P.map c').sum - (P.map c).sum)| := by ring_nf
      _ ≤ |c' e - c e| + |(P.map c').sum - (P.map c).sum| := abs_add_le _ _
      _ ≤ ε + P.length * ε := add_le_add (hc e) ih
      _ = ((P.length + 1 : ℕ) : ℝ) * ε := by push_cast; ring

/-- Least values over a nonempty finite set of paths of at most `h` links differ by at most `h ε`. -/
theorem dist_sub_le (c c' : E → ℝ) (ε : ℝ) (hc : ∀ e, |c' e - c e| ≤ ε) (S : Finset (List E))
    (hS : S.Nonempty) (h : ℕ) (hlen : ∀ P ∈ S, P.length ≤ h) (hε : 0 ≤ ε) :
    |S.inf' hS (pathValue c') - S.inf' hS (pathValue c)| ≤ h * ε := by
  have key : ∀ P ∈ S, |pathValue c' P - pathValue c P| ≤ h * ε := fun P hP =>
    (pathValue_sub_le c c' ε hc P).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen P hP) hε)
  rw [abs_sub_le_iff]
  constructor
  · obtain ⟨P, hP, hPv⟩ := S.exists_mem_eq_inf' hS (pathValue c)
    have h1 : S.inf' hS (pathValue c') ≤ pathValue c' P := Finset.inf'_le _ hP
    have h2 := (abs_sub_le_iff.1 (key P hP)).1
    linarith
  · obtain ⟨P, hP, hPv⟩ := S.exists_mem_eq_inf' hS (pathValue c')
    have h1 : S.inf' hS (pathValue c) ≤ pathValue c P := Finset.inf'_le _ hP
    have h2 := (abs_sub_le_iff.1 (key P hP)).2
    linarith

end Triggered

end DownhillRouting
