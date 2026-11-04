import Covers.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases

/-!
# Deterministic sampling: Lemma 3 and the sampling process of Section 2

A **column** is a pair `(x, c)`. Alignment `a` **survives** a list of columns if `P[x - a] = c` for all of them, with
`x - a` in range.

* `IsSample` is the abstract situation of Lemma 3: a survivor `s`, and a column killing every other alignment in
  `[0, w)` **at a position that is in range for it**.
* `vishkin_exclusion`, `two_extremes`, `two_extremes_block` are Lemma 3 and its consequence.
* `IsPhase` is the process of the notes: each new column lies in the overlap of the current extreme survivors, and its
  character is that of one of the two. `IsPhase.isSample` shows the process produces an `IsSample`. This is the part of
  the proof of Lemma 3 that says "`x - a` is in range or `a` was removed earlier for that reason".

## Out-of-range conventions

`Survives` asks for `a ≤ x` and `P[x - a]? = some c`, so an alignment out of range at a column does not survive it. The
`kills` field of `IsSample` then has to say in-range explicitly, since a kill out of range does not exclude an
occurrence.
-/

namespace Strings

variable {α : Type*}

/-- Alignment `a` of `P` agrees with all the columns. -/
def Survives (P : List α) (cols : List (ℕ × α)) (a : ℕ) : Prop :=
  ∀ col ∈ cols, a ≤ col.1 ∧ P[col.1 - a]? = some col.2

/-- Text position `t` passes the sample with survivor `s`: `S[t + x - s] = c` for all columns. -/
def Passes (S : List α) (t s : ℕ) (cols : List (ℕ × α)) : Prop :=
  ∀ col ∈ cols, S[t + col.1 - s]? = some col.2

/-- A sample for `P` on the alignments `[0, w)` with the single survivor `s`. -/
structure IsSample (P : List α) (w s : ℕ) (cols : List (ℕ × α)) : Prop where
  s_lt : s < w
  survives : Survives P cols s
  kills : ∀ a, a < w → a ≠ s → ∃ col ∈ cols, a ≤ col.1 ∧ col.1 - a < P.length ∧ P[col.1 - a]? ≠ some col.2

/-- **Lemma 3 (Vishkin exclusion).** If position `t` passes the sample, then no `t' ≠ t` with `t' + s ∈ [t, t + w)`
is an occurrence of `P`. In the notation of the notes, `t' ∈ [t - s, t - s + w)`. -/
theorem vishkin_exclusion {P S : List α} {w s t t' : ℕ} {cols : List (ℕ × α)} (hs : IsSample P w s cols)
    (hp : Passes S t s cols) (h₁ : t ≤ t' + s) (h₂ : t' + s < t + w) (hne : t' ≠ t) :
    ¬ OccursAt P S t' := by
  intro hocc
  obtain ⟨col, hcol, hax, hlt, hbad⟩ := hs.kills (t' + s - t) (by omega) (by omega)
  have hsx := (hs.survives col hcol).1
  have h1 := hocc.2 _ hlt
  have hidx : t' + (col.1 - (t' + s - t)) = t + col.1 - s := by omega
  rw [hidx, hp col hcol] at h1
  exact hbad h1.symm

/-- An occurrence of `P` passes every sample of `P`. -/
theorem OccursAt.passes {P S : List α} {w s y : ℕ} {cols : List (ℕ × α)} (hs : IsSample P w s cols)
    (hocc : OccursAt P S y) : Passes S y s cols := by
  intro col hcol
  obtain ⟨hsx, hc⟩ := hs.survives col hcol
  have hlt : col.1 - s < P.length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hc
    simp at hc
  have h1 := hocc.2 _ hlt
  rw [hc] at h1
  have hidx : y + (col.1 - s) = y + col.1 - s := by omega
  rwa [hidx] at h1

/-- **Lemma 3, the two extremes.** If `t₁ ≤ y ≤ t₂` all lie within fewer than `w` positions, `t₁, t₂` pass the sample
and `y` is an occurrence of `P`, then `y` is `t₁` or `t₂`. -/
theorem two_extremes {P S : List α} {w s t₁ t₂ y : ℕ} {cols : List (ℕ × α)} (hs : IsSample P w s cols)
    (h₁ : Passes S t₁ s cols) (h₂ : Passes S t₂ s cols) (hw : t₂ < t₁ + w) (hy₁ : t₁ ≤ y) (hy₂ : y ≤ t₂)
    (hocc : OccursAt P S y) : y = t₁ ∨ y = t₂ := by
  have hsw := hs.s_lt
  by_contra hne
  rw [not_or] at hne
  by_cases hin : y + s < t₁ + w
  · exact vishkin_exclusion hs h₁ (by omega) hin hne.1 hocc
  · exact vishkin_exclusion hs h₂ (by omega) (by omega) hne.2 hocc

/-- **Lemma 3, in a block.** In a set of starts of diameter less than `w`, only the leftmost and rightmost starts
that pass the sample can be occurrences. -/
theorem two_extremes_block {P S : List α} {w s t₁ t₂ y : ℕ} {cols : List (ℕ × α)} {B : Set ℕ}
    (hs : IsSample P w s cols) (hB : ∀ a ∈ B, ∀ b ∈ B, b < a + w)
    (h₁ : IsLeast {t | t ∈ B ∧ Passes S t s cols} t₁) (h₂ : IsGreatest {t | t ∈ B ∧ Passes S t s cols} t₂)
    (hy : y ∈ B) (hocc : OccursAt P S y) : y = t₁ ∨ y = t₂ :=
  have hmem : y ∈ {t | t ∈ B ∧ Passes S t s cols} := ⟨hy, hocc.passes hs⟩
  two_extremes hs h₁.1.2 h₂.1.2 (hB _ h₁.1.1 _ h₂.1.1) (h₁.2 hmem) (h₂.2 hmem) hocc

/-! ## The process -/

/-- `a` is the lowest surviving alignment in `[0, w)`. -/
def IsLow (P : List α) (w : ℕ) (cols : List (ℕ × α)) (a : ℕ) : Prop :=
  a < w ∧ Survives P cols a ∧ ∀ e, e < w → Survives P cols e → a ≤ e

/-- `b` is the highest surviving alignment in `[0, w)`. -/
def IsHigh (P : List α) (w : ℕ) (cols : List (ℕ × α)) (b : ℕ) : Prop :=
  b < w ∧ Survives P cols b ∧ ∀ e, e < w → Survives P cols e → e ≤ b

/-- One phase of the sampling of Section 2, on the alignments `[0, w)`. Given the extreme survivors `a < b`, a column is
appended at a position `x` of their overlap `[b, a + ℓ)` where they differ, with the character of `a` or `b`. -/
inductive IsPhase (P : List α) (w : ℕ) : List (ℕ × α) → Prop
  | nil : IsPhase P w []
  | step {cols : List (ℕ × α)} {a b x : ℕ} {c : α} :
      IsPhase P w cols → IsLow P w cols a → IsHigh P w cols b → a < b → b ≤ x → x < a + P.length →
      P[x - a]? ≠ P[x - b]? → (P[x - a]? = some c ∨ P[x - b]? = some c) → IsPhase P w (cols ++ [(x, c)])

theorem survives_append {P : List α} {cols : List (ℕ × α)} {a x : ℕ} {c : α} :
    Survives P (cols ++ [(x, c)]) a ↔ Survives P cols a ∧ a ≤ x ∧ P[x - a]? = some c := by
  simp only [Survives, List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
  tauto

/-- Every survivor is defined at a column in the overlap of the extremes. -/
theorem survivor_defined {ℓ a b e x : ℕ} (hae : a ≤ e) (heb : e ≤ b) (hb : b ≤ x) (hx : x < a + ℓ) :
    e ≤ x ∧ x - e < ℓ := by omega

/-- A phase has an invariant: each alignment still survives, or it was killed **in range**. -/
theorem IsPhase.survives_or_killed {P : List α} {w : ℕ} {cols : List (ℕ × α)} (h : IsPhase P w cols) :
    ∀ e, e < w → Survives P cols e ∨
      ∃ col ∈ cols, e ≤ col.1 ∧ col.1 - e < P.length ∧ P[col.1 - e]? ≠ some col.2 := by
  induction h with
  | nil => exact fun e _ => Or.inl (by simp [Survives])
  | @step cols a b x c _ hlo hhi _ hbx hxa _ _ ih =>
    intro e he
    rcases ih e he with hs | ⟨col, hcol, h1, h2, h3⟩
    · have hd := survivor_defined (hlo.2.2 e he hs) (hhi.2.2 e he hs) hbx hxa
      by_cases hc : P[x - e]? = some c
      · exact Or.inl (survives_append.2 ⟨hs, hd.1, hc⟩)
      · exact Or.inr ⟨(x, c), by simp, hd.1, hd.2, hc⟩
    · exact Or.inr ⟨col, by simp [hcol], h1, h2, h3⟩

/-- **The process produces a sample.** If a phase ends with the single survivor `s`, the abstract hypotheses of Lemma 3
hold. -/
theorem IsPhase.isSample {P : List α} {w s : ℕ} {cols : List (ℕ × α)} (h : IsPhase P w cols) (hsw : s < w)
    (hs : Survives P cols s) (huniq : ∀ a, a < w → Survives P cols a → a = s) : IsSample P w s cols where
  s_lt := hsw
  survives := hs
  kills a ha hne := by
    rcases h.survives_or_killed a ha with hsv | hk
    · exact absurd (huniq a ha hsv) hne
    · exact hk

/-- `IsPhase` and `IsSample` are not vacuous: `P = 011` with `w = 2`. The extremes `0, 1` differ at column `1`, and taking
the character of alignment `1` leaves alignment `1` alone. -/
theorem isSample_example : IsSample [false, true, true] 2 1 [(1, false)] := by
  have hlo : IsLow [false, true, true] 2 [] 0 := ⟨by norm_num, by simp [Survives], fun e _ _ => Nat.zero_le e⟩
  have hhi : IsHigh [false, true, true] 2 [] 1 := ⟨by norm_num, by simp [Survives], fun e he _ => by omega⟩
  have hp : IsPhase [false, true, true] 2 [(1, false)] :=
    IsPhase.step (cols := []) (a := 0) (b := 1) (x := 1) (c := false) IsPhase.nil hlo hhi (by norm_num) le_rfl
      (by simp) (by simp) (Or.inr (by simp))
  refine hp.isSample (by norm_num) (by simp [Survives]) ?_
  intro a ha hs
  have h1 := hs (1, false) (by simp)
  interval_cases a
  · simp at h1
  · rfl

/-- **Agreement on the whole overlap gives a period.** This is the restart step of Section 2. -/
theorem period_of_agree {P : List α} {a b : ℕ} (hab : a < b)
    (h : ∀ x, b ≤ x → x < a + P.length → P[x - a]? = P[x - b]?) :
    P.HasPeriod (b - a) := by
  rw [List.hasPeriod_iff_getElem?]
  intro i hi
  have := h (i + b) (by omega) (by omega)
  have e1 : i + b - a = i + (b - a) := by omega
  have e2 : i + b - b = i := by omega
  rw [e1, e2] at this
  exact this.symm

/-- **Halving.** At a column where the extremes have characters `c₁ ≠ c₂`, the two classes of survivors are disjoint,
so one of them has at most half the survivors. With a fair choice between the two characters, the survivors therefore
halve with probability at least `1/2`. -/
theorem smaller_class_le_half {P : List α} [DecidableEq α] (T : Finset ℕ) (x : ℕ) {c₁ c₂ : α} (hne : c₁ ≠ c₂) :
    2 * (T.filter fun a => P[x - a]? = some c₁).card ≤ T.card ∨
      2 * (T.filter fun a => P[x - a]? = some c₂).card ≤ T.card := by
  have hdisj : Disjoint (T.filter fun a => P[x - a]? = some c₁) (T.filter fun a => P[x - a]? = some c₂) := by
    rw [Finset.disjoint_filter]
    intro a _ h1 h2
    rw [h1] at h2
    exact hne (Option.some.inj h2)
  have hcard := Finset.card_union_of_disjoint hdisj
  have hle : ((T.filter fun a => P[x - a]? = some c₁) ∪ (T.filter fun a => P[x - a]? = some c₂)).card ≤ T.card :=
    Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  omega

end Strings
