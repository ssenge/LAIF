import Covers.Periodic

/-!
# All borders in a range: Section 4

* `border_start_range`, `border_occurs_prefix`: starts of borders in `[L, 2L)` lie in a range of `L` starts, and are
  occurrences of the prefix of length `L`.
* `border_iff_of_run_to_end`: the case `hi = n`.
* `border_start_of_run_break`: the case of a break at `hi < n`.
* `capped_stop_is_not_break`: why a stop at a forward cap below `n` must not be read as a break. The cap `z + ℓ` of the
  occurrence search is below `n` on the lower half of the range, so Section 4 needs the cap to be at least `n`
  (`cap_reaches_end`).

`f` is capped at `min(2L, n)` in the notes. That is the parameter `cap` below, and both theorems ask for `n - t ≤ cap`.

In both cases the start `t` comes from the progression: `S` has period `p` from `t` up to `hi`, and the prefix of length
`ℓ ≥ p` occurs at `t`. The border that starts at `t` is `S.drop t`.
-/

namespace Strings

variable {α : Type*}

/-- `f` is the length of the longest prefix of `S` with period `p`, capped at `cap`, as found by a first-mismatch search. -/
structure IsPeriodicPrefix (S : List α) (p cap f : ℕ) : Prop where
  p_le : p ≤ f
  le : f ≤ cap
  per : PeriodicOn S 0 f p
  stop : f = cap ∨ S[f - p]? ≠ S[f]?

/-- The suffix from `t` is a border iff it matches the prefix, position by position. -/
theorem isBorder_drop_iff {S : List α} {t : ℕ} :
    IsBorder (S.drop t) S ↔ ∀ i, t + i < S.length → S[t + i]? = S[i]? := by
  constructor
  · intro h i hi
    have hlt : i < (S.drop t).length := by rw [List.length_drop]; omega
    rw [List.prefix_iff_getElem?.1 h.1 i hlt, ← List.getElem?_drop]
    exact List.getElem?_eq_getElem hlt
  · intro h
    refine ⟨?_, List.drop_suffix _ _⟩
    rw [List.prefix_iff_getElem?]
    intro i hi
    rw [List.length_drop] at hi
    rw [← h i (by omega), ← List.getElem?_drop]
    exact List.getElem?_eq_getElem (by rw [List.length_drop]; omega)

/-- The starts of borders with length in `[L, 2L)` lie in a range of `L` starts. -/
theorem border_start_range {v S : List α} {L : ℕ} (hb : IsBorder v S) (h₁ : L ≤ v.length) (h₂ : v.length < 2 * L) :
    (S.length - v.length) + L ≤ S.length ∧ S.length < (S.length - v.length) + 2 * L := by
  have := hb.length_le
  omega

/-- A border of length at least `L` starts with an occurrence of the prefix of length `L`. -/
theorem border_occurs_prefix {v S : List α} {L : ℕ} (hb : IsBorder v S) (h₁ : L ≤ v.length) :
    OccursAt (S.take L) S (S.length - v.length) := by
  have hpre : S.take L <+: v := by
    have hle := hb.length_le
    refine List.prefix_of_prefix_length_le (List.take_prefix L S) hb.1 ?_
    rw [List.length_take]
    omega
  have := (occursAt_zero_iff.2 hpre).trans hb.occursAt_end
  simpa using this

/-- **Section 4, the case `hi = n`.** Let `S` have period `p` from `t` to the end, and let the prefix of length `ℓ ≥ p`
occur at `t`. Then `t` starts a border iff `n - t ≤ f`. -/
theorem border_iff_of_run_to_end {S : List α} {t p ℓ cap f : ℕ} (hp0 : 0 < p) (hocc : OccursAt (S.take ℓ) S t)
    (hℓ : p ≤ ℓ) (hℓn : ℓ ≤ S.length) (hrun : PeriodicOn S t S.length p) (hf : IsPeriodicPrefix S p cap f)
    (hcap : S.length - t ≤ cap) :
    IsBorder (S.drop t) S ↔ S.length - t ≤ f := by
  rw [isBorder_drop_iff]
  have htℓ := hocc.1
  rw [List.length_take, min_eq_left hℓn] at htℓ
  constructor
  · intro hb
    by_contra hlt
    have hbad := hf.stop.resolve_left (by omega)
    have hfp := hf.p_le
    have e1 := hb (f - p) (by omega)
    have e2 := hb f (by omega)
    have e3 := hrun (t + (f - p)) (by omega) (by omega)
    have idx : t + (f - p) + p = t + f := by omega
    rw [idx] at e3
    exact hbad (by rw [← e1, e3, e2])
  · intro hle
    have key : ∀ N i, i ≤ N → t + i < S.length → S[t + i]? = S[i]? := by
      intro N
      induction N with
      | zero =>
        intro i hi hl
        have hi0 : i = 0 := by omega
        subst hi0
        have := hocc.2 0 (by rw [List.length_take]; omega)
        rw [this, List.getElem?_take_of_lt (by omega)]
      | succ N ih =>
        intro i hi hl
        by_cases hip : i < p
        · have := hocc.2 i (by rw [List.length_take]; omega)
          rw [this, List.getElem?_take_of_lt (by omega)]
        · have e1 := hrun (t + (i - p)) (by omega) (by omega)
          have idx : t + (i - p) + p = t + i := by omega
          rw [idx] at e1
          have e2 := hf.per (i - p) (Nat.zero_le _) (by omega)
          have idx2 : i - p + p = i := by omega
          rw [idx2] at e2
          rw [← e1, ih (i - p) (by omega) (by omega), e2]
    exact fun i hi => key i i le_rfl hi

/-- **Section 4, the case `hi < n`.** Let `S` have period `p` on `[t, hi)`, with a break at `hi < n`, and `t + p ≤ hi`.
If `t` starts a border, then `t = hi - f`. So at most one start of the progression gives a border. -/
theorem border_start_of_run_break {S : List α} {t p hi cap f : ℕ} (hrun : PeriodicOn S t hi p) (htp : t + p ≤ hi)
    (hhi : hi < S.length) (hbreak : S[hi - p]? ≠ S[hi]?) (hf : IsPeriodicPrefix S p cap f)
    (hcap : S.length - t ≤ cap) (hb : IsBorder (S.drop t) S) : t + f = hi := by
  rw [isBorder_drop_iff] at hb
  have hfp := hf.p_le
  rcases lt_trichotomy (t + f) hi with hlt | heq | hgt
  · -- the prefix breaks earlier than the suffix
    have hbad := hf.stop.resolve_left (by omega)
    have e1 := hb (f - p) (by omega)
    have e2 := hb f (by omega)
    have e3 := hrun (t + (f - p)) (by omega) (by omega)
    have idx : t + (f - p) + p = t + f := by omega
    rw [idx] at e3
    exact absurd (by rw [← e1, e3, e2]) hbad
  · exact heq
  · -- the prefix runs past the break of the suffix
    have e1 := hb (hi - t - p) (by omega)
    have e2 := hb (hi - t) (by omega)
    have e3 := hf.per (hi - t - p) (Nat.zero_le _) (by omega)
    have idx1 : t + (hi - t - p) = hi - p := by omega
    have idx2 : t + (hi - t) = hi := by omega
    have idx3 : hi - t - p + p = hi - t := by omega
    rw [idx1] at e1
    rw [idx2] at e2
    rw [idx3] at e3
    exact absurd (by rw [e1, e2, e3]) hbreak

/-- With `y ≥ n - 2L + 1` and `y ≤ z`, a forward cap of `z + 2L` reaches `n`. -/
theorem cap_reaches_end {n L y z : ℕ} (hy : n + 1 ≤ y + 2 * L) (hyz : y ≤ z) : n ≤ z + 2 * L := by
  omega

/-- **A stop at the cap `z + ℓ` is not a break.** Take `S = a⁶⁴` and `L = ℓ = 16`, with `B = (32, 40]` the lower half of
the range of starts, `z = 40` and `p = 1`. The forward cap `z + ℓ = 56` is below `n`, and `hi = 56` has no break there.
The notes' rule for `hi < n` would give `t = hi - f = 56 - 32 = 24 ∉ B`, while `33` does start a border, of length
`31 ∈ [16, 32)`. So `border_start_of_run_break` cannot do without `hbreak`. -/
theorem capped_stop_is_not_break (a : α) :
    let S := List.replicate 64 a
    IsBorder (S.drop 33) S ∧ S[56 - 1]? = S[56]? ∧ 33 + 32 ≠ 56 := by
  intro S
  refine ⟨?_, by simp [S], by norm_num⟩
  rw [isBorder_drop_iff]
  intro i hi
  have hl : S.length = 64 := by simp [S]
  rw [hl] at hi
  simp only [S]
  rw [List.getElem?_replicate, List.getElem?_replicate]
  simp [hi, show i < 64 by omega]

end Strings
