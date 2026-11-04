import Monge.TotallyMonotone
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Log

/-!
# The bisection recursion (Section 2 of the notes)

`rowMaxima` is the recursion. It finds `p` for the middle row on the current window, then recurses
on the rows above with window `[l, p]` and on the rows below with window `[p, u]`. It reads the
matrix only through a row-maximum oracle. `globalMax` compares the cells found. `globalMax_spec`
says this is the true maximum on every totally monotone matrix, `scanOracle_spec` says the oracle
spec can be met.

Then the window arithmetic: `width_split` is `c₁ + c₂ = c + 1`, `levelWidths_sum_le` is the level
bound `c + 2^j`, `levelCost_le` is Cauchy-Schwarz on a level, `totalCost_le` sums over the levels
to `O(√(k (c + k)))`, and `blockWidths_sum` is `Σ c_i = c + k` over the `k + 1` remaining blocks.
-/

namespace Monge

variable {r c : ℕ} {α : Type*} [LinearOrder α]

/-- `p` is the leftmost maximum of `f` on the window `[l, u]`. -/
def IsWindowMax (f : Fin c → α) (l u p : Fin c) : Prop :=
  l ≤ p ∧ p ≤ u ∧ (∀ j, l ≤ j → j ≤ u → f j ≤ f p) ∧ ∀ j, l ≤ j → j < p → f j < f p

/-- The spec of a row-maximum oracle: `orc i l u` is the leftmost maximum of row `i` on `[l, u]`. -/
def OracleSpec (M : Fin r → Fin c → α) (orc : Fin r → Fin c → Fin c → Fin c) : Prop :=
  ∀ i l u, l ≤ u → IsWindowMax (M i) l u (orc i l u)

/-- If the global leftmost maximum of a row lies in the window, a window maximum finds it. -/
theorem IsWindowMax.eq_of_isLeftmostMax {f : Fin c → α} {l u q P : Fin c}
    (hq : IsWindowMax f l u q) (hP : IsLeftmostMax f P) (h1 : l ≤ P) (h2 : P ≤ u) : q = P := by
  obtain ⟨hlq, hqu, hmax, hstrict⟩ := hq
  rcases lt_trichotomy q P with h | h | h
  · exact absurd (hP.2 q h) (not_lt.mpr (hmax P h1 h2))
  · exact h
  · exact absurd (hP.1 q) (not_le.mpr (hstrict P h1 h))

/-! ## The recursion -/

/-- The cells `(i, p(i))` for rows `s, …, s + n - 1`, with columns restricted to `[l, u]`. The middle
row is `⌊(s + t) / 2⌋` with `t = s + n - 1`. -/
def rowMaxima (orc : Fin r → Fin c → Fin c → Fin c) (s n : ℕ) (h : s + n ≤ r) (l u : Fin c) :
    List (Fin r × Fin c) :=
  if hn : n = 0 then [] else
    rowMaxima orc s ((n - 1) / 2) (by omega) l (orc ⟨s + (n - 1) / 2, by omega⟩ l u) ++
      (⟨s + (n - 1) / 2, by omega⟩, orc ⟨s + (n - 1) / 2, by omega⟩ l u) ::
        rowMaxima orc (s + (n - 1) / 2 + 1) (n - 1 - (n - 1) / 2) (by omega)
          (orc ⟨s + (n - 1) / 2, by omega⟩ l u) u
termination_by n
decreasing_by all_goals omega

/-- The algorithm: run the recursion on all rows and all columns, then take the best cell found. -/
def globalMax [NeZero c] (M : Fin r → Fin c → α) (orc : Fin r → Fin c → Fin c → Fin c) :
    Option (Fin r × Fin c) :=
  (rowMaxima orc 0 r (by omega) 0 ⟨c - 1, by have := NeZero.pos c; omega⟩).argmax
    fun q => M q.1 q.2

/-- Each row whose leftmost maximum lies in the window is found by the recursion. -/
theorem mem_rowMaxima [NeZero c] {M : Fin r → Fin c → α} {orc : Fin r → Fin c → Fin c → Fin c}
    (hM : TotallyMonotone M) (hO : OracleSpec M orc) (n s : ℕ) (h : s + n ≤ r) (l u : Fin c)
    (hlu : l ≤ u)
    (hwin : ∀ i : Fin r, s ≤ i → (i : ℕ) < s + n → l ≤ rowMax M i ∧ rowMax M i ≤ u)
    (i : Fin r) (hi1 : s ≤ i) (hi2 : (i : ℕ) < s + n) :
    (i, rowMax M i) ∈ rowMaxima orc s n h l u := by
  induction n using Nat.strong_induction_on generalizing s l u with
  | _ n ih =>
    have hn : n ≠ 0 := by omega
    rw [rowMaxima]
    simp only [hn, ↓reduceDIte]
    have hm : s + (n - 1) / 2 < r := by omega
    set m : Fin r := ⟨s + (n - 1) / 2, hm⟩ with hmdef
    have hmwin := hwin m (by simp [hmdef]) (by simp only [hmdef]; omega)
    have hp : orc m l u = rowMax M m :=
      (hO m l u hlu).eq_of_isLeftmostMax (rowMax_spec M m) hmwin.1 hmwin.2
    rw [hp]
    simp only [List.mem_append, List.mem_cons]
    rcases lt_trichotomy (i : ℕ) (s + (n - 1) / 2) with hlt | heq | hgt
    · left
      refine ih ((n - 1) / 2) (by omega) s _ l _ hmwin.1 (fun i' h1 h2 => ?_) hi1 (by omega)
      have hi'm : i' < m := by
        rw [Fin.lt_def]
        simp only [hmdef]
        omega
      exact ⟨(hwin i' h1 (by omega)).1, hM.rowMax_monotone hi'm.le⟩
    · right; left
      have : i = m := Fin.ext heq
      rw [this]
    · right; right
      refine ih (n - 1 - (n - 1) / 2) (by omega) (s + (n - 1) / 2 + 1) _ _ u hmwin.2
        (fun i' h1 h2 => ?_) (by omega) (by omega)
      have hi'm : m < i' := by
        rw [Fin.lt_def]
        simp only [hmdef]
        omega
      exact ⟨hM.rowMax_monotone hi'm.le, (hwin i' (by omega) (by omega)).2⟩

/-- **Correctness.** On every totally monotone matrix with at least one row and one column,
`globalMax` returns a cell holding the global maximum. -/
theorem globalMax_spec [NeZero c] {M : Fin r → Fin c → α} {orc : Fin r → Fin c → Fin c → Fin c}
    (hM : TotallyMonotone M) (hO : OracleSpec M orc) (hr : 0 < r) :
    ∃ q, globalMax M orc = some q ∧ ∀ i j, M i j ≤ M q.1 q.2 := by
  have hc := NeZero.pos c
  have hmem : ∀ i : Fin r, (i, rowMax M i) ∈
      rowMaxima orc 0 r (by omega) (0 : Fin c) ⟨c - 1, by omega⟩ := fun i =>
    mem_rowMaxima hM hO r 0 _ _ _ (by rw [Fin.le_def]; simp)
      (fun i' _ _ => ⟨by rw [Fin.le_def]; simp, by
        rw [Fin.le_def]; have := (rowMax M i').2; simp only; omega⟩) i (by omega) (by omega)
  have hne : (rowMaxima orc 0 r (by omega) (0 : Fin c) ⟨c - 1, by omega⟩) ≠ [] :=
    List.ne_nil_of_mem (hmem ⟨0, hr⟩)
  unfold globalMax
  cases hq : (rowMaxima orc 0 r (by omega) (0 : Fin c) ⟨c - 1, by omega⟩).argmax
      (fun q => M q.1 q.2) with
  | none => exact absurd (List.argmax_eq_none.mp hq) hne
  | some q =>
    refine ⟨q, rfl, fun i j => ?_⟩
    have h1 : M i j ≤ M i (rowMax M i) := (rowMax_spec M i).1 j
    have h2 : M i (rowMax M i) ≤ M q.1 q.2 :=
      List.le_of_mem_argmax (f := fun q : Fin r × Fin c => M q.1 q.2) (hmem i) (by simp [hq])
    exact h1.trans h2

/-! ## The spec can be met: a classical scan -/

/-- Scan a list of columns, keeping the first strict improvement. -/
def scanFrom (f : Fin c → α) : Fin c → List (Fin c) → Fin c
  | b, [] => b
  | b, x :: xs => scanFrom f (if f b < f x then x else b) xs

/-- The classical oracle that reads the whole window. -/
def scanOracle (M : Fin r → Fin c → α) (i : Fin r) (l u : Fin c) : Fin c :=
  scanFrom (M i) l ((List.finRange c).filter fun j => l < j ∧ j ≤ u)

theorem scanFrom_spec (f : Fin c → α) (xs : List (Fin c)) (b : Fin c) (hs : xs.Pairwise (· < ·))
    (hb : ∀ x ∈ xs, b < x) :
    (scanFrom f b xs = b ∨ scanFrom f b xs ∈ xs) ∧
    (∀ j, (j = b ∨ j ∈ xs) → f j ≤ f (scanFrom f b xs)) ∧
    (∀ j, (j = b ∨ j ∈ xs) → j < scanFrom f b xs → f j < f (scanFrom f b xs)) := by
  induction xs generalizing b with
  | nil =>
    show (b = b ∨ b ∈ []) ∧ (∀ j, (j = b ∨ j ∈ []) → f j ≤ f b) ∧
      (∀ j, (j = b ∨ j ∈ []) → j < b → f j < f b)
    refine ⟨Or.inl rfl, ?_, ?_⟩
    · rintro j (rfl | hj)
      · exact le_rfl
      · simp at hj
    · rintro j (rfl | hj) h
      · exact absurd h (lt_irrefl _)
      · simp at hj
  | cons x xs ih =>
    rw [List.pairwise_cons] at hs
    have hbx : b < x := hb x (by simp)
    simp only [scanFrom, List.mem_cons]
    by_cases hlt : f b < f x
    · simp only [hlt, ↓reduceIte]
      obtain ⟨h1, h2, h3⟩ := ih x hs.2 hs.1
      refine ⟨Or.inr h1, ?_, ?_⟩
      · rintro j (rfl | rfl | hj)
        · exact hlt.le.trans (h2 x (Or.inl rfl))
        · exact h2 j (Or.inl rfl)
        · exact h2 j (Or.inr hj)
      · rintro j (rfl | rfl | hj) hjlt
        · exact lt_of_lt_of_le hlt (h2 x (Or.inl rfl))
        · exact h3 j (Or.inl rfl) hjlt
        · exact h3 j (Or.inr hj) hjlt
    · simp only [hlt, ↓reduceIte]
      have hb' : ∀ y ∈ xs, b < y := fun y hy => hb y (by simp [hy])
      obtain ⟨h1, h2, h3⟩ := ih b hs.2 hb'
      refine ⟨?_, ?_, ?_⟩
      · rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
      · rintro j (rfl | rfl | hj)
        · exact h2 j (Or.inl rfl)
        · exact (not_lt.mp hlt).trans (h2 b (Or.inl rfl))
        · exact h2 j (Or.inr hj)
      · rintro j (rfl | rfl | hj) hjlt
        · exact h3 j (Or.inl rfl) hjlt
        · exact lt_of_le_of_lt (not_lt.mp hlt) (h3 b (Or.inl rfl) (hbx.trans hjlt))
        · exact h3 j (Or.inr hj) hjlt

/-- The scan meets the oracle spec, so the spec is not vacuous. -/
theorem scanOracle_spec (M : Fin r → Fin c → α) : OracleSpec M (scanOracle M) := by
  intro i l u hlu
  have hsorted : ((List.finRange c).filter fun j => l < j ∧ j ≤ u).Pairwise (· < ·) :=
    (List.pairwise_lt_finRange c).filter _
  have hmem : ∀ j, j ∈ (List.finRange c).filter (fun j => l < j ∧ j ≤ u) ↔ l < j ∧ j ≤ u := by
    intro j
    simp [List.mem_filter, List.mem_finRange]
  obtain ⟨h1, h2, h3⟩ := scanFrom_spec (M i) _ l hsorted (fun x hx => ((hmem x).mp hx).1)
  have hcover : ∀ j, l ≤ j → j ≤ u →
      (j = l ∨ j ∈ (List.finRange c).filter (fun j => l < j ∧ j ≤ u)) := by
    intro j hj1 hj2
    rcases hj1.eq_or_lt with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr ((hmem j).mpr ⟨hlt, hj2⟩)
  unfold scanOracle
  refine ⟨?_, ?_, fun j hj1 hj2 => h2 j (hcover j hj1 hj2), fun j hj1 hj2 => ?_⟩
  · rcases h1 with h1 | h1
    · rw [h1]
    · exact ((hmem _).mp h1).1.le
  · rcases h1 with h1 | h1
    · rw [h1]; exact hlu
    · exact ((hmem _).mp h1).2
  · refine h3 j (hcover j hj1 ?_) hj2
    rcases h1 with h1 | h1
    · rw [h1] at hj2; exact absurd hj1 (not_le.mpr hj2)
    · exact hj2.le.trans ((hmem _).mp h1).2

/-! ## A sanity run on a small integer matrix -/

/-- `-(i - j - 1)² + i` is inverse Monge. Its maximum is `5`, at row `5`, column `4`. -/
def sampleMatrix (i : Fin 6) (j : Fin 5) : ℤ := -((i : ℤ) - (j : ℤ) - 1) ^ 2 + (i : ℤ)

#guard (globalMax sampleMatrix (scanOracle sampleMatrix)).map (fun q => sampleMatrix q.1 q.2)
  == some 5
#guard (globalMax sampleMatrix (scanOracle sampleMatrix)).map (fun q => ((q.1 : ℕ), (q.2 : ℕ)))
  == some (5, 4)

/-! ## Windows -/

/-- The number of columns in `[l, u]`. -/
def width (l u : Fin c) : ℕ := (u : ℕ) - l + 1

/-- The row-window sum `c₁ + c₂ = c + 1`: the two windows share the pivot column. -/
theorem width_split {l p u : Fin c} (h1 : l ≤ p) (h2 : p ≤ u) :
    width l p + width p u = width l u + 1 := by
  have h1' : (l : ℕ) ≤ p := h1
  have h2' : (p : ℕ) ≤ u := h2
  unfold width
  omega

/-- The window widths of the recursion nodes at bisection level `j`. -/
def levelWidths (orc : Fin r → Fin c → Fin c → Fin c) :
    (j s n : ℕ) → (h : s + n ≤ r) → (l u : Fin c) → List ℕ
  | 0, _, n, _, l, u => if n = 0 then [] else [width l u]
  | j + 1, s, n, _, l, u =>
    if hn : n = 0 then [] else
      levelWidths orc j s ((n - 1) / 2) (by omega) l (orc ⟨s + (n - 1) / 2, by omega⟩ l u) ++
        levelWidths orc j (s + (n - 1) / 2 + 1) (n - 1 - (n - 1) / 2) (by omega)
          (orc ⟨s + (n - 1) / 2, by omega⟩ l u) u

variable {M : Fin r → Fin c → α} {orc : Fin r → Fin c → Fin c → Fin c}

/-- Level `j` has at most `2^j` nodes. -/
theorem levelWidths_length_le (j s n : ℕ) (h : s + n ≤ r) (l u : Fin c) :
    (levelWidths orc j s n h l u).length ≤ 2 ^ j := by
  induction j generalizing s n l u with
  | zero =>
    simp only [levelWidths]
    split_ifs <;> simp
  | succ j ih =>
    simp only [levelWidths]
    split_ifs with hn
    · simp
    · rw [List.length_append, pow_succ]
      have h1 := ih s ((n - 1) / 2) (by omega) l (orc ⟨s + (n - 1) / 2, by omega⟩ l u)
      have h2 := ih (s + (n - 1) / 2 + 1) (n - 1 - (n - 1) / 2) (by omega)
        (orc ⟨s + (n - 1) / 2, by omega⟩ l u) u
      omega

/-- Level `j` is empty unless there are at least `2^j` rows. -/
theorem levelWidths_eq_nil (j s n : ℕ) (h : s + n ≤ r) (l u : Fin c) (hn : n < 2 ^ j) :
    levelWidths orc j s n h l u = [] := by
  induction j generalizing s n l u with
  | zero =>
    have : n = 0 := by simpa using hn
    simp [levelWidths, this]
  | succ j ih =>
    simp only [levelWidths]
    split_ifs with hn0
    · rfl
    · rw [pow_succ] at hn
      rw [ih s ((n - 1) / 2) (by omega) l _ (by omega),
        ih (s + (n - 1) / 2 + 1) (n - 1 - (n - 1) / 2) (by omega) _ u (by omega)]
      rfl

/-- The level sum: over the nodes of a level, widths add up to at most `c + (#nodes) - 1`. -/
theorem levelWidths_sum_add_one_le (hO : OracleSpec M orc) (j s n : ℕ) (h : s + n ≤ r) (l u : Fin c)
    (hlu : l ≤ u) :
    (levelWidths orc j s n h l u).sum + 1 ≤ width l u + (levelWidths orc j s n h l u).length := by
  induction j generalizing s n l u with
  | zero =>
    simp only [levelWidths]
    split_ifs
    · simp [width]
    · simp
  | succ j ih =>
    simp only [levelWidths]
    split_ifs with hn
    · simp [width]
    · have hspec := hO ⟨s + (n - 1) / 2, by omega⟩ l u hlu
      have h1 := ih s ((n - 1) / 2) (by omega) l _ hspec.1
      have h2 := ih (s + (n - 1) / 2 + 1) (n - 1 - (n - 1) / 2) (by omega) _ u hspec.2.1
      have h3 := width_split hspec.1 hspec.2.1
      rw [List.sum_append, List.length_append]
      omega

/-- The bound in the notes: at level `j` the windows have total width at most `c + 2^j`. -/
theorem levelWidths_sum_le (hO : OracleSpec M orc) (j s n : ℕ) (h : s + n ≤ r) (l u : Fin c)
    (hlu : l ≤ u) : (levelWidths orc j s n h l u).sum ≤ width l u + 2 ^ j := by
  have h1 := levelWidths_sum_add_one_le hO j s n h l u hlu
  have h2 := levelWidths_length_le (orc := orc) j s n h l u
  omega

/-- Cauchy-Schwarz for square roots along a list. -/
theorem sum_sqrt_sq_le (L : List ℕ) :
    (L.map fun w : ℕ => √(w : ℝ)).sum ^ 2 ≤ (L.length : ℝ) * (L.sum : ℝ) := by
  induction L with
  | nil => simp
  | cons w L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    set s := (L.map fun w : ℕ => √(w : ℝ)).sum with hs
    set A := √(w : ℝ) with hA
    set n : ℝ := (L.length : ℝ) with hn
    set t : ℝ := (L.sum : ℝ) with ht
    have hA2 : A ^ 2 = (w : ℝ) := Real.sq_sqrt (by positivity)
    have hA0 : 0 ≤ A := Real.sqrt_nonneg _
    have hn0 : 0 ≤ n := by positivity
    have ht0 : 0 ≤ t := by positivity
    have key : 2 * A * s ≤ n * A ^ 2 + t := by
      rcases hn0.eq_or_lt with hn' | hn'
      · have hs0 : s = 0 := by
          have : s ^ 2 ≤ 0 := by
            calc s ^ 2 ≤ n * t := ih
              _ = 0 := by rw [← hn']; ring
          exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg s))
        rw [hs0, ← hn']
        simpa using ht0
      · have : n * (2 * A * s) ≤ n * (n * A ^ 2 + t) := by
          nlinarith [sq_nonneg (n * A - s)]
        exact le_of_mul_le_mul_left this hn'
    rw [← hA2]
    nlinarith

/-- The cost of a level: `Σ √(window width)` over its nodes. -/
noncomputable def levelCost (orc : Fin r → Fin c → Fin c → Fin c) (j s n : ℕ) (h : s + n ≤ r)
    (l u : Fin c) : ℝ :=
  ((levelWidths orc j s n h l u).map fun w : ℕ => √(w : ℝ)).sum

theorem levelCost_nonneg (j s n : ℕ) (h : s + n ≤ r) (l u : Fin c) :
    0 ≤ levelCost orc j s n h l u := by
  unfold levelCost
  apply List.sum_nonneg
  intro x hx
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx
  exact Real.sqrt_nonneg _

/-- The cost of level `j` is at most `√(2^j (c + 2^j))`, as in the notes. -/
theorem levelCost_le (hO : OracleSpec M orc) (j s n : ℕ) (h : s + n ≤ r) (l u : Fin c)
    (hlu : l ≤ u) :
    levelCost orc j s n h l u ≤ √((2 : ℝ) ^ j * ((width l u : ℝ) + 2 ^ j)) := by
  apply Real.le_sqrt_of_sq_le
  refine (sum_sqrt_sq_le _).trans ?_
  have h1 : ((levelWidths orc j s n h l u).length : ℝ) ≤ 2 ^ j := by
    exact_mod_cast levelWidths_length_le j s n h l u
  have h2 : ((levelWidths orc j s n h l u).sum : ℝ) ≤ (width l u : ℝ) + 2 ^ j := by
    exact_mod_cast levelWidths_sum_le hO j s n h l u hlu
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- The geometric sum of the level costs. -/
theorem sum_sqrt_two_pow_le (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), √((2 : ℝ) ^ j) ≤ 4 * √((2 : ℝ) ^ J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have hx : √((2 : ℝ) ^ J) ^ 2 = 2 ^ J := Real.sq_sqrt (by positivity)
    have hx0 : 0 ≤ √((2 : ℝ) ^ J) := Real.sqrt_nonneg _
    have hy : 4 * √((2 : ℝ) ^ J) / 3 ≤ √((2 : ℝ) ^ (J + 1)) := by
      apply Real.le_sqrt_of_sq_le
      have h2 : (2 : ℝ) ^ (J + 1) = 2 * 2 ^ J := by ring
      rw [h2]
      nlinarith [sq_nonneg (√((2 : ℝ) ^ J))]
    linarith

/-- **The total over all levels** is `O(√(k (c + k)))`, for `k` rows and window width `c`. -/
theorem totalCost_le (hO : OracleSpec M orc) (L s n : ℕ) (h : s + n ≤ r) (l u : Fin c)
    (hlu : l ≤ u) (hn : 0 < n) :
    ∑ j ∈ Finset.range L, levelCost orc j s n h l u ≤
      4 * √(n : ℝ) * √((width l u : ℝ) + n) := by
  set X := √((width l u : ℝ) + n) with hX
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hcost : ∀ j, 2 ^ j ≤ n → levelCost orc j s n h l u ≤ √((2 : ℝ) ^ j) * X := by
    intro j hj
    rw [hX, ← Real.sqrt_mul (by positivity)]
    refine (levelCost_le hO j s n h l u hlu).trans (Real.sqrt_le_sqrt ?_)
    have : ((2 : ℝ) ^ j) ≤ n := by exact_mod_cast hj
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hzero : ∀ j, ¬ 2 ^ j ≤ n → levelCost orc j s n h l u = 0 := by
    intro j hj
    unfold levelCost
    rw [levelWidths_eq_nil j s n h l u (not_le.mp hj)]
    rfl
  have hJ : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn.ne'
  calc ∑ j ∈ Finset.range L, levelCost orc j s n h l u
      ≤ ∑ j ∈ Finset.range L, if j ≤ Nat.log 2 n then √((2 : ℝ) ^ j) * X else 0 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : 2 ^ j ≤ n
        · have hjJ : j ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hj
          simp only [hjJ, ↓reduceIte]
          exact hcost j hj
        · rw [hzero j hj]
          split_ifs
          · positivity
          · exact le_rfl
    _ = ∑ j ∈ (Finset.range L).filter (· ≤ Nat.log 2 n), √((2 : ℝ) ^ j) * X :=
        (Finset.sum_filter _ _).symm
    _ ≤ ∑ j ∈ Finset.range (Nat.log 2 n + 1), √((2 : ℝ) ^ j) * X := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
          omega
        · intro j _ _
          positivity
    _ = (∑ j ∈ Finset.range (Nat.log 2 n + 1), √((2 : ℝ) ^ j)) * X := by
        rw [Finset.sum_mul]
    _ ≤ (4 * √(n : ℝ)) * X := by
        apply mul_le_mul_of_nonneg_right _ hX0
        refine (sum_sqrt_two_pow_le _).trans ?_
        have : ((2 : ℝ) ^ Nat.log 2 n) ≤ n := by exact_mod_cast hJ
        have := Real.sqrt_le_sqrt this
        linarith

/-- The `k + 1` row blocks left between `k` sampled rows, as window widths. -/
def blockWidths (orc : Fin r → Fin c → Fin c → Fin c) (s n : ℕ) (h : s + n ≤ r) (l u : Fin c) :
    List ℕ :=
  if hn : n = 0 then [width l u] else
    blockWidths orc s ((n - 1) / 2) (by omega) l (orc ⟨s + (n - 1) / 2, by omega⟩ l u) ++
      blockWidths orc (s + (n - 1) / 2 + 1) (n - 1 - (n - 1) / 2) (by omega)
        (orc ⟨s + (n - 1) / 2, by omega⟩ l u) u
termination_by n
decreasing_by all_goals omega

/-- There are `k + 1` blocks. -/
theorem blockWidths_length (n s : ℕ) (h : s + n ≤ r) (l u : Fin c) :
    (blockWidths orc s n h l u).length = n + 1 := by
  induction n using Nat.strong_induction_on generalizing s l u with
  | _ n ih =>
    rw [blockWidths]
    split_ifs with hn
    · simp [hn]
    · rw [List.length_append, ih _ (by omega), ih _ (by omega)]
      omega

/-- The block widths add up to `c + k`, which is `Σ c_i ≤ c + k` in Section 2 of the notes. -/
theorem blockWidths_sum (hO : OracleSpec M orc) (n s : ℕ) (h : s + n ≤ r) (l u : Fin c)
    (hlu : l ≤ u) : (blockWidths orc s n h l u).sum = width l u + n := by
  induction n using Nat.strong_induction_on generalizing s l u with
  | _ n ih =>
    rw [blockWidths]
    split_ifs with hn
    · simp [hn]
    · have hspec := hO ⟨s + (n - 1) / 2, by omega⟩ l u hlu
      have h3 := width_split hspec.1 hspec.2.1
      rw [List.sum_append, ih _ (by omega) _ _ _ _ hspec.1, ih _ (by omega) _ _ _ _ hspec.2.1]
      omega

end Monge
