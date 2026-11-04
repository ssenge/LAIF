import Covers.Range

/-!
# The outer loop of Theorem 1, with correct subroutines

`find k` returns `b_k` if it exists, and `test` decides covers. If both are correct, the first `b_k` that covers `S` is a
shortest cover, with at most `log₂ n + 1` calls of each. This is the deterministic skeleton: its quantum subroutines
appear in `Model.lean` and their cost in `Cost.lean`.
-/

namespace Strings

variable {α : Type*}

/-- The loop over `k = 0, …, K`: the first `b_k` that passes the test. -/
def firstCover (find : ℕ → Option (List α)) (test : List α → Bool) : ℕ → Option (List α)
  | 0 => (find 0).filter test
  | K + 1 =>
    match firstCover find test K with
    | some x => some x
    | none => (find (K + 1)).filter test

variable {find : ℕ → Option (List α)} {test : List α → Bool} {S : List α}

theorem filter_some_iff {o : Option (List α)} {x : List α} :
    o.filter test = some x ↔ o = some x ∧ test x = true := by
  cases o with
  | none => simp
  | some v =>
    simp only [Option.filter_some, Option.some.injEq]
    constructor
    · intro h
      split at h
      · obtain rfl := Option.some.inj h
        exact ⟨rfl, ‹_›⟩
      · cases h
    · rintro ⟨rfl, h⟩
      simp [h]

theorem firstCover_spec (hfind : ∀ k b, find k = some b ↔ IsRangeMin k b S)
    (htest : ∀ b, test b = true ↔ Covers b S) (K : ℕ) :
    (∀ x, firstCover find test K = some x →
      ∃ k, k ≤ K ∧ IsRangeMin k x S ∧ Covers x S ∧ ∀ j, j < k → ∀ b, IsRangeMin j b S → ¬ Covers b S) ∧
    (firstCover find test K = none → ∀ j, j ≤ K → ∀ b, IsRangeMin j b S → ¬ Covers b S) := by
  induction K with
  | zero =>
    constructor
    · intro x hx
      obtain ⟨h1, h2⟩ := filter_some_iff.1 hx
      exact ⟨0, le_rfl, (hfind _ _).1 h1, (htest _).1 h2, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    · intro hn j hj b hb hc
      obtain rfl : j = 0 := by omega
      have : (find 0).filter test = some b :=
        filter_some_iff.2 ⟨(hfind _ _).2 hb, (htest _).2 hc⟩
      simp only [firstCover] at hn
      rw [this] at hn
      cases hn
  | succ K ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · intro x hx
      simp only [firstCover] at hx
      cases hK : firstCover find test K with
      | some y =>
        rw [hK] at hx
        obtain rfl : y = x := by simpa using hx
        obtain ⟨k, hk, h⟩ := ih1 y hK
        exact ⟨k, by omega, h⟩
      | none =>
        rw [hK] at hx
        obtain ⟨h1, h2⟩ := filter_some_iff.1 hx
        exact ⟨K + 1, le_rfl, (hfind _ _).1 h1, (htest _).1 h2, fun j hj => ih2 hK j (by omega)⟩
    · intro hn j hj b hb hc
      simp only [firstCover] at hn
      cases hK : firstCover find test K with
      | some y =>
        rw [hK] at hn
        cases hn
      | none =>
        rw [hK] at hn
        by_cases hjK : j ≤ K
        · exact ih2 hK j hjK b hb hc
        · obtain rfl : j = K + 1 := by omega
          have : (find (K + 1)).filter test = some b :=
            filter_some_iff.2 ⟨(hfind _ _).2 hb, (htest _).2 hc⟩
          rw [this] at hn
          cases hn

/-- **Correctness of the outer loop.** With correct `find` and `test`, the loop on `k ≤ log₂ n` returns a shortest
cover of a nonempty string. -/
theorem firstCover_correct (hS : S ≠ []) (hfind : ∀ k b, find k = some b ↔ IsRangeMin k b S)
    (htest : ∀ b, test b = true ↔ Covers b S) :
    ∃ C, firstCover find test (Nat.log 2 S.length) = some C ∧ IsShortestCover C S := by
  obtain ⟨h1, h2⟩ := firstCover_spec hfind htest (Nat.log 2 S.length)
  cases hK : firstCover find test (Nat.log 2 S.length) with
  | some x =>
    obtain ⟨k, _, hx, hc, hfirst⟩ := h1 x hK
    exact ⟨x, rfl, first_covering_rangeMin_isShortest hS hx hc hfirst⟩
  | none =>
    exfalso
    obtain ⟨C, hC⟩ := exists_shortestCover S
    obtain ⟨k, hk, -⟩ := corollary_shortest hS hC
    have hle : C.length ≤ S.length := (hC.1.isBorder hS).length_le
    have hkle : k ≤ Nat.log 2 S.length :=
      Nat.le_log_of_pow_le (by norm_num) (hk.2.1.1.trans hle)
    exact h2 hK k hkle C hk hC.1

end Strings
