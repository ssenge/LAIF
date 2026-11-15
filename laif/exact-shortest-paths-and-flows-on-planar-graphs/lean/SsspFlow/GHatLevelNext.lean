import SsspFlow.GHatLevelSsspLocal

/-!
# The input of the next level

From one level to the next, only the incised darts grow: the cut corners, the modes and the hosts
stay. So a node gets its input for the next level from its input for the current level and one bit
per neighbour, the bit of a new incised dart. With token lengths given by the costs of the darts, the
cost of a dart at a node is the sum of the lengths of its tokens with labels `0` and `1`, since a
dart has the token `0` or the token `1`.

* `LevelIn.next`: the local update of the input of a node.
* `RData.levelIn_next`: the update gives the input of the data with the new incised darts.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest

namespace RotSystem

namespace LevelIn

variable {n : ℕ}

/-- The input of a node for the next level, with the bit `F u` of a new incised dart to `u`. -/
def next (F : Fin n → Bool) (j : LevelIn n) : LevelIn n where
  me := j.me
  rot := j.rot
  own u := { j.own u with inc := (j.own u).inc || F u }
  lamO u l := if (l = .zero ↔ ((j.own u).inc || F u) = false) then j.lamO u .zero + j.lamO u .one else 0
  bnd := j.bnd
  src := j.src

end LevelIn

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S S' : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

/-- `λ` of a token as the cost of its dart. -/
theorem lamAt_cc (cc : N.G.Dart → ℕ) (lam : S.Tok → ℕ) (hlam : ∀ x, lam x = cc x.1.1) (w u : Fin n)
    (l : Lab) : S.lamAt lam w u l =
      if h : N.G.Adj w u then (if S.IsTok ((⟨(w, u), h⟩ : N.G.Dart), l) then cc ⟨(w, u), h⟩ else 0) else 0 := by
  unfold lamAt
  split_ifs with h1 h2
  · exact hlam _
  · rfl
  · rfl

/-- **The input of the next level.** Let `S'` have the incised darts of `S` and the darts with the
bit `F`, and the cut corners, modes and hosts of `S`, let both token lengths be the costs of the darts,
and let both sources be the star centre of `u₁`. Then the update of the input of a node `w` with the
bits `F w` is its input for `S'`. -/
theorem levelIn_next (F : Fin n → Fin n → Bool) (hF : ∀ w u, F w u = true → N.G.Adj w u)
    (hinc : ∀ d : N.G.Dart, d ∈ S'.inc ↔ d ∈ S.inc ∨ F d.fst d.snd = true)
    (hcut : S'.cut = S.cut) (hmode : S'.modeL = S.modeL) (hhost : S'.hostT = S.hostT)
    (cc : N.G.Dart → ℕ) (lam : S.Tok → ℕ) (lam' : S'.Tok → ℕ) (hlam : ∀ x, lam x = cc x.1.1)
    (hlam' : ∀ x, lam' x = cc x.1.1) (M : ℕ) (u₁ w : Fin n) :
    (S.levelIn hN lam M (S.starV hN u₁) w).next (F w) = S'.levelIn hN lam' M (S'.starV hN u₁) w := by
  have hmov : ∀ c, S'.MovB c ↔ S.MovB c := fun c => by simp only [MovB, hcut, hmode]
  have hown : ∀ u, { S.dinfoAt w u with inc := (S.dinfoAt w u).inc || F w u } = S'.dinfoAt w u := by
    intro u
    unfold dinfoAt
    by_cases h : N.G.Adj w u
    · simp only [dite_eq_left_of_eq_true (eq_true h), dinfo, hcut, hmode, hhost, hmov]
      congr 1
      rw [Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff,
        hinc ⟨(w, u), h⟩]
    · have hf : F w u = false := by
        cases hx : F w u
        · rfl
        · exact absurd (hF w u hx) h
      simp only [dite_eq_right_of_eq_false (eq_false h), hf, Bool.or_false]
  have hinc' : ∀ u, ((S.dinfoAt w u).inc || F w u) = (S'.dinfoAt w u).inc := fun u => by
    rw [← hown u]
  unfold LevelIn.next levelIn
  simp only [hown]
  congr 1
  funext u l
  rw [hinc' u]
  rw [S.lamAt_cc cc lam hlam, S'.lamAt_cc cc lam' hlam', S.lamAt_cc cc lam hlam]
  unfold dinfoAt
  by_cases h : N.G.Adj w u
  · simp only [dite_eq_left_of_eq_true (eq_true h), dinfo, IsTok]
    by_cases hi' : (⟨(w, u), h⟩ : N.G.Dart) ∈ S'.inc
    · by_cases hi : (⟨(w, u), h⟩ : N.G.Dart) ∈ S.inc <;> cases l <;> simp [hi, hi']
    · have hi : (⟨(w, u), h⟩ : N.G.Dart) ∉ S.inc := fun hi => hi' ((hinc _).2 (.inl hi))
      cases l <;> simp [hi, hi']
  · simp only [dite_eq_right_of_eq_false (eq_false h)]
    split_ifs <;> rfl

end RData

end RotSystem

end SsspFlow
