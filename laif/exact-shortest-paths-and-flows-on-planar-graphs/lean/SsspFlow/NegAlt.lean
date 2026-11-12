import SsspFlow.NegWalk

/-!
# Few negative arcs: Lemma 1 of `notes/NEGATIVE.md`

Arcs `E` with integer weights `y` and integer potentials `φ`. The reduced weight of an arc is
`yr = y(a, b) + φ(a) - φ(b)`. `altSeq` alternates distances along the arcs with `yr ≥ 0`, one oracle
call each, with one relaxation over the arcs with `yr < 0`. After `t` steps, `altD` is the weight of a
walk of `E` that ends in `v` (`altD_walk`), and at most the weight of every walk of `E` that ends in
`v` and has at most `t` negative arcs (`altD_le`). `altSeq_ge` and `altSeq_le` bound the values.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal
open Cslib.Congest

namespace SsspFlow.Congest

section Alt

variable {V : Type} [Fintype V] (E : V → V → Prop) (y : V → V → ℤ) (φ : V → ℤ)

/-- The reduced weights. -/
def yr (a b : V) : ℤ := y a b + φ a - φ b

/-- The arcs of `E` with nonnegative reduced weight. -/
def posArc (a b : V) : Prop := E a b ∧ 0 ≤ yr y φ a b

/-- The arcs of `E` with negative reduced weight. -/
def negArc (a b : V) : Prop := E a b ∧ yr y φ a b < 0

/-- The reduced weights as natural lengths. -/
def posLen (a b : V) : ℕ := (yr y φ a b).toNat

open Classical in
/-- One relaxation over the negative arcs into `v`. -/
noncomputable def negRelax (A : V → ℤ) (v : V) : ℤ :=
  Finset.univ.inf' ⟨v, Finset.mem_univ v⟩ fun u =>
    if negArc E y φ u v then min (A v) (A u + yr y φ u v) else A v

/-- The alternation: distances along the nonnegative arcs from the offsets `-φ`, then from the
relaxed values. -/
noncomputable def altSeq : ℕ → V → ℤ
  | 0 => zdist (posArc E y φ) (posLen y φ) (fun a => -φ a)
  | i + 1 => zdist (posArc E y φ) (posLen y φ) (negRelax E y φ (altSeq i))

/-- **Lemma 1.** The value after `t` steps. -/
noncomputable def altD (t : ℕ) (v : V) : ℤ := altSeq E y φ t v + φ v

variable {E y φ}

theorem negRelax_le_self (A : V → ℤ) (v : V) : negRelax E y φ A v ≤ A v := by
  classical
  unfold negRelax
  refine (Finset.inf'_le _ (Finset.mem_univ v)).trans ?_
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem negRelax_le_arc (A : V → ℤ) {u v : V} (h : negArc E y φ u v) :
    negRelax E y φ A v ≤ A u + yr y φ u v := by
  classical
  unfold negRelax
  refine (Finset.inf'_le _ (Finset.mem_univ u)).trans ?_
  rw [ite_eq_left h]
  exact min_le_right _ _

theorem negRelax_cases (A : V → ℤ) (v : V) :
    negRelax E y φ A v = A v ∨ ∃ u, negArc E y φ u v ∧ negRelax E y φ A v = A u + yr y φ u v := by
  classical
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) ⟨v, Finset.mem_univ v⟩
    (fun u => if negArc E y φ u v then min (A v) (A u + yr y φ u v) else A v)
  have e : negRelax E y φ A v =
      if negArc E y φ u v then min (A v) (A u + yr y φ u v) else A v := hu
  split_ifs at e with h
  · rcases min_choice (A v) (A u + yr y φ u v) with h' | h'
    · exact .inl (e.trans h')
    · exact .inr ⟨u, h, e.trans h'⟩
  · exact .inl e

theorem zw_yr {adj : V → V → Prop} {a b : V} (p : Walk adj a b) :
    p.zw (yr y φ) = p.zw y + φ a - φ b :=
  Walk.zw_red y φ p

/-- Along the nonnegative arcs the natural length is the reduced weight. -/
theorem nwt_posLen : ∀ {a b : V} (p : Walk (posArc E y φ) a b),
    (p.nwt (posLen y φ) : ℤ) = p.zw (yr y φ)
  | _, _, .nil _ => rfl
  | _, _, .cons e p => by
    rw [Walk.nwt_cons, Walk.zw_cons, Nat.cast_add, nwt_posLen p, posLen, Int.toNat_of_nonneg e.2]

theorem posArc_le {a b : V} (h : posArc E y φ a b) : E a b := h.1

/-- A walk of `E` has only nonnegative arcs, or it ends with a negative arc followed by nonnegative
ones. -/
theorem split_last : ∀ {a b : V} (P : Walk E a b),
    (∃ p : Walk (posArc E y φ) a b, p.zw y = P.zw y ∧ P.cnt (negArc E y φ) = 0) ∨
    ∃ (u m : V) (Q : Walk E a u) (_ : negArc E y φ u m) (p : Walk (posArc E y φ) m b),
      Q.zw y + y u m + p.zw y = P.zw y ∧ Q.cnt (negArc E y φ) + 1 = P.cnt (negArc E y φ)
  | _, _, .nil a => .inl ⟨.nil a, rfl, rfl⟩
  | _, _, @Walk.cons _ _ a m _ e P => by
    classical
    rcases split_last P with ⟨p, hp, hc⟩ | ⟨u, m', Q, hn, p, hp, hc⟩
    · by_cases hneg : negArc E y φ a m
      · refine .inr ⟨a, m, .nil a, hneg, p, ?_, ?_⟩
        · rw [Walk.zw_cons, hp, Walk.zw_nil]
          ring
        · rw [Walk.cnt_cons, ite_eq_left hneg, hc, Walk.cnt_nil]
      · have hpos : posArc E y φ a m := ⟨e, not_lt.1 fun h => hneg ⟨e, h⟩⟩
        refine .inl ⟨.cons hpos p, ?_, ?_⟩
        · rw [Walk.zw_cons, Walk.zw_cons, hp]
        · rw [Walk.cnt_cons, ite_eq_right hneg, hc]
    · refine .inr ⟨u, m', .cons e Q, hn, p, ?_, ?_⟩
      · rw [Walk.zw_cons, Walk.zw_cons, ← hp]
        ring
      · rw [Walk.cnt_cons, Walk.cnt_cons, ← hc]
        omega

/-- **Lemma 1, lower bound.** Each value is `y(P) - φ(v)` for a walk `P` of `E` that ends in `v`. -/
theorem altSeq_walk : ∀ (i : ℕ) (v : V), ∃ a, ∃ P : Walk E a v, altSeq E y φ i v = P.zw y - φ v
  | 0, v => by
    obtain ⟨a, p, hp⟩ := zdist_spec (adj := posArc E y φ) (len := posLen y φ) (o := fun a => -φ a) v
    refine ⟨a, p.lift fun _ _ h => h.1, ?_⟩
    rw [show altSeq E y φ 0 v = _ from hp, nwt_posLen, zw_yr, Walk.zw_lift]
    ring
  | i + 1, v => by
    obtain ⟨a, p, hp⟩ := zdist_spec (adj := posArc E y φ) (len := posLen y φ)
      (o := negRelax E y φ (altSeq E y φ i)) v
    have e : altSeq E y φ (i + 1) v = negRelax E y φ (altSeq E y φ i) a + p.zw (yr y φ) := by
      rw [show altSeq E y φ (i + 1) v = _ from hp, nwt_posLen]
    rcases negRelax_cases (altSeq E y φ i) a with h | ⟨u, hu, h⟩
    · obtain ⟨x, Q, hQ⟩ := altSeq_walk i a
      refine ⟨x, Q.append (p.lift fun _ _ h => h.1), ?_⟩
      rw [e, h, hQ, Walk.zw_append, Walk.zw_lift, zw_yr]
      ring
    · obtain ⟨x, Q, hQ⟩ := altSeq_walk i u
      refine ⟨x, Q.append (.cons hu.1 (p.lift fun _ _ h => h.1)), ?_⟩
      rw [e, h, hQ, Walk.zw_append, Walk.zw_cons, Walk.zw_lift, zw_yr, yr]
      ring

/-- **Lemma 1, upper bound.** Each walk of `E` with at most `i` negative arcs is seen after `i`
steps. -/
theorem altSeq_le : ∀ (i : ℕ) {a v : V} (P : Walk E a v), P.cnt (negArc E y φ) ≤ i →
    altSeq E y φ i v ≤ P.zw y - φ v
  | 0, a, v, P, hP => by
    rcases split_last P with ⟨p, hp, -⟩ | ⟨u, m, Q, -, p, -, hc⟩
    · have := zdist_le (adj := posArc E y φ) (len := posLen y φ) (o := fun a => -φ a) p
      rw [nwt_posLen, zw_yr, hp] at this
      show altSeq E y φ 0 v ≤ _
      unfold altSeq
      linarith
    · omega
  | i + 1, a, v, P, hP => by
    rcases split_last P with ⟨p, hp, -⟩ | ⟨u, m, Q, hn, p, hp, hc⟩
    · have h₁ := zdist_le (adj := posArc E y φ) (len := posLen y φ)
        (o := negRelax E y φ (altSeq E y φ i)) p
      rw [nwt_posLen, zw_yr, hp] at h₁
      have h₂ := negRelax_le_self (E := E) (y := y) (φ := φ) (altSeq E y φ i) a
      have h₃ := altSeq_le i (.nil a) (by simp)
      rw [Walk.zw_nil] at h₃
      show altSeq E y φ (i + 1) v ≤ _
      unfold altSeq
      linarith
    · have h₁ := zdist_le (adj := posArc E y φ) (len := posLen y φ)
        (o := negRelax E y φ (altSeq E y φ i)) p
      rw [nwt_posLen, zw_yr] at h₁
      have h₂ := negRelax_le_arc (E := E) (y := y) (φ := φ) (altSeq E y φ i) hn
      have h₃ := altSeq_le i Q (by omega)
      rw [yr] at h₂
      show altSeq E y φ (i + 1) v ≤ _
      unfold altSeq
      linarith

theorem altD_walk (t : ℕ) (v : V) : ∃ a, ∃ P : Walk E a v, altD E y φ t v = P.zw y := by
  obtain ⟨a, P, hP⟩ := altSeq_walk (E := E) (y := y) (φ := φ) t v
  exact ⟨a, P, by rw [altD, hP]; ring⟩

theorem altD_le (t : ℕ) {a v : V} (P : Walk E a v) (hP : P.cnt (negArc E y φ) ≤ t) :
    altD E y φ t v ≤ P.zw y := by
  have := altSeq_le (E := E) (y := y) (φ := φ) t P hP
  rw [altD]
  linarith

theorem altD_nonpos (t : ℕ) (v : V) : altD E y φ t v ≤ 0 := by
  simpa using altD_le (E := E) (y := y) (φ := φ) t (.nil v) (by simp)

/-- The values stay at most `-φ`. -/
theorem altSeq_le_off (i : ℕ) (v : V) : altSeq E y φ i v ≤ -φ v := by
  simpa using altSeq_le (E := E) (y := y) (φ := φ) i (.nil v) (by simp)

/-- The values stay at least `-i (M + 1)` when `-M ≤ φ ≤ 0` and the weights are at least `-1`. -/
theorem altSeq_ge {M : ℤ} (hM : ∀ a, -M ≤ φ a ∧ φ a ≤ 0) (hy : ∀ a b, E a b → -1 ≤ y a b) :
    ∀ (i : ℕ) (v : V), -(i * (M + 1)) ≤ altSeq E y φ i v
  | 0, v => by
    show _ ≤ zdist _ _ _ v
    refine le_zdist (fun a => ?_) v
    have := hM a
    push_cast
    linarith
  | i + 1, v => by
    show _ ≤ zdist _ _ _ v
    refine le_zdist (fun a => ?_) v
    rcases negRelax_cases (E := E) (y := y) (φ := φ) (altSeq E y φ i) a with h | ⟨u, hu, h⟩
    · rw [h]
      have := altSeq_ge hM hy i a
      have hM0 : 0 ≤ M + 1 := by have := hM a; linarith
      push_cast
      nlinarith
    · rw [h, yr]
      have := altSeq_ge hM hy i u
      have := hy u a hu.1
      have := hM u
      have := hM a
      push_cast
      linarith

end Alt

end SsspFlow.Congest
