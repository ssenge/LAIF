import SsspFlow.NegAlt
import SsspFlow.NegScaling

/-!
# The restricted problem: Proposition 4 of `notes/NEGATIVE.md`, the deterministic part

Kept arcs with integer weights `ys` are *restricted* (`Restr`): weights at least `-1`, and every
closed walk at least as heavy as it is long. `wdist` is the least weight of a walk that ends in a
vertex, and `short_walk` is Lemma 3. The levels `levPhi` run Lemma 1 inside the clusters of each
decomposition, from the potentials of the level before, and shift by the index of the cluster. The
last level uses all kept arcs. If the decompositions behave (`Good`), the last potential makes all
kept arcs nonnegative (`levPhi_last`). It always lies in `[-n, 0]` (`levPhi_last_bounds`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal
open Cslib.Congest

namespace SsspFlow.Congest

section WDist

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Weights at least `-1`, and closed walks at least as heavy as they are long. -/
structure Restr (E : V → V → Prop) (y : V → V → ℤ) : Prop where
  low : ∀ a b, E a b → -1 ≤ y a b
  cyc : ∀ a (C : Walk E a a), (C.len : ℤ) ≤ C.zw y

theorem Restr.mono {E E' : V → V → Prop} {y : V → V → ℤ} (h : Restr E y) (hE : ∀ a b, E' a b → E a b) :
    Restr E' y where
  low a b h' := h.low a b (hE a b h')
  cyc a C := by simpa using h.cyc a (C.lift hE)

theorem Restr.noNeg {E : V → V → Prop} {y : V → V → ℤ} (h : Restr E y) (a : V) (C : Walk E a a) :
    0 ≤ C.zw y :=
  le_trans (by positivity) (h.cyc a C)

/-- The least weight of a walk of `E` that ends in `v`, the empty walk included. -/
noncomputable def wdist (E : V → V → Prop) (y : V → V → ℤ) (v : V) : ℤ :=
  sInf {z | ∃ a, ∃ P : Walk E a v, z = P.zw y}

variable {E : V → V → Prop} {y : V → V → ℤ}

theorem Restr.nodup_ge (h : Restr E y) {a b : V} (Q : Walk E a b) (hQ : Q.support.Nodup) :
    -((Fintype.card V : ℤ) - 1) ≤ Q.zw y := by
  have h1 := Walk.len_lt_card Q hQ
  have h2 := Walk.neg_len_le_zw y h.low Q
  omega

theorem wdist_bdd (h : Restr E y) (v : V) : BddBelow {z | ∃ a, ∃ P : Walk E a v, z = P.zw y} := by
  refine ⟨-((Fintype.card V : ℤ) - 1), ?_⟩
  rintro z ⟨a, P, rfl⟩
  obtain ⟨Q, hQ, hw, -⟩ := Walk.exists_nodup_le y h.noNeg P
  have := h.nodup_ge Q hQ
  omega

theorem wdist_le (h : Restr E y) {a v : V} (P : Walk E a v) : wdist E y v ≤ P.zw y :=
  csInf_le (wdist_bdd h v) ⟨a, P, rfl⟩

/-- The least weight is that of a walk without repeated vertices. -/
theorem wdist_spec (h : Restr E y) (v : V) :
    ∃ a, ∃ P : Walk E a v, P.support.Nodup ∧ wdist E y v = P.zw y := by
  obtain ⟨a, P, hP⟩ := Int.csInf_mem (s := {z | ∃ a, ∃ P : Walk E a v, z = P.zw y})
    ⟨_, v, .nil v, rfl⟩ (wdist_bdd h v)
  obtain ⟨Q, hQ, hw, -⟩ := Walk.exists_nodup_le y h.noNeg P
  have := wdist_le h Q
  exact ⟨a, Q, hQ, le_antisymm this (by unfold wdist; omega)⟩

theorem wdist_nonpos (h : Restr E y) (v : V) : wdist E y v ≤ 0 := by
  simpa using wdist_le h (.nil v)

theorem wdist_ge (h : Restr E y) (v : V) : -((Fintype.card V : ℤ) - 1) ≤ wdist E y v := by
  obtain ⟨a, P, hP, e⟩ := wdist_spec h v
  rw [e]
  exact h.nodup_ge P hP

theorem wdist_triangle (h : Restr E y) {a b : V} (hab : E a b) :
    wdist E y b ≤ wdist E y a + y a b := by
  obtain ⟨c, P, -, e⟩ := wdist_spec h a
  have := wdist_le h (P.append (.cons hab (.nil b)))
  rw [Walk.zw_append, Walk.zw_cons, Walk.zw_nil] at this
  omega

end WDist

section Short

variable {V : Type} {K : V → V → Prop} {y : V → V → ℤ}

/-- `max(y, 0)` as natural lengths. -/
def posPart (y : V → V → ℤ) (a b : V) : ℕ := (max (y a b) 0).toNat

theorem nwt_posPart : ∀ {a b : V} (p : Walk K a b),
    (p.nwt (posPart y) : ℤ) = p.zw (fun a b => max (y a b) 0)
  | _, _, .nil _ => rfl
  | _, _, .cons e p => by
    rw [Walk.nwt_cons, Walk.zw_cons, Nat.cast_add, nwt_posPart p, posPart,
      Int.toNat_of_nonneg (le_max_right _ _)]

/-- **Lemma 3.** A walk `P` of weight at most `0` from `a` to `v`, with a walk back of rounded weight
at most `d`, has at most `d` arcs and rounded weight at most `d`. -/
theorem short_walk [Fintype V] [DecidableEq V] (h : Restr K y) {a v : V} (P : Walk K a v)
    (hP : P.zw y ≤ 0) (Q : Walk K v a) {d : ℕ} (hQ : Q.nwt (posPart y) ≤ d) :
    P.len ≤ d ∧ P.zw (fun a b => max (y a b) 0) ≤ d := by
  have hC := h.cyc a (P.append Q)
  rw [Walk.len_append, Walk.zw_append] at hC
  have h₁ := Walk.zw_le_pos y Q
  have h₂ := nwt_posPart (y := y) Q
  have h₃ := Walk.zw_pos_le y h.low P
  have h₄ : ((Q.nwt (posPart y) : ℕ) : ℤ) ≤ d := by exact_mod_cast hQ
  push_cast at hC
  constructor
  · have : (P.len : ℤ) ≤ d := by linarith
    exact_mod_cast this
  · linarith

end Short

/-! ### Minimum over the repetitions -/

/-- `min_{q ≤ R} f q`. -/
def minR (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => f 0
  | R + 1 => min (minR f R) (f (R + 1))

theorem minR_le (f : ℕ → ℤ) : ∀ {R q : ℕ}, q ≤ R → minR f R ≤ f q
  | 0, q, h => by obtain rfl : q = 0 := by omega
                  exact le_rfl
  | R + 1, q, h => by
    rcases Nat.lt_or_ge q (R + 1) with h' | h'
    · exact (min_le_left _ _).trans (minR_le f (by omega))
    · obtain rfl : q = R + 1 := by omega
      exact min_le_right _ _

theorem le_minR {f : ℕ → ℤ} {m : ℤ} : ∀ {R : ℕ}, (∀ q ≤ R, m ≤ f q) → m ≤ minR f R
  | 0, h => h 0 le_rfl
  | R + 1, h => le_min (le_minR fun q hq => h q (by omega)) (h _ le_rfl)

theorem minR_mem (f : ℕ → ℤ) : ∀ R : ℕ, ∃ q ≤ R, minR f R = f q
  | 0 => ⟨0, le_rfl, rfl⟩
  | R + 1 => by
    obtain ⟨q, hq, e⟩ := minR_mem f R
    rcases min_choice (minR f R) (f (R + 1)) with h | h
    · exact ⟨q, by omega, (show minR f (R + 1) = _ from h).trans e⟩
    · exact ⟨R + 1, le_rfl, h⟩

/-! ### The levels -/

section Levels

variable {V : Type} [Fintype V] [DecidableEq V]
variable (n L R t : ℕ) (kept : V → V → Prop) (ys : V → V → ℤ) (idx : ℕ → ℕ → V → ℕ)

/-- The arcs inside the clusters of the decomposition `(ℓ, r)`; at level `L` all kept arcs. -/
def clArc (ℓ r : ℕ) (a b : V) : Prop := kept a b ∧ (ℓ < L → idx ℓ r a = idx ℓ r b)

/-- An arc from a larger index to a smaller one. -/
def cutArc (ℓ r : ℕ) (a b : V) : Prop := idx ℓ r b < idx ℓ r a

/-- The shift by the index of the cluster, below level `L`. -/
def shiftI (ℓ r : ℕ) (v : V) : ℤ := if ℓ < L then (n : ℤ) * idx ℓ r v else 0

/-- The potentials of the levels: the least clipped value of Lemma 1 over the potentials of the
level before, minus the shift. Level `0` starts from the potential `0`. -/
noncomputable def levPhi : ℕ → ℕ → V → ℤ
  | 0 => fun r v =>
    minR (fun _ => max (-(n : ℤ)) (altD (clArc L kept idx 0 r) ys (fun _ => 0) t v)) R -
      shiftI n L idx 0 r v
  | ℓ + 1 => fun r v =>
    minR (fun q => max (-(n : ℤ)) (altD (clArc L kept idx (ℓ + 1) r) ys (levPhi ℓ q) t v)) R -
      shiftI n L idx (ℓ + 1) r v

/-- The potentials that level `ℓ` starts from. -/
noncomputable def prevPhi : ℕ → ℕ → V → ℤ
  | 0 => fun _ _ => 0
  | ℓ + 1 => levPhi n L R t kept ys idx ℓ

theorem levPhi_eq (ℓ r : ℕ) (v : V) : levPhi n L R t kept ys idx ℓ r v =
    minR (fun q => max (-(n : ℤ)) (altD (clArc L kept idx ℓ r) ys (prevPhi n L R t kept ys idx ℓ q) t v)) R -
      shiftI n L idx ℓ r v := by
  cases ℓ <;> rfl

/-- The decompositions behave: the input is restricted, clusters below level `L` are close in the
rounded weights, and the shortest walks of each cluster at each level `ℓ ≥ 1` have a repetition of
level `ℓ - 1` that cuts at most `t` of their arcs. -/
structure Good : Prop where
  card : Fintype.card V ≤ n
  restr : Restr kept ys
  t2 : 2 ≤ t
  hL : 1 ≤ L
  s1 : ∀ ℓ < L, ∀ r ≤ R, ∀ u v, idx ℓ r u = idx ℓ r v →
    ∃ Q : Walk kept u v, Q.nwt (posPart ys) ≤ 2 ^ (ℓ + 1)
  s2 : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → ∀ r ≤ R, ∀ v, ∃ a, ∃ P : Walk (clArc L kept idx ℓ r) a v,
    P.zw ys = wdist (clArc L kept idx ℓ r) ys v ∧ ∃ r' ≤ R, P.cnt (cutArc idx (ℓ - 1) r') ≤ t

variable {n L R t kept ys idx}

theorem clArc_kept {ℓ r : ℕ} {a b : V} (h : clArc L kept idx ℓ r a b) : kept a b := h.1

theorem idx_walk {ℓ r : ℕ} (hℓ : ℓ < L) : ∀ {a b : V}, Walk (clArc L kept idx ℓ r) a b →
    idx ℓ r a = idx ℓ r b
  | _, _, .nil _ => rfl
  | _, _, .cons e P => (e.2 hℓ).trans (idx_walk hℓ P)

/-- The potentials of each level, shifted back, lie in `[-n, 0]`. -/
theorem levPhi_bounds (ℓ r : ℕ) (v : V) :
    -(n : ℤ) ≤ levPhi n L R t kept ys idx ℓ r v + shiftI n L idx ℓ r v ∧
      levPhi n L R t kept ys idx ℓ r v + shiftI n L idx ℓ r v ≤ 0 := by
  rw [levPhi_eq]
  refine ⟨?_, ?_⟩
  · have := le_minR (f := fun q => max (-(n : ℤ))
      (altD (clArc L kept idx ℓ r) ys (prevPhi n L R t kept ys idx ℓ q) t v)) (m := -(n : ℤ))
      (R := R) fun q _ => le_max_left _ _
    linarith
  · have := minR_le (fun q => max (-(n : ℤ))
      (altD (clArc L kept idx ℓ r) ys (prevPhi n L R t kept ys idx ℓ q) t v)) (R := R) (q := 0)
      (Nat.zero_le _)
    have h0 : max (-(n : ℤ)) (altD (clArc L kept idx ℓ r) ys (prevPhi n L R t kept ys idx ℓ 0) t v) ≤ 0 :=
      max_le (by linarith [Int.natCast_nonneg n]) (altD_nonpos t v)
    linarith

/-- The last potential lies in `[-n, 0]`. -/
theorem levPhi_last_bounds (v : V) :
    -(n : ℤ) ≤ levPhi n L R t kept ys idx L 0 v ∧ levPhi n L R t kept ys idx L 0 v ≤ 0 := by
  have h := levPhi_bounds (n := n) (L := L) (R := R) (t := t) (kept := kept) (ys := ys) (idx := idx) L 0 v
  rw [shiftI, ite_eq_right (lt_irrefl L), add_zero] at h
  exact h

variable (hG : Good n L R t kept ys idx)
include hG

theorem Good.restr_cl (ℓ r : ℕ) : Restr (clArc L kept idx ℓ r) ys :=
  hG.restr.mono fun _ _ h => h.1

theorem Good.wdist_ge_n (ℓ r : ℕ) (v : V) : -((n : ℤ) - 1) ≤ wdist (clArc L kept idx ℓ r) ys v := by
  have := wdist_ge (hG.restr_cl ℓ r) v
  have := hG.card
  have : (Fintype.card V : ℤ) ≤ n := by exact_mod_cast this
  linarith

/-- A(ℓ): the least value over the repetitions is the least weight in the cluster, if some potential
of the level before sees a shortest walk. -/
theorem Good.levPhi_of {ℓ r : ℕ} (v : V)
    (hq : ∃ q ≤ R, altD (clArc L kept idx ℓ r) ys (prevPhi n L R t kept ys idx ℓ q) t v ≤
      wdist (clArc L kept idx ℓ r) ys v) :
    levPhi n L R t kept ys idx ℓ r v = wdist (clArc L kept idx ℓ r) ys v - shiftI n L idx ℓ r v := by
  rw [levPhi_eq]
  congr 1
  have hW := hG.wdist_ge_n ℓ r v
  apply le_antisymm
  · obtain ⟨q, hqR, hle⟩ := hq
    exact (minR_le _ hqR).trans (max_le (by linarith) hle)
  · refine le_minR fun q _ => ?_
    obtain ⟨a, P, hP⟩ := altD_walk (E := clArc L kept idx ℓ r) (y := ys)
      (φ := prevPhi n L R t kept ys idx ℓ q) t v
    have := wdist_le (hG.restr_cl ℓ r) P
    exact le_max_of_le_right (by linarith)

/-- B(ℓ) from A(ℓ): kept arcs that are not cut are nonnegative under the potential of `(ℓ, r)`. -/
theorem Good.forward {ℓ r : ℕ}
    (hA : ∀ v, levPhi n L R t kept ys idx ℓ r v = wdist (clArc L kept idx ℓ r) ys v - shiftI n L idx ℓ r v)
    {a b : V} (hab : kept a b) (hcut : ℓ < L → ¬ cutArc idx ℓ r a b) :
    0 ≤ ys a b + levPhi n L R t kept ys idx ℓ r a - levPhi n L R t kept ys idx ℓ r b := by
  rw [hA a, hA b]
  have hR := hG.restr_cl ℓ r
  by_cases hℓ : ℓ < L
  · have hc := hcut hℓ
    unfold cutArc at hc
    unfold shiftI
    rw [ite_eq_left hℓ, ite_eq_left hℓ]
    rcases Nat.lt_or_ge (idx ℓ r a) (idx ℓ r b) with hlt | hge
    · have hlow := hG.restr.low a b hab
      have ha := hG.wdist_ge_n ℓ r a
      have hb := wdist_nonpos hR b
      have := NegScaling.forward_arc (n := (n : ℤ)) hlow ha hb (Int.natCast_nonneg n)
        (Int.ofNat_lt.2 hlt)
      linarith
    · have heq : idx ℓ r a = idx ℓ r b := by omega
      have := wdist_triangle hR (show clArc L kept idx ℓ r a b from ⟨hab, fun _ => heq⟩)
      rw [heq]
      linarith
  · unfold shiftI
    rw [ite_eq_right hℓ, ite_eq_right hℓ]
    have := wdist_triangle hR (show clArc L kept idx ℓ r a b from ⟨hab, fun h => absurd h hℓ⟩)
    linarith

/-- A(ℓ) for all levels up to `L`. -/
theorem Good.levels : ∀ ℓ ≤ L, ∀ r ≤ R, ∀ v,
    levPhi n L R t kept ys idx ℓ r v = wdist (clArc L kept idx ℓ r) ys v - shiftI n L idx ℓ r v
  | 0, _, r, hr, v => by
    refine hG.levPhi_of v ⟨0, Nat.zero_le _, ?_⟩
    obtain ⟨a, P, -, e⟩ := wdist_spec (hG.restr_cl 0 r) v
    have h0 : 0 < L := hG.hL
    obtain ⟨Q, hQ⟩ := hG.s1 0 h0 r hr v a (idx_walk h0 P).symm
    have hP0 : (P.lift fun _ _ h => h.1).zw ys ≤ 0 := by
      rw [Walk.zw_lift, ← e]
      exact wdist_nonpos (hG.restr_cl 0 r) v
    have hs := (short_walk hG.restr (P.lift fun _ _ h => h.1) hP0 Q hQ).1
    rw [Walk.len_lift] at hs
    have hcnt := Walk.cnt_le_len (negArc (clArc L kept idx 0 r) ys
      (prevPhi n L R t kept ys idx 0 0)) P
    have := hG.t2
    simp only [zero_add, pow_one] at hs
    rw [e]
    exact altD_le t P (by omega)
  | ℓ + 1, hℓ, r, hr, v => by
    refine hG.levPhi_of v ?_
    obtain ⟨a, P, e, r', hr', hcnt⟩ := hG.s2 (ℓ + 1) (by omega) hℓ r hr v
    refine ⟨r', hr', ?_⟩
    have hA := Good.levels ℓ (by omega) r' hr'
    rw [← e]
    refine altD_le t P (le_trans (Walk.cnt_mono (fun a b hab hneg => ?_) P) hcnt)
    by_contra hc
    have := hG.forward hA hab.1 (fun _ => hc)
    have hn := hneg.2
    simp only [prevPhi, yr] at hn
    simp only [Nat.add_sub_cancel] at hc
    linarith

/-- **Proposition 4, deterministic part.** If the decompositions behave, the potential of the last
level makes all kept arcs nonnegative. -/
theorem Good.levPhi_last {a b : V} (hab : kept a b) :
    0 ≤ ys a b + levPhi n L R t kept ys idx L 0 a - levPhi n L R t kept ys idx L 0 b :=
  hG.forward (hG.levels L le_rfl 0 (Nat.zero_le _)) hab fun h => absurd h (lt_irrefl L)

end Levels

end SsspFlow.Congest
