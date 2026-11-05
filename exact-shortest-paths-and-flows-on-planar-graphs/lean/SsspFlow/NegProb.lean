import SsspFlow.NegScale

/-!
# The failure probability: Proposition 4 of `notes/NEGATIVE.md`, the probabilistic part

`pcount p` is the number of strings with property `p`. Fixing one coordinate of a product leaves the
others free (`pcount_update`, `pcount_eval`), independent coordinates multiply (`pcount_forall`), and
large values are rare (`pcount_markov`). In a phase, the strings `y ℓ r` give the decompositions
(`idxOf`). The phase is bad (`PhaseBad`) if a decomposition below level `L` puts far nodes into one
cluster, or if a least walk in a cluster is cut more than `t` times in every repetition of the level
below. Outside bad phases the decompositions behave (`decOK_of`), and then all arcs end up
nonnegative (`pos_of_noBad`). Bad phases are rare (`phaseBad_count`), also among all phases, where
each phase depends on the strings of the phases before it (`anyBad_count`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal
open Cslib.Congest

namespace SsspFlow.Congest

/-! ### Counting -/

section Count

/-- The number of elements with a property. -/
noncomputable def pcount {X : Type} [Fintype X] (p : X → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter p).card

variable {X : Type} [Fintype X]

theorem pcount_eq (p : X → Prop) [DecidablePred p] : pcount p = (Finset.univ.filter p).card := by
  unfold pcount
  congr

open Classical in
theorem pcount_eq_sum (p : X → Prop) : pcount p = ∑ x, if p x then 1 else 0 := by
  rw [pcount_eq, Finset.card_filter]

theorem pcount_le (p : X → Prop) : pcount p ≤ Fintype.card X := by
  classical
  rw [pcount_eq]
  exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ

theorem pcount_mono {p q : X → Prop} (h : ∀ x, p x → q x) : pcount p ≤ pcount q := by
  classical
  rw [pcount_eq, pcount_eq]
  exact Finset.card_le_card fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact h x hx

theorem pcount_false : pcount (fun _ : X => False) = 0 := by
  classical
  rw [pcount_eq]
  simp

theorem pcount_or (p q : X → Prop) : pcount (fun x => p x ∨ q x) ≤ pcount p + pcount q := by
  classical
  rw [pcount_eq, pcount_eq, pcount_eq]
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
  exact hx

theorem pcount_exists {ι : Type} [Fintype ι] (p : ι → X → Prop) :
    pcount (fun x => ∃ i, p i x) ≤ ∑ i, pcount (p i) := by
  classical
  rw [pcount_eq]
  simp only [pcount_eq]
  refine (Finset.card_le_card ?_).trans Finset.card_biUnion_le
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hx ⊢
  exact hx

/-- **Markov's inequality.** -/
theorem pcount_markov (f : X → ℕ) (t : ℕ) : pcount (fun x => t < f x) * (t + 1) ≤ ∑ x, f x := by
  classical
  rw [pcount_eq]
  calc (Finset.univ.filter fun x => t < f x).card * (t + 1)
      = ∑ _x ∈ Finset.univ.filter (fun x => t < f x), (t + 1) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ x ∈ Finset.univ.filter (fun x => t < f x), f x := Finset.sum_le_sum fun x hx => by
        simp only [Finset.mem_filter] at hx
        omega
    _ ≤ ∑ x, f x := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- **Fixing one coordinate.** If every choice of the other coordinates leaves at most `M / D` values
of coordinate `j` with property `E`, then `E` holds for at most a fraction `M / (D |Y|)`. -/
theorem pcount_update {ι Y : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] (j : ι)
    (E : (ι → Y) → Prop) {D M : ℕ} (h : ∀ ω, pcount (fun y => E (Function.update ω j y)) * D ≤ M) :
    pcount E * Fintype.card Y * D ≤ M * Fintype.card (ι → Y) := by
  classical
  have key : ∑ ω : ι → Y, pcount (fun y => E (Function.update ω j y)) =
      pcount E * Fintype.card Y := by
    simp only [pcount_eq_sum]
    let e : (ι → Y) × Y ≃ (ι → Y) × Y :=
      { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
        invFun := fun p => (Function.update p.1 j p.2, p.1 j)
        left_inv := fun p => by simp
        right_inv := fun p => by simp }
    have h₁ := e.sum_comp (fun p => if E p.1 then 1 else 0)
    have h₂ : ∑ p : (ι → Y) × Y, (if E (e p).1 then 1 else 0) =
        ∑ ω : ι → Y, ∑ y : Y, if E (Function.update ω j y) then 1 else 0 :=
      Fintype.sum_prod_type _
    rw [← h₂, h₁, Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ω _ => ?_
    show (∑ _y : Y, if E ω then 1 else 0) = _
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  calc pcount E * Fintype.card Y * D
      = ∑ ω : ι → Y, pcount (fun y => E (Function.update ω j y)) * D := by
        rw [← Finset.sum_mul, key]
    _ ≤ ∑ _ω : ι → Y, M := Finset.sum_le_sum fun ω _ => h ω
    _ = M * Fintype.card (ι → Y) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- A property of one coordinate has the same frequency in the product. -/
theorem pcount_eval {ι Y : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] [Nonempty Y] (j : ι)
    {P : Y → Prop} {D : ℕ} (h : pcount P * D ≤ Fintype.card Y) :
    pcount (fun ω : ι → Y => P (ω j)) * D ≤ Fintype.card (ι → Y) := by
  have h₁ := pcount_update j (fun ω : ι → Y => P (ω j)) (D := D) (M := Fintype.card Y)
    fun ω => by simpa using h
  have hY : 0 < Fintype.card Y := Fintype.card_pos
  refine Nat.le_of_mul_le_mul_right (c := Fintype.card Y) ?_ hY
  calc pcount (fun ω : ι → Y => P (ω j)) * D * Fintype.card Y
      = pcount (fun ω : ι → Y => P (ω j)) * Fintype.card Y * D := by ring
    _ ≤ Fintype.card Y * Fintype.card (ι → Y) := h₁
    _ = Fintype.card (ι → Y) * Fintype.card Y := by ring

/-- **Independent coordinates.** -/
theorem pcount_forall {ι : Type} [Fintype ι] [DecidableEq ι] (P : X → Prop) :
    pcount (fun z : ι → X => ∀ i, P (z i)) = pcount P ^ Fintype.card ι := by
  classical
  rw [pcount_eq, pcount_eq, ← Fintype.card_subtype, ← Fintype.card_subtype,
    Fintype.card_congr (Equiv.subtypePiEquivPi), Fintype.card_pi, Finset.prod_const,
    Finset.card_univ]

/-- The count along a walk is the sum of the counts of its arcs. -/
theorem sum_cnt {V : Type} {adj : V → V → Prop} (cut : X → V → V → Prop) :
    ∀ {a b : V} (P : Walk adj a b), ∑ x, P.cnt (cut x) = P.nwt (fun a b => pcount fun x => cut x a b)
  | _, _, .nil _ => by simp
  | _, _, .cons e P => by
    rw [Walk.nwt_cons, ← sum_cnt cut P, pcount_eq_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Walk.cnt_cons]

theorem nwt_cut_le {V : Type} {adj : V → V → Prop} (c lam : V → V → ℕ) {d M Cq Y : ℕ}
    (h : ∀ a b, adj a b → c a b * (d * M) ≤ (Cq * lam a b * M + d) * Y) :
    ∀ {a b : V} (P : Walk adj a b), P.nwt c * (d * M) ≤ (Cq * P.nwt lam * M + P.len * d) * Y
  | _, _, .nil _ => by simp
  | _, _, .cons e P => by
    have ih := nwt_cut_le c lam h P
    have h₁ := h _ _ e
    simp only [Walk.nwt_cons, Walk.len_cons]
    nlinarith

end Count

/-! ### One phase -/

section Phase

variable {V X : Type} [Fintype V] [DecidableEq V] [Fintype X]

/-- The indices of the decompositions of a phase from its strings `y`; `ix ℓ x` is the index at
level `ℓ` from the string `x`. -/
def idxOf {L R : ℕ} (ix : ℕ → X → V → ℕ) (y : Fin (L + 1) → Fin (R + 1) → X) (ℓ r : ℕ) (v : V) : ℕ :=
  if h : ℓ ≤ L ∧ r ≤ R then ix ℓ (y ⟨ℓ, Nat.lt_succ_of_le h.1⟩ ⟨r, Nat.lt_succ_of_le h.2⟩) v else 0

theorem idxOf_fin {L R : ℕ} (ix : ℕ → X → V → ℕ) (y : Fin (L + 1) → Fin (R + 1) → X)
    (ℓ : Fin (L + 1)) (r : Fin (R + 1)) : idxOf ix y ℓ r = ix ℓ (y ℓ r) := by
  funext v
  unfold idxOf
  rw [dite_eq_left ⟨Nat.le_of_lt_succ ℓ.2, Nat.le_of_lt_succ r.2⟩]

/-- The lengths of the decompositions: the rounded weights on kept arcs, `⊤` elsewhere. -/
noncomputable def lamS (kept : V → V → Prop) (ys : V → V → ℤ) : V → V → ℕ∞ :=
  restrictLen kept (posPart ys)

/-- Equal indices at level `ℓ` from the string `x` are close in both directions. -/
def CloseX (adj : V → V → Prop) (lam : V → V → ℕ∞) (ix : ℕ → X → V → ℕ) (ℓ : ℕ) (x : X) : Prop :=
  ∀ u v, ix ℓ x u = ix ℓ x v →
    dist adj (lenTop lam) Set.univ u v ≤ ((2 ^ (ℓ + 1) : ℕ) : ℝ≥0∞) ∧
      dist adj (lenTop lam) Set.univ v u ≤ ((2 ^ (ℓ + 1) : ℕ) : ℝ≥0∞)

theorem exists_canon (E : V → V → Prop) (ys : V → V → ℤ) (v : V) :
    ∃ a, ∃ P : Walk E a v, P.support.Nodup ∧ (Restr E ys → P.zw ys = wdist E ys v) := by
  by_cases h : Restr E ys
  · obtain ⟨a, P, hP, e⟩ := wdist_spec h v
    exact ⟨a, P, hP, fun _ => e.symm⟩
  · exact ⟨v, .nil v, by simp, fun h' => absurd h' h⟩

/-- The start of the chosen least walk to `v`. -/
noncomputable def canonA (E : V → V → Prop) (ys : V → V → ℤ) (v : V) : V :=
  (exists_canon E ys v).choose

/-- The chosen least walk to `v`, without repeated vertices. -/
noncomputable def canonP (E : V → V → Prop) (ys : V → V → ℤ) (v : V) : Walk E (canonA E ys v) v :=
  (exists_canon E ys v).choose_spec.choose

theorem canonP_spec (E : V → V → Prop) (ys : V → V → ℤ) (v : V) :
    (canonP E ys v).support.Nodup ∧ (Restr E ys → (canonP E ys v).zw ys = wdist E ys v) :=
  (exists_canon E ys v).choose_spec.choose_spec

variable (adj : V → V → Prop) (L R t : ℕ) (kept : V → V → Prop) (ys : V → V → ℤ)
  (ix : ℕ → X → V → ℕ)

/-- Far nodes with equal index, below level `L`. -/
def BadClose (y : Fin (L + 1) → Fin (R + 1) → X) : Prop :=
  ∃ ℓ : Fin (L + 1), ∃ r : Fin (R + 1), (ℓ : ℕ) < L ∧ ¬ CloseX adj (lamS kept ys) ix ℓ (y ℓ r)

/-- At level `ℓ`, the least walk to `v` in its cluster of `(ℓ, r)` is cut more than `t` times in
every repetition of level `ℓ - 1`. -/
def BadCut (y : Fin (L + 1) → Fin (R + 1) → X) (ℓ : Fin (L + 1)) (r : Fin (R + 1)) (v : V) : Prop :=
  Restr kept ys ∧ ((ℓ : ℕ) < L → CloseX adj (lamS kept ys) ix ℓ (y ℓ r)) ∧
    ∀ r' : Fin (R + 1),
      t < (canonP (clArc L kept (idxOf ix y) ℓ r) ys v).cnt (cutArc (idxOf ix y) (ℓ - 1) r')

/-- A bad phase. -/
def PhaseBad (y : Fin (L + 1) → Fin (R + 1) → X) : Prop :=
  BadClose adj L R kept ys ix y ∨
    ∃ ℓ : Fin (L + 1), ∃ r : Fin (R + 1), ∃ v, 1 ≤ (ℓ : ℕ) ∧ BadCut adj L R t kept ys ix y ℓ r v

variable {adj L R t kept ys ix}

/-- Outside a bad phase the decompositions behave. -/
theorem decOK_of (hR : Restr kept ys)
    {y : Fin (L + 1) → Fin (R + 1) → X} (hy : ¬ PhaseBad adj L R t kept ys ix y) :
    DecOK L R t kept ys (idxOf ix y) := by
  have hy₁ : ¬ BadClose adj L R kept ys ix y := fun h => hy (.inl h)
  have hy₂ : ∀ (ℓ : Fin (L + 1)) (r : Fin (R + 1)) v, 1 ≤ (ℓ : ℕ) →
      ¬ BadCut adj L R t kept ys ix y ℓ r v := fun ℓ r v h h' => hy (.inr ⟨ℓ, r, v, h, h'⟩)
  have hclose : ∀ (ℓ : Fin (L + 1)) (r : Fin (R + 1)), (ℓ : ℕ) < L →
      CloseX adj (lamS kept ys) ix ℓ (y ℓ r) := fun ℓ r hℓ => by
    by_contra h
    exact hy₁ ⟨ℓ, r, hℓ, h⟩
  refine ⟨fun ℓ hℓ r hr u v huv => ?_, fun ℓ h1ℓ hℓ r hr v => ?_⟩
  · have hc := hclose ⟨ℓ, by omega⟩ ⟨r, by omega⟩ hℓ
    rw [show ℓ = ((⟨ℓ, by omega⟩ : Fin (L + 1)) : ℕ) from rfl,
      show r = ((⟨r, by omega⟩ : Fin (R + 1)) : ℕ) from rfl, idxOf_fin] at huv
    exact exists_walk_le_of_dist (posPart ys) (hc u v huv).1
  · have hb := hy₂ ⟨ℓ, by omega⟩ ⟨r, by omega⟩ v h1ℓ
    simp only [BadCut, not_and, not_forall, not_lt] at hb
    obtain ⟨r', hr'⟩ := hb hR (fun hlt => hclose ⟨ℓ, by omega⟩ ⟨r, by omega⟩ hlt)
    obtain ⟨-, hmin⟩ := canonP_spec (clArc L kept (idxOf ix y) ℓ r) ys v
    exact ⟨_, canonP _ ys v, hmin (hR.mono fun _ _ h => h.1), r', by omega, hr'⟩

/-- The least walk of a behaving cluster has rounded weight at most `2 ^ (ℓ + 1)`. -/
theorem canon_short (hR : Restr kept ys)
    (hLV : Fintype.card V ≤ 2 ^ (L + 1)) {y : Fin (L + 1) → Fin (R + 1) → X}
    {ℓ : Fin (L + 1)} {r : Fin (R + 1)} (hc : (ℓ : ℕ) < L → CloseX adj (lamS kept ys) ix ℓ (y ℓ r))
    (v : V) : (canonP (clArc L kept (idxOf ix y) ℓ r) ys v).nwt (posPart ys) ≤ 2 ^ ((ℓ : ℕ) + 1) := by
  have hRc : Restr (clArc L kept (idxOf ix y) ℓ r) ys := hR.mono fun _ _ h => h.1
  obtain ⟨hnd, hmin⟩ := canonP_spec (clArc L kept (idxOf ix y) ℓ r) ys v
  set P := canonP (clArc L kept (idxOf ix y) ℓ r) ys v
  have hP0 : P.zw ys ≤ 0 := (hmin hRc).trans_le (wdist_nonpos hRc v)
  have hlift : ∀ a b, clArc L kept (idxOf ix y) ℓ r a b → kept a b := fun _ _ h => h.1
  have hpos := nwt_posPart (y := ys) P
  by_cases hℓ : (ℓ : ℕ) < L
  · have hidx := idx_walk hℓ P
    rw [idxOf_fin] at hidx
    obtain ⟨Q, hQ⟩ := exists_walk_le_of_dist (posPart ys) ((hc hℓ) _ _ hidx).2
    have hs := (short_walk hR (P.lift hlift) (by rwa [Walk.zw_lift]) Q hQ).2
    rw [Walk.zw_lift] at hs
    have : (P.nwt (posPart ys) : ℤ) ≤ ((2 ^ ((ℓ : ℕ) + 1) : ℕ) : ℤ) := by rw [hpos]; exact hs
    exact_mod_cast this
  · have h₁ := Walk.zw_pos_le ys hRc.low P
    have h₂ := Walk.len_lt_card P hnd
    have : (P.nwt (posPart ys) : ℤ) ≤ ((2 ^ ((ℓ : ℕ) + 1) : ℕ) : ℤ) := by
      have hℓL : (ℓ : ℕ) = L := by omega
      have h2L : ((2 ^ ((ℓ : ℕ) + 1) : ℕ) : ℤ) = ((2 ^ (L + 1) : ℕ) : ℤ) := by rw [hℓL]
      rw [hpos, h2L]
      have : ((Fintype.card V : ℕ) : ℤ) ≤ ((2 ^ (L + 1) : ℕ) : ℤ) := by exact_mod_cast hLV
      have : ((P.len : ℕ) : ℤ) < Fintype.card V := by exact_mod_cast h₂
      linarith
    exact_mod_cast this

/-- **One phase.** Bad strings of a phase are rare. -/
theorem phaseBad_count [Nonempty X] {M Cq : ℕ}
    (hM : Fintype.card V ≤ M) (hLV : Fintype.card V ≤ 2 ^ (L + 1)) (ht : t + 1 = 2 * (2 * Cq + 1))
    (hP1 : ∀ ℓ < L, pcount (fun x => ¬ CloseX adj (lamS kept ys) ix ℓ x) * M ≤ Fintype.card X)
    (hP2 : ∀ ℓ < L, ∀ a b, kept a b →
      pcount (fun x => ix ℓ x b < ix ℓ x a) * (2 ^ (ℓ + 1) * M) ≤
        (Cq * posPart ys a b * M + 2 ^ (ℓ + 1)) * Fintype.card X) :
    pcount (PhaseBad adj L R t kept ys ix) * (M * 2 ^ (R + 1)) ≤
      (L + 1) * (R + 1) * (2 ^ (R + 1) + Fintype.card V * M) *
        Fintype.card (Fin (L + 1) → Fin (R + 1) → X) := by
  classical
  set Y := Fin (L + 1) → Fin (R + 1) → X
  set Z := Fin (R + 1) → X
  have hZ : 0 < Fintype.card Z := Fintype.card_pos
  -- far nodes in one cluster
  have hA : pcount (BadClose adj L R kept ys ix) * M ≤ (L + 1) * (R + 1) * Fintype.card Y := by
    have h₁ : pcount (BadClose adj L R kept ys ix) ≤
        ∑ ℓ : Fin (L + 1), ∑ r : Fin (R + 1),
          pcount (fun y : Y => (ℓ : ℕ) < L ∧ ¬ CloseX adj (lamS kept ys) ix ℓ (y ℓ r)) :=
      (pcount_exists _).trans (Finset.sum_le_sum fun ℓ _ => pcount_exists _)
    have h₂ : ∀ (ℓ : Fin (L + 1)) (r : Fin (R + 1)),
        pcount (fun y : Y => (ℓ : ℕ) < L ∧ ¬ CloseX adj (lamS kept ys) ix ℓ (y ℓ r)) * M ≤
          Fintype.card Y := fun ℓ r => by
      by_cases hℓ : (ℓ : ℕ) < L
      · have hz : pcount (fun z : Z => ¬ CloseX adj (lamS kept ys) ix ℓ (z r)) * M ≤ Fintype.card Z :=
          pcount_eval r (hP1 ℓ hℓ)
        have hy := pcount_eval (ι := Fin (L + 1)) (Y := Z) ℓ hz
        refine le_trans ?_ hy
        exact Nat.mul_le_mul_right _ (pcount_mono fun y h => h.2)
      · rw [show (fun y : Y => (ℓ : ℕ) < L ∧ ¬ CloseX adj (lamS kept ys) ix ℓ (y ℓ r)) =
          fun _ => False from funext fun y => by simp [hℓ], pcount_false]
        simp
    calc pcount (BadClose adj L R kept ys ix) * M
        ≤ (∑ ℓ : Fin (L + 1), ∑ r : Fin (R + 1),
            pcount (fun y : Y => (ℓ : ℕ) < L ∧ ¬ CloseX adj (lamS kept ys) ix ℓ (y ℓ r))) * M :=
          Nat.mul_le_mul_right _ h₁
      _ ≤ ∑ _ℓ : Fin (L + 1), ∑ _r : Fin (R + 1), Fintype.card Y := by
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun ℓ _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun r _ => h₂ ℓ r
      _ = (L + 1) * (R + 1) * Fintype.card Y := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring
  -- least walks cut in every repetition
  have hB : ∀ (ℓ : Fin (L + 1)) (r : Fin (R + 1)) (v : V), 1 ≤ (ℓ : ℕ) →
      pcount (fun y : Y => BadCut adj L R t kept ys ix y ℓ r v) * 2 ^ (R + 1) ≤ Fintype.card Y := by
    intro ℓ r v h1
    set ℓ' : Fin (L + 1) := ⟨ℓ - 1, by omega⟩
    have hne : ℓ ≠ ℓ' := fun h => by
      have := congrArg Fin.val h
      simp [ℓ'] at this
      omega
    have hfix : ∀ (y : Y) (z : Z), pcount (fun z : Z => BadCut adj L R t kept ys ix
        (Function.update y ℓ' z) ℓ r v) * 2 ^ (R + 1) ≤ Fintype.card Z := by
      intro y _
      -- the cluster of `(ℓ, r)` does not see the row `ℓ - 1`
      have hrow : (Function.update y ℓ' · ℓ) = fun _ : Z => y ℓ := funext fun z =>
        Function.update_of_ne hne _ _
      have hcl : ∀ z : Z, clArc L kept (idxOf ix (Function.update y ℓ' z)) ℓ r =
          clArc L kept (idxOf ix y) ℓ r := fun z => by
        funext a b
        simp only [clArc, idxOf_fin, Function.update_of_ne hne]
      have hcut : ∀ (z : Z) (r' : Fin (R + 1)),
          cutArc (idxOf ix (Function.update y ℓ' z)) (ℓ - 1) r' =
            fun a b => ix (ℓ - 1) (z r') b < ix (ℓ - 1) (z r') a := fun z r' => by
        have : idxOf ix (Function.update y ℓ' z) (ℓ - 1) r' = ix (ℓ - 1) (z r') := by
          rw [show (ℓ : ℕ) - 1 = ((ℓ' : Fin (L + 1)) : ℕ) from rfl, idxOf_fin,
            Function.update_self]
        funext a b
        simp only [cutArc, this]
      set P := canonP (clArc L kept (idxOf ix y) ℓ r) ys v
      set A : X → Prop := fun x => t < P.cnt (fun a b => ix (ℓ - 1) x b < ix (ℓ - 1) x a)
      by_cases hg : Restr kept ys ∧ ((ℓ : ℕ) < L → CloseX adj (lamS kept ys) ix ℓ (y ℓ r))
      · have hsub : ∀ z : Z, BadCut adj L R t kept ys ix (Function.update y ℓ' z) ℓ r v →
            ∀ r', A (z r') := fun z hz r' => by
          have h3 := hz.2.2 r'
          rw [hcl z, hcut z r'] at h3
          exact h3
        -- each repetition fails with probability at most one half
        have hAx : pcount A * 2 ≤ Fintype.card X := by
          have hshort := canon_short (L := L) hg.1 hLV hg.2 v
          have hd : 0 < 2 ^ ((ℓ : ℕ) - 1 + 1) * M := by
            have : 0 < M := lt_of_lt_of_le (Fintype.card_pos_iff.2 ⟨v⟩) hM
            positivity
          have hsum := nwt_cut_le (fun a b => pcount fun x => ix (ℓ - 1) x b < ix (ℓ - 1) x a)
            (posPart ys) (d := 2 ^ ((ℓ : ℕ) - 1 + 1)) (M := M) (Cq := Cq) (Y := Fintype.card X)
            (fun a b h => hP2 (ℓ - 1) (by omega) a b h.1) P
          have hmk := pcount_markov (fun x => P.cnt fun a b => ix (ℓ - 1) x b < ix (ℓ - 1) x a) t
          rw [sum_cnt (fun x a b => ix (ℓ - 1) x b < ix (ℓ - 1) x a) P] at hmk
          have hlen : P.len ≤ M := ((Walk.len_lt_card P (canonP_spec _ ys v).1).le).trans hM
          have h2 : 2 ^ ((ℓ : ℕ) + 1) = 2 * 2 ^ ((ℓ : ℕ) - 1 + 1) := by
            rw [show (ℓ : ℕ) + 1 = ((ℓ : ℕ) - 1 + 1) + 1 by omega, pow_succ]
            ring
          rw [h2] at hshort
          set d := 2 ^ ((ℓ : ℕ) - 1 + 1)
          have key : pcount A * 2 * ((2 * Cq + 1) * (d * M)) ≤
              Fintype.card X * ((2 * Cq + 1) * (d * M)) := by
            calc pcount A * 2 * ((2 * Cq + 1) * (d * M))
                = pcount A * (t + 1) * (d * M) := by rw [ht]; ring
              _ ≤ P.nwt (fun a b => pcount fun x => ix (ℓ - 1) x b < ix (ℓ - 1) x a) * (d * M) :=
                  Nat.mul_le_mul_right _ hmk
              _ ≤ (Cq * P.nwt (posPart ys) * M + P.len * d) * Fintype.card X := hsum
              _ ≤ (Cq * (2 * d) * M + M * d) * Fintype.card X := by
                  gcongr
              _ = Fintype.card X * ((2 * Cq + 1) * (d * M)) := by ring
          exact Nat.le_of_mul_le_mul_right key (by positivity)
        calc pcount (fun z : Z => BadCut adj L R t kept ys ix (Function.update y ℓ' z) ℓ r v) *
              2 ^ (R + 1)
            ≤ pcount (fun z : Z => ∀ r', A (z r')) * 2 ^ (R + 1) :=
              Nat.mul_le_mul_right _ (pcount_mono hsub)
          _ = (pcount A * 2) ^ (R + 1) := by
              rw [pcount_forall, Fintype.card_fin, mul_pow]
          _ ≤ Fintype.card X ^ (R + 1) := Nat.pow_le_pow_left hAx _
          _ = Fintype.card Z := by simp [Z]
      · have : (fun z : Z => BadCut adj L R t kept ys ix (Function.update y ℓ' z) ℓ r v) =
            fun _ => False := funext fun z => by
          simp only [eq_iff_iff, iff_false]
          intro hz
          refine hg ⟨hz.1, fun hlt => ?_⟩
          have := hz.2.1 hlt
          rwa [Function.update_of_ne hne] at this
        rw [this, pcount_false]
        simp
    have h₁ := pcount_update (ι := Fin (L + 1)) (Y := Z) ℓ'
      (fun y : Y => BadCut adj L R t kept ys ix y ℓ r v) (D := 2 ^ (R + 1))
      (M := Fintype.card Z) fun y => hfix y (y ℓ')
    refine Nat.le_of_mul_le_mul_right (c := Fintype.card Z) ?_ hZ
    calc pcount (fun y : Y => BadCut adj L R t kept ys ix y ℓ r v) * 2 ^ (R + 1) * Fintype.card Z
        = pcount (fun y : Y => BadCut adj L R t kept ys ix y ℓ r v) * Fintype.card Z *
            2 ^ (R + 1) := by ring
      _ ≤ Fintype.card Z * Fintype.card Y := h₁
      _ = Fintype.card Y * Fintype.card Z := by ring
  have hB' : pcount (fun y : Y => ∃ ℓ : Fin (L + 1), ∃ r : Fin (R + 1), ∃ v, 1 ≤ (ℓ : ℕ) ∧
      BadCut adj L R t kept ys ix y ℓ r v) * 2 ^ (R + 1) ≤
        (L + 1) * (R + 1) * Fintype.card V * Fintype.card Y := by
    have h₁ : pcount (fun y : Y => ∃ ℓ : Fin (L + 1), ∃ r : Fin (R + 1), ∃ v, 1 ≤ (ℓ : ℕ) ∧
        BadCut adj L R t kept ys ix y ℓ r v) ≤
        ∑ ℓ : Fin (L + 1), ∑ r : Fin (R + 1), ∑ v : V,
          pcount (fun y : Y => 1 ≤ (ℓ : ℕ) ∧ BadCut adj L R t kept ys ix y ℓ r v) :=
      (pcount_exists _).trans (Finset.sum_le_sum fun ℓ _ => (pcount_exists _).trans
        (Finset.sum_le_sum fun r _ => pcount_exists _))
    have h₂ : ∀ (ℓ : Fin (L + 1)) (r : Fin (R + 1)) (v : V),
        pcount (fun y : Y => 1 ≤ (ℓ : ℕ) ∧ BadCut adj L R t kept ys ix y ℓ r v) * 2 ^ (R + 1) ≤
          Fintype.card Y := fun ℓ r v => by
      by_cases h1 : 1 ≤ (ℓ : ℕ)
      · exact le_trans (Nat.mul_le_mul_right _ (pcount_mono fun y h => h.2)) (hB ℓ r v h1)
      · rw [show (fun y : Y => 1 ≤ (ℓ : ℕ) ∧ BadCut adj L R t kept ys ix y ℓ r v) =
          fun _ => False from funext fun y => by simp [h1], pcount_false]
        simp
    calc _ ≤ (∑ ℓ : Fin (L + 1), ∑ r : Fin (R + 1), ∑ v : V,
            pcount (fun y : Y => 1 ≤ (ℓ : ℕ) ∧ BadCut adj L R t kept ys ix y ℓ r v)) * 2 ^ (R + 1) :=
          Nat.mul_le_mul_right _ h₁
      _ ≤ ∑ _ℓ : Fin (L + 1), ∑ _r : Fin (R + 1), ∑ _v : V, Fintype.card Y := by
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun ℓ _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun r _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun v _ => h₂ ℓ r v
      _ = (L + 1) * (R + 1) * Fintype.card V * Fintype.card Y := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring
  calc pcount (PhaseBad adj L R t kept ys ix) * (M * 2 ^ (R + 1))
      ≤ (pcount (BadClose adj L R kept ys ix) + pcount (fun y : Y => ∃ ℓ : Fin (L + 1),
          ∃ r : Fin (R + 1), ∃ v, 1 ≤ (ℓ : ℕ) ∧ BadCut adj L R t kept ys ix y ℓ r v)) *
          (M * 2 ^ (R + 1)) := Nat.mul_le_mul_right _ (pcount_or _ _)
    _ = pcount (BadClose adj L R kept ys ix) * M * 2 ^ (R + 1) +
          pcount (fun y : Y => ∃ ℓ : Fin (L + 1), ∃ r : Fin (R + 1), ∃ v, 1 ≤ (ℓ : ℕ) ∧
            BadCut adj L R t kept ys ix y ℓ r v) * 2 ^ (R + 1) * M := by ring
    _ ≤ (L + 1) * (R + 1) * Fintype.card Y * 2 ^ (R + 1) +
          (L + 1) * (R + 1) * Fintype.card V * Fintype.card Y * M := by
        gcongr
    _ = (L + 1) * (R + 1) * (2 ^ (R + 1) + Fintype.card V * M) * Fintype.card Y := by ring

end Phase

/-! ### All phases -/

section Phases

variable {V X : Type} [Fintype V] [DecidableEq V] [Fintype X]

/-- The decompositions of all phases from the strings `ω`. `ixF φ B ℓ x` is the index at level `ℓ`
from the string `x`, for the lengths of a phase with potential `φ` and bound `B`. -/
def decOf {J L R : ℕ} (B₀ : ℕ) (ixF : (V → ℤ) → ℕ → ℕ → X → V → ℕ)
    (ω : Fin J → Fin (L + 1) → Fin (R + 1) → X) (j : ℕ) (φ : V → ℤ) : ℕ → ℕ → V → ℕ :=
  if h : j < J then idxOf (ixF φ (Bseq B₀ j)) (ω ⟨j, h⟩) else fun _ _ _ => 0

variable {adj : V → V → Prop} {n L R t : ℕ} {w : V → V → Option ℤ}

theorem phiS_congr {B₀ : ℕ} {dec dec' : ℕ → (V → ℤ) → ℕ → ℕ → V → ℕ} :
    ∀ {j : ℕ}, (∀ i < j, dec i = dec' i) →
      phiS adj n L R t w B₀ dec j = phiS adj n L R t w B₀ dec' j
  | 0, _ => rfl
  | j + 1, h => by
    show phiNext adj n L R t w (phiS adj n L R t w B₀ dec j) (Bseq B₀ j)
        (dec j (phiS adj n L R t w B₀ dec j)) =
      phiNext adj n L R t w (phiS adj n L R t w B₀ dec' j) (Bseq B₀ j)
        (dec' j (phiS adj n L R t w B₀ dec' j))
    rw [phiS_congr fun i hi => h i (by omega), h j (by omega)]

/-- The potential of a phase does not depend on the strings of that phase or later ones. -/
theorem phiS_update {J B₀ : ℕ} (ixF : (V → ℤ) → ℕ → ℕ → X → V → ℕ)
    (ω : Fin J → Fin (L + 1) → Fin (R + 1) → X) (j : Fin J) (y : Fin (L + 1) → Fin (R + 1) → X) :
    phiS adj n L R t w B₀ (decOf B₀ ixF (Function.update ω j y)) j =
      phiS adj n L R t w B₀ (decOf B₀ ixF ω) j := by
  refine phiS_congr fun i hi => ?_
  funext φ
  unfold decOf
  by_cases h : i < J
  · rw [dite_eq_left h, dite_eq_left h, Function.update_of_ne]
    intro e
    have := congrArg Fin.val e
    simp at this
    omega
  · rw [dite_eq_right h, dite_eq_right h]

/-- **All phases.** The strings with a bad phase are rare. -/
theorem anyBad_count [Nonempty X] {J B₀ M Cq : ℕ} (ixF : (V → ℤ) → ℕ → ℕ → X → V → ℕ)
    (hM : Fintype.card V ≤ M) (hLV : Fintype.card V ≤ 2 ^ (L + 1)) (ht : t + 1 = 2 * (2 * Cq + 1))
    (hP1 : ∀ φ B, ∀ ℓ < L, pcount (fun x => ¬ CloseX adj (lamS (keptS adj n w φ B) (ysc n w φ B))
      (ixF φ B) ℓ x) * M ≤ Fintype.card X)
    (hP2 : ∀ φ B, ∀ ℓ < L, ∀ a b, keptS adj n w φ B a b →
      pcount (fun x => ixF φ B ℓ x b < ixF φ B ℓ x a) * (2 ^ (ℓ + 1) * M) ≤
        (Cq * posPart (ysc n w φ B) a b * M + 2 ^ (ℓ + 1)) * Fintype.card X) :
    pcount (fun ω : Fin J → Fin (L + 1) → Fin (R + 1) → X => ∃ j : Fin J,
      PhaseBad adj L R t (keptS adj n w (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j))
        (ysc n w (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j))
        (ixF (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j)) (ω j)) * (M * 2 ^ (R + 1)) ≤
      J * ((L + 1) * (R + 1) * (2 ^ (R + 1) + Fintype.card V * M)) *
        Fintype.card (Fin J → Fin (L + 1) → Fin (R + 1) → X) := by
  set Y := Fin (L + 1) → Fin (R + 1) → X
  set K := (L + 1) * (R + 1) * (2 ^ (R + 1) + Fintype.card V * M)
  have hY : 0 < Fintype.card Y := Fintype.card_pos
  have hone : ∀ j : Fin J, pcount (fun ω : Fin J → Y =>
      PhaseBad adj L R t (keptS adj n w (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j))
        (ysc n w (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j))
        (ixF (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j)) (ω j)) * (M * 2 ^ (R + 1)) ≤
      K * Fintype.card (Fin J → Y) := by
    intro j
    have h₁ := pcount_update (ι := Fin J) (Y := Y) j (fun ω : Fin J → Y =>
      PhaseBad adj L R t (keptS adj n w (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j))
        (ysc n w (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j))
        (ixF (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j)) (ω j))
      (D := M * 2 ^ (R + 1)) (M := K * Fintype.card Y) fun ω => by
        simp only [phiS_update, Function.update_self]
        exact phaseBad_count hM hLV ht (hP1 _ _) (hP2 _ _)
    refine Nat.le_of_mul_le_mul_right (c := Fintype.card Y) ?_ hY
    calc _ = pcount (fun ω : Fin J → Y =>
          PhaseBad adj L R t (keptS adj n w (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j))
            (ysc n w (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j))
            (ixF (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j)) (ω j)) *
          Fintype.card Y * (M * 2 ^ (R + 1)) := by ring
      _ ≤ K * Fintype.card Y * Fintype.card (Fin J → Y) := h₁
      _ = K * Fintype.card (Fin J → Y) * Fintype.card Y := by ring
  calc _ ≤ (∑ j : Fin J, pcount (fun ω : Fin J → Y =>
        PhaseBad adj L R t (keptS adj n w (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j))
          (ysc n w (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j))
          (ixF (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j)) (ω j))) *
        (M * 2 ^ (R + 1)) := Nat.mul_le_mul_right _ (pcount_exists _)
    _ ≤ ∑ _j : Fin J, K * Fintype.card (Fin J → Y) := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun j _ => hone j
    _ = J * K * Fintype.card (Fin J → Y) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        ring

/-- **No bad phase.** Without negative closed walks, if no phase is bad, all arcs are nonnegative
after the last phase. -/
theorem pos_of_noBad (hcard : Fintype.card V ≤ n)
    (hneg : ∀ a (C : Walk (zArc adj w) a a), 0 ≤ C.zw (zWt w)) (ht : 2 ≤ t) (hL : 1 ≤ L)
    {B₀ : ℕ} (hB₀ : ∀ a b, zArc adj w a b → -(B₀ : ℤ) ≤ xw n w a b)
    (ixF : (V → ℤ) → ℕ → ℕ → X → V → ℕ) (ω : Fin (nPhase B₀) → Fin (L + 1) → Fin (R + 1) → X)
    (hω : ∀ j : Fin (nPhase B₀), ¬ PhaseBad adj L R t
      (keptS adj n w (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j))
      (ysc n w (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j))
      (ixF (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j)) (ω j))
    (a b : V) (hab : zArc adj w a b) :
    0 ≤ yr (xw n w) (phiS adj n L R t w B₀ (decOf B₀ ixF ω) (nPhase B₀)) a b := by
  have hall : ∀ m ≤ nPhase B₀, ∀ j < m, DecOK L R t
      (keptS adj n w (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j))
      (ysc n w (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j))
      (decOf B₀ ixF ω j (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j)) := by
    intro m
    induction m with
    | zero => intro _ j hj; omega
    | succ m ih =>
      intro hm j hj
      rcases Nat.lt_or_ge j m with hjm | hjm
      · exact ih (by omega) j hjm
      · obtain rfl : j = m := by omega
        have hinv := scale_all hcard hneg ht hL hB₀ j (ih (by omega))
        have hR := restr_of_bound hneg hinv
        have hd : decOf B₀ ixF ω j (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) =
            idxOf (ixF (phiS adj n L R t w B₀ (decOf B₀ ixF ω) j) (Bseq B₀ j)) (ω ⟨j, by omega⟩) := by
          unfold decOf
          rw [dite_eq_left (by omega)]
        rw [hd]
        exact decOK_of hR (hω ⟨j, by omega⟩)
  have := scale_all hcard hneg ht hL hB₀ (nPhase B₀) (hall _ le_rfl) a b hab
  rwa [Bseq_nPhase, Nat.cast_zero, neg_zero] at this

end Phases

end SsspFlow.Congest
