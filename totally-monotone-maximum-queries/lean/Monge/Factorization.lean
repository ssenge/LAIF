import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Basic

/-!
# Filtered `γ₂` and its composition lemmas (Section 3 of the notes)

Inputs are strings `x : J → V` in a set `D`. A factorization assigns to each string and query index
a pair of real vectors over a finite index type `I`. It is feasible for a target `A` on `D` when
`A x y = Σ_j Δ_j[x, y] ⟨u_{xj}, v_{yj}⟩` for **all ordered pairs** `x, y ∈ D`. Its cost is the
largest of `Σ_j ‖u_{xj}‖²` and `Σ_j ‖v_{xj}‖²` over `x ∈ D`.

Functions are total on strings and only their values on `D` matter, so restricting to a subdomain
is restricting the set.

Main results: `seqComp` with `seqComp_feasible`, `seqComp_cost` (Lemma A, as a construction),
`orFact` with `orFact_feasible`, `orFact_cost` (Lemma B, as a construction), and the same statements
for `gam`: `gam_seq_le`, `gam_or_le`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace Monge

variable {J V : Type} [Fintype J] [DecidableEq V]

/-- `Δ_j[x, y]`. -/
def delta (j : J) (x y : J → V) : ℝ := if x j = y j then 0 else 1

/-- Vectors `u_{xj}`, `v_{xj}` with coordinates in `I`. -/
structure Factorization (J V I : Type) where
  u : (J → V) → J → I → ℝ
  v : (J → V) → J → I → ℝ

namespace Factorization

variable {I I' : Type} [Fintype I] [Fintype I']

/-- `Σ_j Δ_j[x, y] ⟨u_{xj}, v_{yj}⟩`. -/
def pairing (F : Factorization J V I) (x y : J → V) : ℝ :=
  ∑ j, delta j x y * ∑ i, F.u x j i * F.v y j i

/-- Feasibility: the factorization equals `A` on all ordered pairs of `D`. -/
def Feasible (F : Factorization J V I) (D : Set (J → V)) (A : (J → V) → (J → V) → ℝ) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, F.pairing x y = A x y

/-- `Σ_j ‖u_{xj}‖²`. -/
def rowCost (F : Factorization J V I) (x : J → V) : ℝ := ∑ j, ∑ i, F.u x j i ^ 2

/-- `Σ_j ‖v_{xj}‖²`. -/
def colCost (F : Factorization J V I) (x : J → V) : ℝ := ∑ j, ∑ i, F.v x j i ^ 2

/-- The cost on `D` is at most `a`. -/
def CostLE (F : Factorization J V I) (D : Set (J → V)) (a : ℝ) : Prop :=
  ∀ x ∈ D, F.rowCost x ≤ a ∧ F.colCost x ≤ a

theorem rowCost_nonneg (F : Factorization J V I) (x : J → V) : 0 ≤ F.rowCost x :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

theorem colCost_nonneg (F : Factorization J V I) (x : J → V) : 0 ≤ F.colCost x :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

/-- Direct sum: pairings add and costs add. -/
def add (F : Factorization J V I) (G : Factorization J V I') : Factorization J V (I ⊕ I') where
  u x j := Sum.elim (F.u x j) (G.u x j)
  v x j := Sum.elim (F.v x j) (G.v x j)

theorem pairing_add (F : Factorization J V I) (G : Factorization J V I') (x y : J → V) :
    (F.add G).pairing x y = F.pairing x y + G.pairing x y := by
  simp only [pairing, add, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_add, sum_add_distrib]

theorem rowCost_add (F : Factorization J V I) (G : Factorization J V I') (x : J → V) :
    (F.add G).rowCost x = F.rowCost x + G.rowCost x := by
  simp only [rowCost, add, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sum_add_distrib]

theorem colCost_add (F : Factorization J V I) (G : Factorization J V I') (x : J → V) :
    (F.add G).colCost x = F.colCost x + G.colCost x := by
  simp only [colCost, add, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sum_add_distrib]

/-- Negate the row vectors. -/
def neg (F : Factorization J V I) : Factorization J V I where
  u x j i := - F.u x j i
  v := F.v

theorem pairing_neg (F : Factorization J V I) (x y : J → V) :
    F.neg.pairing x y = - F.pairing x y := by
  simp only [pairing, neg, neg_mul, sum_neg_distrib, mul_neg]

theorem rowCost_neg (F : Factorization J V I) (x : J → V) : F.neg.rowCost x = F.rowCost x := by
  simp only [rowCost, neg, neg_sq]

theorem colCost_neg (F : Factorization J V I) (x : J → V) : F.neg.colCost x = F.colCost x := rfl

section Tagged

variable {E : Type} [Fintype E] [DecidableEq E] {K : E → Type} [∀ e, Fintype (K e)]

/-- Tagging: the vectors of `x` live in the block `t x`, using the factorization of that block.
Vectors of different tags are orthogonal. -/
def tagged (t : (J → V) → E) (F : ∀ e, Factorization J V (K e)) :
    Factorization J V (Σ e, K e) where
  u x j q := if t x = q.1 then (F q.1).u x j q.2 else 0
  v x j q := if t x = q.1 then (F q.1).v x j q.2 else 0

theorem pairing_tagged (t : (J → V) → E) (F : ∀ e, Factorization J V (K e)) (x y : J → V) :
    (tagged t F).pairing x y = if t x = t y then (F (t x)).pairing x y else 0 := by
  have hinner : ∀ j, ∑ q : Σ e, K e, (tagged t F).u x j q * (tagged t F).v y j q =
      if t x = t y then ∑ i, (F (t x)).u x j i * (F (t x)).v y j i else 0 := by
    intro j
    rw [Fintype.sum_sigma]
    simp only [tagged]
    rw [Finset.sum_eq_single (t x)]
    · by_cases h : t x = t y
      · simp [h]
      · simp [h, Ne.symm h]
    · intro e _ he
      simp [Ne.symm he]
    · simp
  unfold pairing
  simp only [hinner]
  split_ifs <;> simp

theorem rowCost_tagged (t : (J → V) → E) (F : ∀ e, Factorization J V (K e)) (x : J → V) :
    (tagged t F).rowCost x = (F (t x)).rowCost x := by
  unfold rowCost
  apply sum_congr rfl
  intro j _
  rw [Fintype.sum_sigma]
  simp only [tagged]
  rw [Finset.sum_eq_single (t x)]
  · simp
  · intro e _ he
    simp [Ne.symm he]
  · simp

theorem colCost_tagged (t : (J → V) → E) (F : ∀ e, Factorization J V (K e)) (x : J → V) :
    (tagged t F).colCost x = (F (t x)).colCost x := by
  unfold colCost
  apply sum_congr rfl
  intro j _
  rw [Fintype.sum_sigma]
  simp only [tagged]
  rw [Finset.sum_eq_single (t x)]
  · simp
  · intro e _ he
    simp [Ne.symm he]
  · simp

end Tagged

/-- The zero factorization. -/
def zero (J V : Type) : Factorization J V Unit where
  u _ _ _ := 0
  v _ _ _ := 0

theorem pairing_zero (x y : J → V) : (zero J V).pairing x y = 0 := by
  simp [pairing, zero]

theorem rowCost_zero (x : J → V) : (zero J V).rowCost x = 0 := by
  simp [rowCost, zero]

theorem colCost_zero (x : J → V) : (zero J V).colCost x = 0 := by
  simp [colCost, zero]

end Factorization

open Factorization

/-- `J - F_f`: the target of `f`, equal to `1` on pairs with different values. -/
def notEq {E : Type} [DecidableEq E] (f : (J → V) → E) (x y : J → V) : ℝ :=
  if f x = f y then 0 else 1

/-- Some factorization of `A` on `D` has cost at most `a`. -/
def GammaLE (D : Set (J → V)) (A : (J → V) → (J → V) → ℝ) (a : ℝ) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (F : Factorization J V I), F.Feasible D A ∧ F.CostLE D a

/-- `γ₂(A|Δ)` on `D`, the infimum of the costs. -/
noncomputable def gamma2 (D : Set (J → V)) (A : (J → V) → (J → V) → ℝ) : ℝ :=
  sInf {a | 0 ≤ a ∧ GammaLE D A a}

/-- `γ(f) = γ₂(J - F_f|Δ)` on `D`. -/
noncomputable def gam {E : Type} [DecidableEq E] (D : Set (J → V)) (f : (J → V) → E) : ℝ :=
  gamma2 D (notEq f)

theorem GammaLE.mono_cost {D : Set (J → V)} {A : (J → V) → (J → V) → ℝ} {a b : ℝ}
    (h : GammaLE D A a) (hab : a ≤ b) : GammaLE D A b := by
  obtain ⟨I, inst, F, hF, hc⟩ := h
  exact ⟨I, inst, F, hF, fun x hx => ⟨(hc x hx).1.trans hab, (hc x hx).2.trans hab⟩⟩

/-- Restriction to a subdomain keeps the same vectors. -/
theorem GammaLE.mono_dom {D D' : Set (J → V)} {A : (J → V) → (J → V) → ℝ} {a : ℝ}
    (h : GammaLE D A a) (hD : D' ⊆ D) : GammaLE D' A a := by
  obtain ⟨I, inst, F, hF, hc⟩ := h
  exact ⟨I, inst, F, fun x hx y hy => hF x (hD hx) y (hD hy), fun x hx => hc x (hD hx)⟩

/-- **Finiteness of `γ`.** For finite alphabets, every function on strings has a factorization: split
each pair evenly over the positions where the two strings differ. So `gam` is an infimum over a
nonempty set. -/
theorem exists_gammaLE [DecidableEq J] [Fintype V] {E : Type} [DecidableEq E] (D : Set (J → V))
    (f : (J → V) → E) : ∃ a, 0 ≤ a ∧ GammaLE D (notEq f) a := by
  classical
  let d : (J → V) → (J → V) → ℝ := fun x y => ∑ j, delta j x y
  let F : Factorization J V ((J → V) × (J → V)) :=
    { u := fun x _ q => if q.1 = x then notEq f q.1 q.2 / d q.1 q.2 else 0
      v := fun y _ q => if q.2 = y then 1 else 0 }
  have hinner : ∀ x y j, ∑ q, F.u x j q * F.v y j q = notEq f x y / d x y := by
    intro x y j
    rw [Finset.sum_eq_single (x, y)]
    · simp [F]
    · rintro ⟨x', y'⟩ _ hne
      simp only [F]
      by_cases h1 : x' = x
      · by_cases h2 : y' = y
        · exact absurd (by rw [h1, h2]) hne
        · simp [h2]
      · simp [h1]
    · simp
  refine ⟨∑ x, (F.rowCost x + F.colCost x), ?_, _, inferInstance, F, ?_, ?_⟩
  · exact sum_nonneg fun x _ => add_nonneg (F.rowCost_nonneg x) (F.colCost_nonneg x)
  · intro x _ y _
    unfold pairing
    simp only [hinner]
    rw [← Finset.sum_mul]
    by_cases hxy : x = y
    · subst hxy
      simp [notEq]
    · have hd : d x y ≠ 0 := by
        obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
        have hpos : 0 < d x y := by
          apply Finset.sum_pos' (fun _ _ => by unfold delta; split_ifs <;> norm_num)
          exact ⟨j, mem_univ _, by simp [delta, hj]⟩
        exact hpos.ne'
      show d x y * (notEq f x y / d x y) = notEq f x y
      field_simp
  · intro x _
    have hle : F.rowCost x + F.colCost x ≤ ∑ x, (F.rowCost x + F.colCost x) :=
      Finset.single_le_sum (f := fun x => F.rowCost x + F.colCost x)
        (fun x _ => add_nonneg (F.rowCost_nonneg x) (F.colCost_nonneg x)) (mem_univ x)
    have h1 := F.rowCost_nonneg x
    have h2 := F.colCost_nonneg x
    exact ⟨by linarith, by linarith⟩

theorem gam_nonneg {E : Type} [DecidableEq E] (D : Set (J → V)) (f : (J → V) → E) : 0 ≤ gam D f :=
  Real.sInf_nonneg fun _ ha => ha.1

theorem gam_le_of_gammaLE {E : Type} [DecidableEq E] {D : Set (J → V)} {f : (J → V) → E} {a : ℝ}
    (ha : 0 ≤ a) (h : GammaLE D (notEq f) a) : gam D f ≤ a :=
  csInf_le ⟨0, fun _ hb => hb.1⟩ ⟨ha, h⟩

/-- Near-optimal factorizations exist. -/
theorem gammaLE_of_pos [DecidableEq J] [Fintype V] {E : Type} [DecidableEq E] (D : Set (J → V))
    (f : (J → V) → E) {ε : ℝ} (hε : 0 < ε) : GammaLE D (notEq f) (gam D f + ε) := by
  obtain ⟨a, ha⟩ := exists_gammaLE D f
  obtain ⟨b, hb, hlt⟩ := exists_lt_of_csInf_lt (s := {a | 0 ≤ a ∧ GammaLE D (notEq f) a}) ⟨a, ha⟩
    (lt_add_of_pos_right _ hε)
  exact hb.2.mono_cost hlt.le

/-- Restriction to a subdomain does not raise `γ`. -/
theorem gam_mono [DecidableEq J] [Fintype V] {E : Type} [DecidableEq E] {D D' : Set (J → V)}
    (f : (J → V) → E) (hD : D' ⊆ D) : gam D' f ≤ gam D f := by
  apply le_of_forall_pos_le_add
  intro ε hε
  exact gam_le_of_gammaLE (add_nonneg (gam_nonneg D f) hε.le) ((gammaLE_of_pos D f hε).mono_dom hD)

/-- `γ` only depends on the values of the function on `D`. -/
theorem gam_congr {E : Type} [DecidableEq E] {D : Set (J → V)} {f g : (J → V) → E}
    (h : ∀ x ∈ D, f x = g x) : gam D f = gam D g := by
  unfold gam gamma2
  congr 1
  ext a
  have hiff : ∀ {I : Type} [Fintype I] (F : Factorization J V I),
      F.Feasible D (notEq f) ↔ F.Feasible D (notEq g) := by
    intro I _ F
    constructor
    · intro hF x hx y hy
      rw [hF x hx y hy]
      simp [notEq, h x hx, h y hy]
    · intro hF x hx y hy
      rw [hF x hx y hy]
      simp [notEq, h x hx, h y hy]
  constructor
  · rintro ⟨h0, I, inst, F, hF, hc⟩
    exact ⟨h0, I, inst, F, (hiff F).mp hF, hc⟩
  · rintro ⟨h0, I, inst, F, hF, hc⟩
    exact ⟨h0, I, inst, F, (hiff F).mpr hF, hc⟩

/-- A function that is constant on `D` has `γ = 0`. -/
theorem gam_const {E : Type} [DecidableEq E] {D : Set (J → V)} {f : (J → V) → E}
    (h : ∀ x ∈ D, ∀ y ∈ D, f x = f y) : gam D f = 0 := by
  apply le_antisymm _ (gam_nonneg D f)
  apply gam_le_of_gammaLE le_rfl
  refine ⟨Unit, inferInstance, zero J V, ?_, ?_⟩
  · intro x hx y hy
    rw [pairing_zero]
    simp [notEq, h x hx y hy]
  · intro x _
    rw [rowCost_zero, colCost_zero]
    exact ⟨le_rfl, le_rfl⟩

/-! ## A single query -/

/-- The factorization of a Boolean function of one position. -/
def bitFact [DecidableEq J] (j₀ : J) (φ : V → Bool) : Factorization J V Bool where
  u x j b := if j = j₀ ∧ φ (x j₀) = b then 1 else 0
  v y j b := if j = j₀ ∧ φ (y j₀) = !b then 1 else 0

/-- A Boolean function of one position has `γ ≤ 1`. -/
theorem gam_bit_le_one [DecidableEq J] (D : Set (J → V)) (j₀ : J) (φ : V → Bool) :
    gam D (fun x => φ (x j₀)) ≤ 1 := by
  apply gam_le_of_gammaLE zero_le_one
  refine ⟨Bool, inferInstance, bitFact j₀ φ, ?_, ?_⟩
  · intro x _ y _
    unfold pairing
    rw [Finset.sum_eq_single j₀]
    · have key : ∀ a b : Bool, ((if a = true then (1 : ℝ) else 0) * (if b = !true then 1 else 0) +
          (if a = false then 1 else 0) * (if b = !false then 1 else 0)) =
          if a = b then 0 else 1 := by
        intro a b
        cases a <;> cases b <;> simp
      simp only [bitFact, true_and, Fintype.sum_bool, notEq, delta]
      by_cases hxy : x j₀ = y j₀
      · simp [hxy]
      · simp only [hxy, ↓reduceIte, one_mul]
        exact key _ _
    · intro j _ hj
      simp [bitFact, hj]
    · simp
  · intro x _
    constructor
    · unfold rowCost
      rw [Finset.sum_eq_single j₀]
      · cases hx : φ (x j₀) <;> simp [bitFact, hx]
      · intro j _ hj
        simp [bitFact, hj]
      · simp
    · unfold colCost
      rw [Finset.sum_eq_single j₀]
      · cases hx : φ (x j₀) <;> simp [bitFact, hx]
      · intro j _ hj
        simp [bitFact, hj]
      · simp

/-! ## Lemma A: sequential composition -/

section LemmaA

variable {E E' : Type} [Fintype E] [DecidableEq E] [Fintype E'] [DecidableEq E']
  {IA : Type} [Fintype IA] {K : E → Type} [∀ a, Fintype (K a)]

/-- The factorization of Lemma A, a direct sum of three parts following
`β = α + (1 - α) β - (1 - β) α`: the factorization of `J - F_A`, the factorizations of the `G_a`
tagged with `A(x)`, and the negated factorization of `J - F_A` tagged with `h(x)`. -/
def seqComp (A : (J → V) → E) (h : (J → V) → E') (FA : Factorization J V IA)
    (FG : ∀ a, Factorization J V (K a)) :
    Factorization J V (IA ⊕ ((Σ a, K a) ⊕ (Σ _ : E', IA))) :=
  FA.add ((tagged A FG).add (tagged h fun _ => FA.neg))

/-- Lemma A, feasibility: for all ordered pairs of `D`. -/
theorem seqComp_feasible {D : Set (J → V)} {A : (J → V) → E} {G : E → (J → V) → E'}
    {h : (J → V) → E'} {FA : Factorization J V IA} {FG : ∀ a, Factorization J V (K a)}
    (hFA : FA.Feasible D (notEq A))
    (hFG : ∀ a, (FG a).Feasible (D ∩ {x | A x = a}) (notEq (G a)))
    (hh : ∀ x ∈ D, h x = G (A x) x) :
    (seqComp A h FA FG).Feasible D (notEq h) := by
  intro x hx y hy
  unfold seqComp
  rw [pairing_add, pairing_add, pairing_tagged, pairing_tagged, pairing_neg, hFA x hx y hy]
  by_cases hA : A x = A y
  · have hxa : x ∈ D ∩ {z | A z = A x} := ⟨hx, rfl⟩
    have hya : y ∈ D ∩ {z | A z = A x} := ⟨hy, hA.symm⟩
    have hG := hFG (A x) x hxa y hya
    rw [ite_eq_left hA, hG]
    have hval : notEq (G (A x)) x y = notEq h x y := by
      simp only [notEq, hh x hx, hh y hy, ← hA]
    rw [hval]
    by_cases hhh : h x = h y
    · simp [notEq, hA, hhh]
    · simp [notEq, hA, hhh]
  · rw [ite_eq_right hA]
    by_cases hhh : h x = h y
    · simp [notEq, hA, hhh]
    · simp [notEq, hA, hhh]

/-- Lemma A, cost: `2 c + b`. -/
theorem seqComp_cost {D : Set (J → V)} {A : (J → V) → E} {h : (J → V) → E'}
    {FA : Factorization J V IA} {FG : ∀ a, Factorization J V (K a)} {c b : ℝ}
    (hFA : FA.CostLE D c) (hFG : ∀ a, (FG a).CostLE (D ∩ {x | A x = a}) b) :
    (seqComp A h FA FG).CostLE D (2 * c + b) := by
  intro x hx
  have hxa : x ∈ D ∩ {z | A z = A x} := ⟨hx, rfl⟩
  have h1 := hFA x hx
  have h2 := hFG (A x) x hxa
  unfold seqComp
  constructor
  · rw [rowCost_add, rowCost_add, rowCost_tagged, rowCost_tagged, rowCost_neg]
    linarith [h1.1, h2.1]
  · rw [colCost_add, colCost_add, colCost_tagged, colCost_tagged, colCost_neg]
    linarith [h1.2, h2.2]

/-- Lemma A on `GammaLE`. -/
theorem gammaLE_seq {D : Set (J → V)} {A : (J → V) → E} {G : E → (J → V) → E'}
    {h : (J → V) → E'} {c b : ℝ} (hA : GammaLE D (notEq A) c)
    (hG : ∀ a, GammaLE (D ∩ {x | A x = a}) (notEq (G a)) b)
    (hh : ∀ x ∈ D, h x = G (A x) x) : GammaLE D (notEq h) (2 * c + b) := by
  obtain ⟨IA, instA, FA, hFA, hcA⟩ := hA
  choose K instK FG hFG hcG using hG
  exact ⟨_, inferInstance, seqComp A h FA FG, seqComp_feasible hFA hFG hh, seqComp_cost hcA hcG⟩

/-- **Lemma A.** `γ(h) ≤ 2 γ(A) + max_a γ(G_a)`, where `b` bounds every `γ(G_a)` on `A⁻¹(a)`. -/
theorem gam_seq_le [DecidableEq J] [Fintype V] {D : Set (J → V)} {A : (J → V) → E}
    {G : E → (J → V) → E'} {h : (J → V) → E'} {b : ℝ}
    (hb : 0 ≤ b) (hG : ∀ a, gam (D ∩ {x | A x = a}) (G a) ≤ b)
    (hh : ∀ x ∈ D, h x = G (A x) x) : gam D h ≤ 2 * gam D A + b := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have h1 := gammaLE_of_pos D A hε3
  have h2 : ∀ a, GammaLE (D ∩ {x | A x = a}) (notEq (G a)) (b + ε / 3) := fun a =>
    (gammaLE_of_pos _ (G a) hε3).mono_cost (by linarith [hG a])
  have h3 := gammaLE_seq h1 h2 hh
  have h4 := gam_nonneg D A
  have hle := gam_le_of_gammaLE (by positivity) h3
  linarith

end LemmaA

/-! ## Lemma B: OR -/

section LemmaB

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : ι → Type} [∀ i, Fintype (K i)]

/-- `OR(x) = ∨_i g_i(x)`. -/
noncomputable def orOf (g : ι → (J → V) → Bool) (x : J → V) : Bool := by
  classical exact decide (∃ i, g i x = true)

theorem orOf_eq_true {g : ι → (J → V) → Bool} {x : J → V} :
    orOf g x = true ↔ ∃ i, g i x = true := by
  simp [orOf]

theorem orOf_eq_false {g : ι → (J → V) → Bool} {x : J → V} :
    orOf g x = false ↔ ∀ i, g i x = false := by
  simp [orOf]

/-- `S = √(Σ a_i²)`. -/
noncomputable def orBound (a : ι → ℝ) : ℝ := √(∑ i, a i ^ 2)

/-- `⊕_i √(a_i) w^i`: the `U` and `W` vectors of the notes. -/
noncomputable def allBlocks (a : ι → ℝ) (w : ∀ i, K i → ℝ) (q : Σ i, K i) : ℝ :=
  √(a q.1) * w q.1 q.2

/-- `a_{i₀}^{-1/2} w^{i₀}` on block `i₀`: the `T` and `V` vectors of the notes. -/
noncomputable def oneBlock (a : ι → ℝ) (i₀ : ι) (w : ∀ i, K i → ℝ) (q : Σ i, K i) : ℝ :=
  if q.1 = i₀ then (√(a q.1))⁻¹ * w q.1 q.2 else 0

/-- `L` and `R` of the notes, in two orthogonal slots (`false` and `true`). The scale `ρ` is `S^{1/2}`
and `sel y` is the chosen index `i(y)` with `g_{i(y)}(y) = 1`.

* `OR(x) = 0`: `L_x = ρ⁻¹ (U_x, 0)`, `R_x = ρ⁻¹ (0, W_x)`.
* `OR(y) = 1`: `L_y = ρ (0, T_y)`, `R_y = ρ (V_y, 0)`. -/
noncomputable def orFact (o : (J → V) → Bool) (sel : (J → V) → ι) (a : ι → ℝ) (ρ : ℝ)
    (F : ∀ i, Factorization J V (K i)) : Factorization J V (Bool × Σ i, K i) where
  u x j q :=
    match o x, q.1 with
    | false, false => ρ⁻¹ * allBlocks a (fun i => (F i).u x j) q.2
    | true, true => ρ * oneBlock a (sel x) (fun i => (F i).u x j) q.2
    | _, _ => 0
  v x j q :=
    match o x, q.1 with
    | false, true => ρ⁻¹ * allBlocks a (fun i => (F i).v x j) q.2
    | true, false => ρ * oneBlock a (sel x) (fun i => (F i).v x j) q.2
    | _, _ => 0

/-- The inner product of `allBlocks` and `oneBlock`. -/
theorem sum_allBlocks_oneBlock (a : ι → ℝ) (i₀ : ι) (ha : 0 < a i₀) (w w' : ∀ i, K i → ℝ) :
    ∑ q : Σ i, K i, allBlocks a w q * oneBlock a i₀ w' q = ∑ k, w i₀ k * w' i₀ k := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single i₀]
  · apply sum_congr rfl
    intro k _
    have hs : √(a i₀) ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
    simp only [allBlocks, oneBlock, ↓reduceIte]
    field_simp
  · intro i _ hi
    simp [oneBlock, hi]
  · simp

/-- The squared norm of `allBlocks`. -/
theorem sum_allBlocks_sq (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (w : ∀ i, K i → ℝ) :
    ∑ q : Σ i, K i, allBlocks a w q ^ 2 = ∑ i, a i * ∑ k, w i k ^ 2 := by
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro k _
  simp only [allBlocks, mul_pow, Real.sq_sqrt (ha i)]

/-- The squared norm of `oneBlock`. -/
theorem sum_oneBlock_sq (a : ι → ℝ) (i₀ : ι) (ha : 0 ≤ a i₀) (w : ∀ i, K i → ℝ) :
    ∑ q : Σ i, K i, oneBlock a i₀ w q ^ 2 = (a i₀)⁻¹ * ∑ k, w i₀ k ^ 2 := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single i₀]
  · rw [Finset.mul_sum]
    apply sum_congr rfl
    intro k _
    simp only [oneBlock, ↓reduceIte, mul_pow, inv_pow, Real.sq_sqrt ha]
  · intro i _ hi
    simp [oneBlock, hi]
  · simp

/-- The inner products of `orFact`, before summing over `j`. -/
theorem orFact_inner (o : (J → V) → Bool) (sel : (J → V) → ι) (a : ι → ℝ) {ρ : ℝ} (hρ : ρ ≠ 0)
    (F : ∀ i, Factorization J V (K i)) (x y : J → V) (j : J)
    (hy : o x = false → o y = true → 0 < a (sel y))
    (hx : o x = true → o y = false → 0 < a (sel x)) :
    ∑ q, (orFact o sel a ρ F).u x j q * (orFact o sel a ρ F).v y j q =
      if o x = o y then 0
      else if o x = false then ∑ k, (F (sel y)).u x j k * (F (sel y)).v y j k
      else ∑ k, (F (sel x)).u x j k * (F (sel x)).v y j k := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  cases h1 : o x <;> cases h2 : o y
  · simp [orFact, h1, h2]
  · have := sum_allBlocks_oneBlock a (sel y) (hy h1 h2) (fun i => (F i).u x j) (fun i => (F i).v y j)
    simp only [orFact, h1, h2, mul_zero, sum_const_zero, zero_add, Bool.false_eq_true, ↓reduceIte]
    rw [← this]
    apply sum_congr rfl
    intro q _
    field_simp
  · have := sum_allBlocks_oneBlock a (sel x) (hx h1 h2) (fun i => (F i).v y j) (fun i => (F i).u x j)
    simp only [orFact, h1, h2, mul_zero, sum_const_zero, add_zero, Bool.true_eq_false, ↓reduceIte]
    have h3 : ∑ k, (F (sel x)).u x j k * (F (sel x)).v y j k =
        ∑ k, (F (sel x)).v y j k * (F (sel x)).u x j k :=
      sum_congr rfl fun _ _ => mul_comm _ _
    rw [h3, ← this]
    apply sum_congr rfl
    intro q _
    field_simp
  · simp [orFact, h1, h2]

/-- Lemma B, feasibility, for all ordered pairs of `D`. -/
theorem orFact_feasible {D : Set (J → V)} {g : ι → (J → V) → Bool} {sel : (J → V) → ι} {a : ι → ℝ}
    {ρ : ℝ} (hρ : ρ ≠ 0) {F : ∀ i, Factorization J V (K i)}
    (hF : ∀ i, (F i).Feasible D (notEq (g i)))
    (hsel : ∀ y ∈ D, orOf g y = true → g (sel y) y = true)
    (hpos : ∀ y ∈ D, orOf g y = true → 0 < a (sel y)) :
    (orFact (orOf g) sel a ρ F).Feasible D (notEq (orOf g)) := by
  intro x hx y hy
  unfold pairing
  have hinner := fun j => orFact_inner (orOf g) sel a hρ F x y j
    (fun _ h2 => hpos y hy h2) (fun h1 _ => hpos x hx h1)
  simp only [hinner]
  cases h1 : orOf g x <;> cases h2 : orOf g y
  · simp [notEq, h1, h2]
  · -- `OR(x) = 0`, `OR(y) = 1`: the chosen `g_{i(y)}` separates them
    have hgy := hsel y hy h2
    have hgx := orOf_eq_false.mp h1 (sel y)
    have := hF (sel y) x hx y hy
    unfold pairing at this
    simp only [notEq, hgx, hgy, h1, h2, Bool.false_eq_true, ↓reduceIte] at this ⊢
    exact this
  · -- `OR(x) = 1`, `OR(y) = 0`: the reversed order, which uses the same factorization
    have hgx := hsel x hx h1
    have hgy := orOf_eq_false.mp h2 (sel x)
    have := hF (sel x) x hx y hy
    unfold pairing at this
    simp only [notEq, hgx, hgy, h1, h2, Bool.true_eq_false, ↓reduceIte] at this ⊢
    exact this
  · simp [notEq, h1, h2]

/-- Lemma B, cost: every squared norm is at most `S`. -/
theorem orFact_cost {D : Set (J → V)} {g : ι → (J → V) → Bool} {sel : (J → V) → ι} {a : ι → ℝ}
    {F : ∀ i, Factorization J V (K i)} (ha : ∀ i, 0 ≤ a i)
    (hc : ∀ i, (F i).CostLE D (a i))
    (hpos : ∀ y ∈ D, orOf g y = true → 0 < a (sel y))
    (hS : 0 < orBound a) :
    (orFact (orOf g) sel a √(orBound a) F).CostLE D (orBound a) := by
  set S := orBound a with hSdef
  set ρ := √S with hρdef
  have hρ2 : ρ ^ 2 = S := Real.sq_sqrt hS.le
  have hρ0 : ρ ≠ 0 := (Real.sqrt_pos.mpr hS).ne'
  have hS2 : S ^ 2 = ∑ i, a i ^ 2 := Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  -- the all-blocks side, for a generic cost function
  have hall : ∀ (w : ∀ i, J → K i → ℝ), (∀ i, ∑ j, ∑ k, w i j k ^ 2 ≤ a i) →
      ∑ j, ∑ q : Σ i, K i, (ρ⁻¹ * allBlocks a (fun i => w i j) q) ^ 2 ≤ S := by
    intro w hw
    have h1 : ∀ j, ∑ q : Σ i, K i, (ρ⁻¹ * allBlocks a (fun i => w i j) q) ^ 2 =
        (ρ ^ 2)⁻¹ * ∑ i, a i * ∑ k, w i j k ^ 2 := by
      intro j
      rw [← sum_allBlocks_sq a ha, Finset.mul_sum]
      apply sum_congr rfl
      intro q _
      rw [mul_pow, inv_pow]
    simp only [h1, ← Finset.mul_sum]
    have h2 : ∑ j, ∑ i, a i * ∑ k, w i j k ^ 2 ≤ S ^ 2 := by
      rw [Finset.sum_comm, hS2]
      apply Finset.sum_le_sum
      intro i _
      rw [← Finset.mul_sum, sq]
      exact mul_le_mul_of_nonneg_left (hw i) (ha i)
    rw [hρ2]
    calc S⁻¹ * ∑ j, ∑ i, a i * ∑ k, w i j k ^ 2 ≤ S⁻¹ * S ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hS.le)
      _ = S := by field_simp
  -- the one-block side
  have hone : ∀ (i₀ : ι) (w : ∀ i, J → K i → ℝ), 0 < a i₀ → ∑ j, ∑ k, w i₀ j k ^ 2 ≤ a i₀ →
      ∑ j, ∑ q : Σ i, K i, (ρ * oneBlock a i₀ (fun i => w i j) q) ^ 2 ≤ S := by
    intro i₀ w hi hw
    have h1 : ∀ j, ∑ q : Σ i, K i, (ρ * oneBlock a i₀ (fun i => w i j) q) ^ 2 =
        ρ ^ 2 * ((a i₀)⁻¹ * ∑ k, w i₀ j k ^ 2) := by
      intro j
      have h := sum_oneBlock_sq a i₀ hi.le (fun i => w i j)
      rw [show ((a i₀)⁻¹ * ∑ k, w i₀ j k ^ 2) = _ from h.symm, Finset.mul_sum]
      apply sum_congr rfl
      intro q _
      rw [mul_pow]
    simp only [h1, ← Finset.mul_sum, hρ2]
    calc S * ((a i₀)⁻¹ * ∑ j, ∑ k, w i₀ j k ^ 2) ≤ S * ((a i₀)⁻¹ * a i₀) := by
          apply mul_le_mul_of_nonneg_left _ hS.le
          exact mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hi.le)
      _ = S := by field_simp
  intro x hx
  unfold rowCost colCost
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  cases h : orOf g x
  · constructor
    · simp only [orFact, h, ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true,
        sum_const_zero, zero_add]
      exact hall (fun i => (F i).u x) fun i => (hc i x hx).1
    · simp only [orFact, h, ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true,
        sum_const_zero, add_zero]
      exact hall (fun i => (F i).v x) fun i => (hc i x hx).2
  · have hi := hpos x hx h
    constructor
    · simp only [orFact, h, ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true,
        sum_const_zero, add_zero]
      exact hone (sel x) (fun i => (F i).u x) hi (hc _ x hx).1
    · simp only [orFact, h, ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true,
        sum_const_zero, zero_add]
      exact hone (sel x) (fun i => (F i).v x) hi (hc _ x hx).2

/-- **Lemma B on `GammaLE`.** `γ(OR) ≤ √(Σ_i a_i²)` when each `g_i` has a factorization of cost
`a_i`. If `OR` is constant on `D` the zero factorization works. Otherwise a chosen `g_{i(y)}` is
not constant on `D`, so its `a_i` is positive and the construction applies. -/
theorem gammaLE_or {D : Set (J → V)} {g : ι → (J → V) → Bool} {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (h : ∀ i, GammaLE D (notEq (g i)) (a i)) : GammaLE D (notEq (orOf g)) (orBound a) := by
  have hS0 : 0 ≤ orBound a := Real.sqrt_nonneg _
  by_cases hmix : ∃ x₀ ∈ D, orOf g x₀ = false
  · by_cases hmix' : ∃ y₀ ∈ D, orOf g y₀ = true
    · obtain ⟨x₀, hx₀, hfalse⟩ := hmix
      obtain ⟨y₀, hy₀, htrue⟩ := hmix'
      obtain ⟨i₀, -⟩ := orOf_eq_true.mp htrue
      have : Nonempty ι := ⟨i₀⟩
      choose K' instK F hF hc using h
      classical
      let sel : (J → V) → ι := fun y =>
        if hy : ∃ i, g i y = true then hy.choose else Classical.arbitrary ι
      have hsel : ∀ y, orOf g y = true → g (sel y) y = true := by
        intro y hy
        have hex := orOf_eq_true.mp hy
        simp only [sel, hex, ↓reduceDIte]
        exact hex.choose_spec
      -- `a_{i(y)} > 0`: otherwise the vectors vanish, but `(x₀, y)` has target `1`
      have hpos : ∀ y ∈ D, orOf g y = true → 0 < a (sel y) := by
        intro y hy hyt
        by_contra hcon
        have hzero : a (sel y) = 0 := le_antisymm (not_lt.mp hcon) (ha _)
        have hu : ∀ j k, (F (sel y)).u x₀ j k = 0 := by
          have hle : (F (sel y)).rowCost x₀ ≤ 0 := by
            have := (hc (sel y) x₀ hx₀).1
            rwa [hzero] at this
          have hsum : (F (sel y)).rowCost x₀ = 0 := le_antisymm hle ((F _).rowCost_nonneg _)
          intro j k
          have h1 := (Finset.sum_eq_zero_iff_of_nonneg
            (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)).mp hsum j (mem_univ j)
          have h2 := (Finset.sum_eq_zero_iff_of_nonneg
            (fun _ _ => sq_nonneg _)).mp h1 k (mem_univ k)
          exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
        have htarget := hF (sel y) x₀ hx₀ y hy
        have hp : (F (sel y)).pairing x₀ y = 0 := by
          simp [pairing, hu]
        rw [hp] at htarget
        have hgy := hsel y hyt
        have hgx := orOf_eq_false.mp hfalse (sel y)
        simp [notEq, hgx, hgy] at htarget
      have hSpos : 0 < orBound a := by
        apply Real.sqrt_pos.mpr
        apply Finset.sum_pos' (fun _ _ => sq_nonneg _)
        exact ⟨sel y₀, mem_univ _, by have := hpos y₀ hy₀ htrue; positivity⟩
      exact ⟨_, inferInstance, orFact (orOf g) sel a √(orBound a) F,
        orFact_feasible (Real.sqrt_pos.mpr hSpos).ne' hF (fun y _ hy => hsel y hy) hpos,
        orFact_cost ha hc hpos hSpos⟩
    · -- `OR = 0` on `D`
      refine ⟨Unit, inferInstance, zero J V, ?_, ?_⟩
      · intro x hx y hy
        have h1 : orOf g x = false := by
          cases hb : orOf g x
          · rfl
          · exact absurd ⟨x, hx, hb⟩ hmix'
        have h2 : orOf g y = false := by
          cases hb : orOf g y
          · rfl
          · exact absurd ⟨y, hy, hb⟩ hmix'
        rw [pairing_zero]
        simp [notEq, h1, h2]
      · intro x _
        rw [rowCost_zero, colCost_zero]
        exact ⟨hS0, hS0⟩
  · -- `OR = 1` on `D`
    refine ⟨Unit, inferInstance, zero J V, ?_, ?_⟩
    · intro x hx y hy
      have h1 : orOf g x = true := by
        cases hb : orOf g x
        · exact absurd ⟨x, hx, hb⟩ hmix
        · rfl
      have h2 : orOf g y = true := by
        cases hb : orOf g y
        · exact absurd ⟨y, hy, hb⟩ hmix
        · rfl
      rw [pairing_zero]
      simp [notEq, h1, h2]
    · intro x _
      rw [rowCost_zero, colCost_zero]
      exact ⟨hS0, hS0⟩

/-- **Lemma B.** `γ(OR) ≤ √(Σ_i γ(g_i)²)`. -/
theorem gam_or_le [DecidableEq J] [Fintype V] (D : Set (J → V)) (g : ι → (J → V) → Bool) :
    gam D (orOf g) ≤ √(∑ i, gam D (g i) ^ 2) := by
  have hcont : Continuous fun ε : ℝ => √(∑ i, (gam D (g i) + ε) ^ 2) := by
    fun_prop
  have hle : ∀ ε : ℝ, 0 < ε → gam D (orOf g) ≤ √(∑ i, (gam D (g i) + ε) ^ 2) := by
    intro ε hε
    apply gam_le_of_gammaLE (Real.sqrt_nonneg _)
    exact gammaLE_or (a := fun i => gam D (g i) + ε)
      (fun i => add_nonneg (gam_nonneg _ _) hε.le) fun i => gammaLE_of_pos D (g i) hε
  have hlim : Filter.Tendsto (fun ε : ℝ => √(∑ i, (gam D (g i) + ε) ^ 2)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (√(∑ i, (gam D (g i) + 0) ^ 2))) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      gam D (orOf g) ≤ √(∑ i, (gam D (g i) + ε) ^ 2) :=
    eventually_nhdsWithin_of_forall fun ε hε => hle ε hε
  have := ge_of_tendsto hlim hev
  simpa using this

/-- The OR of `c` single bits has `γ ≤ √c`, which is the base case of the notes. -/
theorem gam_or_bits_le [DecidableEq J] [Fintype V] (D : Set (J → V)) (w : ι → J) (φ : ι → V → Bool) :
    gam D (orOf fun i x => φ i (x (w i))) ≤ √(Fintype.card ι : ℝ) := by
  refine (gam_or_le D _).trans (Real.sqrt_le_sqrt ?_)
  have h1 : ∀ i, gam D (fun x : J → V => φ i (x (w i))) ^ 2 ≤ 1 := fun i =>
    pow_le_one₀ (gam_nonneg _ _) (gam_bit_le_one D (w i) (φ i))
  calc ∑ i, gam D (fun x : J → V => φ i (x (w i))) ^ 2 ≤ ∑ _i : ι, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = Fintype.card ι := by simp

end LemmaB

end Monge
