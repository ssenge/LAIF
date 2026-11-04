import Arborescence.Model

/-!
# Weak duality and the optimality certificate (end of Lemma 2)

`Dual g X y` packages the hypotheses on a family of vertex sets with values `y`:
the sets are nonempty and avoid the root, `y ≥ 0` on non-singletons, and inequality (1) holds for all
edges `(u, v)` with `u ≠ v`, `v ≠ root`.

The nonemptiness is a hypothesis that the README leave implicit, since there every set is a node. Without it
the statement is false: the empty set with `y = 1` satisfies all the other conditions.
-/

set_option linter.unusedSectionVars false

open Finset

namespace Arborescence

variable {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι]

/-- A dual solution: a finite family of nonempty vertex sets without the root, with `y ≥ 0` on sets of at
least two vertices, and inequality (1) of the README for all edges with `u ≠ v`, `v ≠ root`. -/
structure Dual (g : Graph V) (X : ι → Finset V) (y : ι → ℤ) : Prop where
  nonempty : ∀ i, (X i).Nonempty
  root_notMem : ∀ i, g.root ∉ X i
  sign : ∀ i, 2 ≤ (X i).card → 0 ≤ y i
  feas : ∀ u v, u ≠ v → v ≠ g.root → g.adj u v = true →
    ∑ i, (if v ∈ X i ∧ u ∉ X i then y i else 0) ≤ g.w u v

variable {g : Graph V} {p : V → V}

/-- A vertex that is fixed by `p` and is not the root does not reach the root. -/
theorem IsArb.ne_self (hp : IsArb g p) {v : V} (hv : v ≠ g.root) : p v ≠ v := by
  intro h
  obtain ⟨k, hk⟩ := hp.reach v
  have : p^[k] v = v := Function.iterate_fixed h k
  exact hv (this ▸ hk)

/-- Following `p` from a vertex of a set without the root, some edge of the arborescence enters the set. -/
theorem IsArb.exists_entering (hp : IsArb g p) {X : Finset V} (hX : X.Nonempty) (hr : g.root ∉ X) :
    ∃ v ∈ X, p v ∉ X := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := hX
  obtain ⟨k, hk⟩ := hp.reach x
  have : ∀ j : ℕ, p^[j] x ∈ X := by
    intro j
    induction j with
    | zero => simpa using hx
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact hcon _ ih
  exact hr (hk ▸ this k)

/-- The vertices through which the arborescence enters `X`. -/
def enteringSet (p : V → V) (X : Finset V) : Finset V := X.filter fun v => p v ∉ X

theorem IsArb.one_le_entering (hp : IsArb g p) {X : Finset V} (hX : X.Nonempty) (hr : g.root ∉ X) :
    1 ≤ (enteringSet p X).card := by
  obtain ⟨v, hv, hpv⟩ := hp.exists_entering hX hr
  exact Finset.card_pos.mpr ⟨v, by simp [enteringSet, hv, hpv]⟩

theorem IsArb.entering_singleton (hp : IsArb g p) {v : V} (hv : v ≠ g.root) :
    (enteringSet p {v}).card = 1 := by
  have : enteringSet p {v} = {v} := by
    ext x
    simp only [enteringSet, mem_filter, mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro rfl
      exact ⟨rfl, hp.ne_self hv⟩
  simp [this]

/-- The contribution of one dual set: an arborescence enters it at least once, in the signed sense. -/
theorem IsArb.le_mul_entering (hp : IsArb g p) {X : Finset V} (hX : X.Nonempty) (hr : g.root ∉ X)
    {y : ℤ} (hy : 2 ≤ X.card → 0 ≤ y) : y ≤ y * (enteringSet p X).card := by
  by_cases h2 : 2 ≤ X.card
  · have h1 := hp.one_le_entering hX hr
    have : (1 : ℤ) ≤ ((enteringSet p X).card : ℤ) := by exact_mod_cast h1
    nlinarith [hy h2]
  · have hc : X.card = 1 := by
      have := Finset.card_pos.mpr hX
      omega
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
    have hv : v ≠ g.root := fun h => hr (by simp [h])
    simp [hp.entering_singleton hv]

/-- Double counting: the sum over `v ≠ root` of the duals entered by `(p v, v)` is the sum of `y` times
the number of entering edges. -/
theorem sum_dual_eq {X' : ι → Finset V} (hr : ∀ i, g.root ∉ X' i) (y : ι → ℤ) :
    ∑ v ∈ univ.erase g.root, ∑ i, (if v ∈ X' i ∧ p v ∉ X' i then y i else 0)
      = ∑ i, y i * (enteringSet p (X' i)).card := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : enteringSet p (X' i) = (univ.erase g.root).filter fun v => v ∈ X' i ∧ p v ∉ X' i := by
    ext v
    simp only [enteringSet, mem_filter, mem_erase, mem_univ, and_true]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => hr i (h ▸ h1), h1, h2⟩
    · rintro ⟨_, h1, h2⟩
      exact ⟨h1, h2⟩
  rw [hsub, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

/-- **Weak duality.** If `y` is a dual solution, then every arborescence costs at least `Σ y`. -/
theorem weak_duality {X : ι → Finset V} {y : ι → ℤ} (hd : Dual g X y) (hp : IsArb g p) :
    ∑ i, y i ≤ cost g p := by
  calc ∑ i, y i ≤ ∑ i, y i * (enteringSet p (X i)).card :=
        Finset.sum_le_sum fun i _ => hp.le_mul_entering (hd.nonempty i) (hd.root_notMem i) (hd.sign i)
    _ = ∑ v ∈ univ.erase g.root, ∑ i, (if v ∈ X i ∧ p v ∉ X i then y i else 0) :=
        (sum_dual_eq hd.root_notMem y).symm
    _ ≤ cost g p := by
        refine Finset.sum_le_sum fun v hv => ?_
        have hv' : v ≠ g.root := (mem_erase.mp hv).1
        exact hd.feas (p v) v (hp.ne_self hv') hv' (hp.edge v hv')

/-- If some arborescence has cost `Σ y` for a dual solution `y`, then it is a minimum one. -/
theorem isMinArb_of_cost_eq {X : ι → Finset V} {y : ι → ℤ} (hd : Dual g X y) (hp : IsArb g p)
    (hc : cost g p = ∑ i, y i) : IsMinArb g p :=
  ⟨hp, fun _ hq => hc ▸ weak_duality hd hq⟩

/-- **Optimality certificate.** An arborescence that is tight (equality in (1) on its edges), and enters each
set with `y ≠ 0` exactly once, is a minimum one. -/
theorem certificate {X : ι → Finset V} {y : ι → ℤ} (hd : Dual g X y) (hp : IsArb g p)
    (htight : ∀ v, v ≠ g.root → ∑ i, (if v ∈ X i ∧ p v ∉ X i then y i else 0) = g.w (p v) v)
    (honce : ∀ i, y i ≠ 0 → (enteringSet p (X i)).card = 1) : IsMinArb g p := by
  refine isMinArb_of_cost_eq hd hp ?_
  calc cost g p = ∑ v ∈ univ.erase g.root, ∑ i, (if v ∈ X i ∧ p v ∉ X i then y i else 0) :=
        Finset.sum_congr rfl fun v hv => (htight v (mem_erase.mp hv).1).symm
    _ = ∑ i, y i * (enteringSet p (X i)).card := sum_dual_eq hd.root_notMem y
    _ = ∑ i, y i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : y i = 0
        · simp [h]
        · simp [honce i h]

/-- **No arborescence.** If no edge enters a nonempty set without the root, there is no arborescence. -/
theorem no_arb_of_no_entering {X : Finset V} (hX : X.Nonempty) (hr : g.root ∉ X)
    (hno : ∀ u v, v ∈ X → u ∉ X → g.adj u v = false) : ¬ ∃ p, IsArb g p := by
  rintro ⟨p, hp⟩
  obtain ⟨v, hv, hpv⟩ := hp.exists_entering hX hr
  have hv' : v ≠ g.root := fun h => hr (h ▸ hv)
  have := hp.edge v hv'
  rw [hno _ _ hv hpv] at this
  exact Bool.false_ne_true this

/-- A minimum arborescence exists as soon as an arborescence does. -/
theorem exists_isMinArb (h : ∃ p, IsArb g p) : ∃ p, IsMinArb g p := by
  classical
  obtain ⟨p₀, hp₀⟩ := h
  have hne : (univ.filter fun p : V → V => IsArb g p).Nonempty := ⟨p₀, by simp [hp₀]⟩
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image _ (cost g) hne
  refine ⟨p, (mem_filter.mp hp).2, fun q hq => hmin q (by simp [hq])⟩

/-! ## List-indexed duals -/

/-- The sum of the values of a list of pairs that satisfy a predicate on the set. -/
def dsum (D : List (Finset V × ℤ)) (P : Finset V → Prop) [DecidablePred P] : ℤ :=
  ((D.filter fun d => P d.1).map Prod.snd).sum

theorem sum_fin_eq_dsum (D : List (Finset V × ℤ)) (P : Finset V → Prop) [DecidablePred P] :
    ∑ i : Fin D.length, (if P (D.get i).1 then (D.get i).2 else 0) = dsum D P := by
  induction D with
  | nil => simp [dsum]
  | cons a l ih =>
    change ∑ i : Fin (l.length + 1), (if P ((a :: l).get i).1 then ((a :: l).get i).2 else 0) = _
    rw [Fin.sum_univ_succ]
    by_cases h : P a.1
    · simpa [dsum, List.filter_cons, h] using ih
    · simpa [dsum, List.filter_cons, h] using ih

/-- Weak duality for a list of dual pairs, the form that the algorithm produces. -/
theorem weak_duality_list {D : List (Finset V × ℤ)}
    (hne : ∀ d ∈ D, d.1.Nonempty) (hroot : ∀ d ∈ D, g.root ∉ d.1)
    (hsign : ∀ d ∈ D, 2 ≤ d.1.card → 0 ≤ d.2)
    (hfeas : ∀ u v, u ≠ v → v ≠ g.root → g.adj u v = true →
      dsum D (fun Z => v ∈ Z ∧ u ∉ Z) ≤ g.w u v) (hp : IsArb g p) :
    (D.map Prod.snd).sum ≤ cost g p := by
  have hd : Dual g (fun i : Fin D.length => (D.get i).1) (fun i => (D.get i).2) :=
    { nonempty := fun i => hne _ (List.get_mem _ _)
      root_notMem := fun i => hroot _ (List.get_mem _ _)
      sign := fun i => hsign _ (List.get_mem _ _)
      feas := fun u v huv hv ha => by
        have := sum_fin_eq_dsum D (fun Z => v ∈ Z ∧ u ∉ Z)
        exact this.trans_le (hfeas u v huv hv ha) }
  have h := weak_duality hd hp
  have hs : ∑ i : Fin D.length, (D.get i).2 = (D.map Prod.snd).sum := by
    have := sum_fin_eq_dsum D (fun _ => True)
    simpa [dsum] using this
  rwa [hs] at h

end Arborescence
