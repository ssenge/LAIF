import SsspFlow.Sector

/-!
# Numbers of the tours from the tree

The masses and positions on the tour at the root come from two passes over the tree. A pass up gives the
mass `upS` of the block of each vertex, and a pass down gives the mass `downS` at the first dart of each vertex
(`phi_eq`). The positions on the tour through all darts differ from them by the depth (`pos_tau_eq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SsspFlow

open FourColor

section Unique

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The masses on a cycle are the only numbers with the recursion of `mass_succ`. -/
theorem mass_unique {g : Equiv.Perm D} {T : Finset D} {x z : D} (f : D → ℕ) (h0 : f x = 0)
    (hs : ∀ y, g y ≠ x → f (g y) = f y + ind T (g y)) (hz : fconnect g x z) :
    f z = mass g T x z := by
  have key : ∀ n, n ≤ pos g x z → f ((⇑g)^[n] x) = mass g T x ((⇑g)^[n] x) := by
    intro n
    induction n with
    | zero =>
      intro _
      show f x = mass g T x x
      rw [mass_self, h0]
    | succ n ih =>
      intro hn
      have hne : g ((⇑g)^[n] x) ≠ x := by
        rw [← Function.iterate_succ_apply' g]
        exact iterate_ne_start hz (by omega) hn
      rw [Function.iterate_succ_apply', hs _ hne, mass_succ T (fconnect_iterate _ _ _) hne, ih (by omega)]
  have := key _ le_rfl
  rwa [pos_spec hz] at this

/-- `offBy` looks at `arc` only along the walk. -/
theorem offBy_congr {ψ : Equiv.Perm D} {arc arc' : D → ℕ} {g₀ z : D}
    (h : ∀ w, fconnect ψ g₀ w → arc w = arc' w) : offBy ψ arc g₀ z = offBy ψ arc' g₀ z := by
  unfold offBy
  refine Finset.sum_congr rfl fun j _ => h _ (fconnect_iterate _ _ _)

end Unique

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace RootedTree

variable {V : Type*} [Fintype V] [DecidableEq V] {t : R.RootedTree V}

theorem c0_inj {u u' : V} (hu : u ≠ t.root) (hu' : u' ≠ t.root) (h : t.c0 u = t.c0 u') : u = u' := by
  have h5 : R.rev (t.up u) = R.rev (t.up u') := congrArg Prod.fst h
  exact t.up_inj hu hu' (R.rev_injective h5)

variable (t) in
/-- A digon corner at the parent of a vertex. -/
def IsC0 (y : D × Bool) : Prop := ∃ u, u ≠ t.root ∧ y = t.c0 u

variable (t) in
open Classical in
/-- What a dart adds to the mass at its vertex: a whole block at a child, and `δ` otherwise. -/
noncomputable def incOf (δ : ℕ) (S : V → ℕ) (y : D × Bool) : ℕ :=
  if h : t.IsC0 y then S h.choose else δ

theorem incOf_c0 (δ : ℕ) (S : V → ℕ) {u : V} (hu : u ≠ t.root) : t.incOf δ S (t.c0 u) = S u := by
  classical
  have h : t.IsC0 (t.c0 u) := ⟨u, hu, rfl⟩
  unfold incOf
  rw [dif_pos h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  rw [c0_inj h1 hu h2.symm]

theorem incOf_not {δ : ℕ} {S : V → ℕ} {y : D × Bool} (h : ¬ t.IsC0 y) : t.incOf δ S y = δ := by
  classical
  unfold incOf
  rw [dif_neg h]

theorem incOf_congr {δ : ℕ} {S S' : V → ℕ} {y : D × Bool}
    (h : ∀ u, u ≠ t.root → y = t.c0 u → S u = S' u) : t.incOf δ S y = t.incOf δ S' y := by
  by_cases hy : t.IsC0 y
  · obtain ⟨u, hu, rfl⟩ := hy
    rw [incOf_c0 _ _ hu, incOf_c0 _ _ hu]
    exact h u hu rfl
  · rw [incOf_not hy, incOf_not hy]

variable (t) in
/-- The iteration of the pass up. -/
noncomputable def upIter (δ : ℕ) : ℕ → V → ℕ
  | 0, _ => 0
  | k + 1, v => if v = t.root then 0 else
      2 + offBy R.double.rot (t.incOf δ (upIter δ k)) (t.c1 v) (t.r0 v)

variable (t) in
/-- A bound on the depth. -/
noncomputable def depBd : ℕ := Finset.univ.sup t.dep

theorem dep_le_depBd (v : V) : t.dep v ≤ t.depBd := Finset.le_sup (Finset.mem_univ v)

variable (t) in
/-- The mass of the block of a vertex, from its first dart to its digon corner at the parent. -/
noncomputable def upS (δ : ℕ) (v : V) : ℕ := t.upIter δ (t.depBd + 1) v

/-- On the walk at a vertex, the digon corners lie below children of this vertex. -/
theorem dep_of_walk {v u : V} (hv : v ≠ t.root) {w : D × Bool}
    (hw : fconnect R.double.rot (t.c1 v) w) (hwu : w = t.c0 u) (hu : u ≠ t.root) :
    t.dep u = t.dep v + 1 := by
  have h1 : t.vertM w = v := by
    rw [← (t.vertM_eq_iff _ _).2 hw]
    exact t.vertM_c1 hv
  rw [hwu, t.vertM_c0] at h1
  rw [← h1]
  exact (t.dep_par u hu).symm

theorem upIter_eq (δ : ℕ) : ∀ n k (v : V), t.depBd - t.dep v = n → n < k →
    t.upIter δ k v = t.upS δ v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k v hn hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    unfold upS
    simp only [upIter]
    by_cases hv : v = t.root
    · rw [if_pos hv, if_pos hv]
    rw [if_neg hv, if_neg hv]
    congr 1
    refine offBy_congr fun w hw => incOf_congr fun u hu hwu => ?_
    have hd := dep_of_walk hv hw hwu hu
    have hb := dep_le_depBd (t := t) u
    rw [ih (t.depBd - t.dep u) (by omega) k' u rfl (by omega),
      ih (t.depBd - t.dep u) (by omega) t.depBd u rfl (by omega)]

theorem upS_eq (δ : ℕ) {v : V} (hv : v ≠ t.root) :
    t.upS δ v = 2 + offBy R.double.rot (t.incOf δ (t.upS δ)) (t.c1 v) (t.r0 v) := by
  unfold upS
  simp only [upIter]
  rw [if_neg hv]
  congr 1
  refine offBy_congr fun w hw => incOf_congr fun u hu hwu => ?_
  have hd := dep_of_walk hv hw hwu hu
  have hb := dep_le_depBd (t := t) u
  exact upIter_eq δ _ _ u rfl (by omega)

variable (t) in
/-- The first dart of a vertex on the tour at the root. -/
noncomputable def base (w₀ : D × Bool) (v : V) : D × Bool := if v = t.root then w₀ else t.c1 v

variable (t) in
/-- The iteration of the pass down. -/
noncomputable def downIter (δ : ℕ) (w₀ : D × Bool) : ℕ → V → ℕ
  | 0, _ => 0
  | k + 1, v => if v = t.root then 0 else
      downIter δ w₀ k (t.par v) +
        offBy R.double.rot (t.incOf δ (t.upS δ)) (t.base w₀ (t.par v)) (R.double.rot⁻¹ (t.c0 v)) + 1

variable (t) in
/-- The mass at the first dart of a vertex. -/
noncomputable def downS (δ : ℕ) (w₀ : D × Bool) (v : V) : ℕ := t.downIter δ w₀ (t.depBd + 1) v

theorem downIter_eq (δ : ℕ) (w₀ : D × Bool) : ∀ n k (v : V), t.dep v = n → n < k →
    t.downIter δ w₀ k v = t.downS δ w₀ v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k v hn hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    unfold downS
    simp only [downIter]
    by_cases hv : v = t.root
    · rw [if_pos hv, if_pos hv]
    rw [if_neg hv, if_neg hv]
    have hd := t.dep_par_lt hv
    have hb := dep_le_depBd (t := t) v
    rw [ih (t.dep (t.par v)) (by omega) k' _ rfl (by omega),
      ih (t.dep (t.par v)) (by omega) t.depBd _ rfl (by omega)]

theorem downS_root (δ : ℕ) (w₀ : D × Bool) : t.downS δ w₀ t.root = 0 := by
  unfold downS
  simp [downIter]

theorem downS_eq (δ : ℕ) (w₀ : D × Bool) {v : V} (hv : v ≠ t.root) :
    t.downS δ w₀ v = t.downS δ w₀ (t.par v) +
      offBy R.double.rot (t.incOf δ (t.upS δ)) (t.base w₀ (t.par v)) (R.double.rot⁻¹ (t.c0 v)) + 1 := by
  unfold downS
  simp only [downIter]
  rw [if_neg hv]
  have hd := t.dep_par_lt hv
  have hb := dep_le_depBd (t := t) v
  rw [downIter_eq δ w₀ _ t.depBd _ rfl (by omega)]
  rfl

variable (t) in
/-- The number of a dart from the two passes. -/
noncomputable def numF (δ : ℕ) (w₀ z : D × Bool) : ℕ :=
  t.downS δ w₀ (t.vertM z) +
    offBy R.double.rot (t.incOf δ (t.upS δ)) (t.base w₀ (t.vertM z)) z

variable {w₀ : D × Bool} (h₀ : t.vertM w₀ = t.root) (h₁ : w₀.2 = true)

include h₀ in
theorem vertM_base (v : V) : t.vertM (t.base w₀ v) = v := by
  unfold base
  split_ifs with h
  · rw [h, h₀]
  · exact t.vertM_c1 h

include h₀ in
theorem fconnect_base {v : V} {z : D × Bool} (hz : t.vertM z = v) :
    fconnect R.double.rot (t.base w₀ v) z :=
  (t.vertM_eq_iff _ _).1 ((vertM_base h₀ v).trans hz.symm)

include h₁ in
theorem base_snd (v : V) : (t.base w₀ v).2 = true := by
  unfold base
  split_ifs
  · exact h₁
  · rfl

theorem rot_inv_vertM (z : D × Bool) : t.vertM (R.double.rot⁻¹ z) = t.vertM z := by
  conv_rhs => rw [← perm_apply_inv_self R.double.rot z, t.vertM_rot]

include h₀ in
theorem tourL_r0 {u : V} (hu : u ≠ t.root) : t.tourL {w₀} (t.r0 u) = t.c0 u := by
  have hm : t.c1 u ∈ t.marks {w₀} := (mem_marks_singleton h₀).2 ⟨u, hu, Or.inl rfl⟩
  rw [tourL_singleton, t.rot_r0]
  exact revOn_of_mem (R := R.double.cone {w₀}) (t.marks_revClosed _) hm

include h₀ in
theorem tourL_pre_c0 {u : V} (hu : u ≠ t.root) :
    t.tourL {w₀} (R.double.rot⁻¹ (t.c0 u)) = t.c1 u := by
  have hm : t.c0 u ∈ t.marks {w₀} := (mem_marks_singleton h₀).2 ⟨u, hu, Or.inr rfl⟩
  rw [tourL_singleton, perm_apply_inv_self]
  exact (revOn_of_mem (R := R.double.cone {w₀}) (t.marks_revClosed _) hm).trans (t.rev_c0 u)

include h₀ in
theorem tourL_c0 {u : V} (hu : u ≠ t.root) :
    t.tourL {w₀} (t.c0 u) = R.double.rot (t.c0 u) := by
  rw [tourL_singleton]
  exact revOn_of_not_mem (rot_c0_not_mark hu h₀)

include h₀ in
theorem tourL_plain {y : D × Bool} (hy : R.double.rot y ∉ t.marks {w₀}) :
    t.tourL {w₀} y = R.double.rot y := by
  rw [tourL_singleton]
  exact revOn_of_not_mem hy

include h₀ h₁ in
/-- The numbers from the passes have the recursion of the masses. -/
theorem numF_step {T₀ : Finset (D × Bool)} {δ : ℕ} (hmk : ∀ y ∈ t.marks {w₀}, ind T₀ y = 1)
    (hδ : ∀ y, y ∉ t.marks {w₀} → ind T₀ y = δ) (y : D × Bool) (hy : t.tourL {w₀} y ≠ w₀) :
    t.numF δ w₀ (t.tourL {w₀} y) = t.numF δ w₀ y + ind T₀ (t.tourL {w₀} y) := by
  have hne_base : ∀ {u p : V}, t.c0 u ≠ t.base w₀ p := fun {u p} e => by
    have h1 := base_snd (t := t) h₁ p
    rw [← e] at h1
    simp [c0] at h1
  by_cases hk : R.double.rot y ∈ t.marks {w₀}
  · obtain ⟨u, hu, h | h⟩ := (mem_marks_singleton h₀).1 hk
    · have hyu : y = t.r0 u := R.double.rot.injective (h.trans (t.rot_r0 u).symm)
      subst hyu
      rw [tourL_r0 h₀ hu, hmk _ ((mem_marks_singleton h₀).2 ⟨u, hu, Or.inr rfl⟩)]
      unfold numF
      rw [t.vertM_c0, t.vertM_r0 hu]
      have hc := fconnect_base (w₀ := w₀) h₀ (rot_inv_vertM (t := t) (t.c0 u))
      rw [t.vertM_c0] at hc
      have h1 := offBy_apply (t.incOf δ (t.upS δ)) hc
        (by rw [perm_apply_inv_self]; exact hne_base)
      rw [perm_apply_inv_self, incOf_c0 _ _ hu, upS_eq δ hu] at h1
      rw [h1, downS_eq δ w₀ hu]
      have h2 : t.base w₀ u = t.c1 u := by
        unfold base
        rw [if_neg hu]
      rw [h2]
      omega
    · have hyu : y = R.double.rot⁻¹ (t.c0 u) := by
        rw [← h, perm_inv_apply_self]
      subst hyu
      rw [tourL_pre_c0 h₀ hu, hmk _ ((mem_marks_singleton h₀).2 ⟨u, hu, Or.inl rfl⟩)]
      unfold numF
      rw [t.vertM_c1 hu, rot_inv_vertM, t.vertM_c0, downS_eq δ w₀ hu]
      have h2 : t.base w₀ u = t.c1 u := by
        unfold base
        rw [if_neg hu]
      rw [h2, offBy_self]
  · rw [tourL_plain h₀ hk, hδ _ hk]
    rw [tourL_plain h₀ hk] at hy
    unfold numF
    rw [t.vertM_rot]
    have hc := fconnect_base (w₀ := w₀) h₀ (rfl : t.vertM y = t.vertM y)
    have hb : R.double.rot y ≠ t.base w₀ (t.vertM y) := by
      unfold base
      split_ifs with hr
      · exact hy
      · intro e
        exact hk (e ▸ (mem_marks_singleton h₀).2 ⟨_, hr, Or.inl rfl⟩)
    rw [offBy_apply _ hc hb, incOf_not fun ⟨u, hu, e⟩ =>
      hk (e ▸ (mem_marks_singleton h₀).2 ⟨u, hu, Or.inr rfl⟩)]
    omega

include h₀ h₁ in
/-- **The two passes give the masses on the tour at the root.** -/
theorem phi_eq (hL₀ : t.IsLevel {w₀}) (hR : R.Planar) (hc : R.Connected) {T₀ : Finset (D × Bool)}
    {δ : ℕ} (hmk : ∀ y ∈ t.marks {w₀}, ind T₀ y = 1) (hδ : ∀ y, y ∉ t.marks {w₀} → ind T₀ y = δ)
    (z : D × Bool) : t.numF δ w₀ z = t.phi T₀ w₀ z := by
  refine mass_unique (t.numF δ w₀) ?_ (numF_step h₀ h₁ hmk hδ) (fconnect_tourL_w₀ h₀ h₁ hL₀ hR hc z)
  unfold numF
  rw [h₀, downS_root]
  have : t.base w₀ t.root = w₀ := by
    unfold base
    rw [if_pos rfl]
  rw [this, offBy_self]

open Classical in
variable (t) in
/-- The position of a dart on the tour through all darts, from its position on the tour at the root. -/
noncomputable def numP (w₀ z : D × Bool) : ℕ :=
  if t.IsC0 z then t.phi Finset.univ w₀ (R.double.rot⁻¹ z) + t.dep (t.vertM z) + 1
  else t.phi Finset.univ w₀ z + t.dep (t.vertM z)

theorem isC0_snd {y : D × Bool} (h : t.IsC0 y) : y.2 = false := by
  obtain ⟨u, _, rfl⟩ := h
  rfl

include h₀ h₁ in
/-- **Positions on the tour through all darts.** -/
theorem pos_tau_eq (hL₀ : t.IsLevel {w₀}) (hR : R.Planar) (hc : R.Connected) (z : D × Bool) :
    pos (t.tau w₀) w₀ z = t.numP w₀ z := by
  classical
  have hP : ∀ y, t.tourL {w₀} y ≠ w₀ →
      t.phi Finset.univ w₀ (t.tourL {w₀} y) = t.phi Finset.univ w₀ y + 1 := fun y hy => by
    have := phi_step (T₀ := Finset.univ) h₀ h₁ hL₀ hR hc y hy
    simpa [ind] using this
  have hne_c0 : ∀ u, t.c0 u ≠ w₀ := fun u e => by
    have := h₁
    rw [← e] at this
    simp [c0] at this
  have hcopy : ∀ {y : D × Bool}, y.2 = true → ¬ t.IsC0 y := fun hy h => by
    rw [isC0_snd h] at hy
    simp at hy
  have hkey : t.numP w₀ z = mass (t.tau w₀) Finset.univ w₀ z := by
    refine mass_unique (t.numP w₀) ?_ ?_ (fconnect_tau h₀ h₁ _ _)
    · unfold numP
      rw [if_neg (hcopy h₁), h₀]
      have : t.phi Finset.univ w₀ w₀ = 0 := mass_self _
      rw [this, t.dep_root]
    · intro y hy
      have hind : ind (Finset.univ : Finset (D × Bool)) (t.tau w₀ y) = 1 := by simp [ind]
      rw [hind]
      by_cases hr : ∃ u, u ≠ t.root ∧ y = t.r0 u
      · obtain ⟨u, hu, rfl⟩ := hr
        rw [tau_r0 hu] at hy ⊢
        have h1 : ¬ t.IsC0 (R.double.rot (t.c0 u)) := hcopy rfl
        have h2 : ¬ t.IsC0 (t.r0 u) := fun ⟨x, hx, e⟩ => c0_ne_r0_of_eq hx hu e.symm
        unfold numP
        rw [if_neg h1, if_neg h2, t.vertM_rot, t.vertM_c0, t.vertM_r0 hu]
        have h3 := hP (t.r0 u) (by rw [tourL_r0 h₀ hu]; exact hne_c0 u)
        have h4 := hP (t.c0 u) (by rw [tourL_c0 h₀ hu]; exact hy)
        rw [tourL_r0 h₀ hu] at h3
        rw [tourL_c0 h₀ hu] at h4
        have h5 := t.dep_par u hu
        have h6 : t.dep (t.par u) + 1 = t.dep u := h5
        omega
      by_cases hc0 : t.IsC0 y
      · obtain ⟨u, hu, rfl⟩ := hc0
        rw [tau_c0 hu] at hy ⊢
        have h1 : ¬ t.IsC0 (t.c1 u) := hcopy rfl
        have h2 : t.IsC0 (t.c0 u) := ⟨u, hu, rfl⟩
        unfold numP
        rw [if_neg h1, if_pos h2, t.vertM_c1 hu, t.vertM_c0]
        have h3 := hP (R.double.rot⁻¹ (t.c0 u)) (by rw [tourL_pre_c0 h₀ hu]; exact hy)
        rw [tourL_pre_c0 h₀ hu] at h3
        have h6 : t.dep (t.par u) + 1 = t.dep u := t.dep_par u hu
        omega
      · have hrot : t.tau w₀ y = R.double.rot y := tau_eq_rot h₁ fun v hv =>
          ⟨fun e => hr ⟨v, hv, e⟩, fun e => hc0 ⟨v, hv, e⟩⟩
        rw [hrot] at hy ⊢
        unfold numP
        rw [if_neg hc0, t.vertM_rot]
        by_cases h1 : t.IsC0 (R.double.rot y)
        · rw [if_pos h1, perm_inv_apply_self]
        · have hk : R.double.rot y ∉ t.marks {w₀} := fun hk => by
            obtain ⟨u, hu, h | h⟩ := (mem_marks_singleton h₀).1 hk
            · exact hr ⟨u, hu, R.double.rot.injective (h.trans (t.rot_r0 u).symm)⟩
            · exact h1 ⟨u, hu, h⟩
          rw [if_neg h1]
          have h3 := hP y (by rw [tourL_plain h₀ hk]; exact hy)
          rw [tourL_plain h₀ hk] at h3
          omega
  rw [hkey, mass_univ (fconnect_tau h₀ h₁ _ _)]

end RootedTree

end RotSystem

end SsspFlow
