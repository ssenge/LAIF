import SsspFlow.Tau

/-!
# Masses from the tour of the root

The tour of a level `Γ` runs through a bag along arcs between its corners. Inside an arc it follows the tour
of the single corner at the root, so masses and positions on the tour of the bag are differences of the
numbers `phi` of the tour at the root, plus one offset per corner (`pot_spec`).

The offsets and the bases `phiB` only need what the node of a corner knows about its own darts.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SsspFlow

open FourColor

section MassTools

variable {D : Type*} [Fintype D] [DecidableEq D] {f : Equiv.Perm D} {g x y : D}

/-- One on `T`, zero off `T`. -/
def ind (T : Finset D) (z : D) : ℕ := if z ∈ T then 1 else 0

/-- A step adds the mark of its end. -/
theorem mass_succ (T : Finset D) (hy : fconnect f x y) (hne : f y ≠ x) :
    mass f T x (f y) = mass f T x y + ind T (f y) := by
  classical
  unfold ind
  split_ifs with hT
  · have h1 : T.filter (InArc f x (f y)) = insert (f y) (T.filter (InArc f x y)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert, inArc_succ hy hne w]
      constructor
      · rintro ⟨hw, h | h⟩
        · exact Or.inr ⟨hw, h⟩
        · exact Or.inl h
      · rintro (rfl | ⟨hw, h⟩)
        · exact ⟨hT, Or.inr rfl⟩
        · exact ⟨hw, Or.inl h⟩
    have h2 : f y ∉ T.filter (InArc f x y) := by
      intro h
      obtain ⟨-, -, -, hle⟩ := Finset.mem_filter.1 h
      have := pos_apply hy hne
      omega
    unfold mass
    rw [h1, Finset.card_insert_of_notMem h2]
  · rw [mass_succ_of_not_mem hy hne hT, Nat.add_zero]

/-- The position is the mass of all elements. -/
theorem mass_univ (hy : fconnect f x y) : mass f Finset.univ x y = pos f x y := by
  have key : ∀ n, n ≤ pos f x y → mass f Finset.univ x (f^[n] x) = n := by
    intro n
    induction n with
    | zero =>
      intro _
      exact mass_self _
    | succ n ih =>
      intro hn
      have hne : f (f^[n] x) ≠ x := by
        rw [← Function.iterate_succ_apply' f]
        exact iterate_ne_start hy (by omega) hn
      rw [Function.iterate_succ_apply', mass_succ _ (fconnect_iterate _ _ _) hne, ih (by omega)]
      simp [ind]
  have := key _ le_rfl
  rwa [pos_spec hy] at this

/-- Masses add up along the cycle from a start. -/
theorem mass_add_of_pos_le (T : Finset D) (hx : fconnect f g x) (hy : fconnect f g y)
    (h : pos f g x ≤ pos f g y) : mass f T g y = mass f T g x + mass f T x y := by
  have hxy := connect_trans (fconnect_symm hx) hy
  have hsh := pos_shift hx hy h
  have key : ∀ n, n ≤ pos f x y →
      mass f T g (f^[n] x) = mass f T g x + mass f T x (f^[n] x) := by
    intro n
    induction n with
    | zero =>
      intro _
      simp
    | succ n ih =>
      intro hn
      have hne1 : f (f^[n] x) ≠ x := by
        rw [← Function.iterate_succ_apply' f]
        exact iterate_ne_start hxy (by omega) hn
      have hne2 : f (f^[n] x) ≠ g := by
        have h1 : f (f^[n] x) = f^[n + 1 + pos f g x] g := by
          rw [Function.iterate_add_apply, pos_spec hx, Function.iterate_succ_apply']
        rw [h1]
        exact iterate_ne_start hy (by omega) (by omega)
      have hc : fconnect f x (f^[n] x) := fconnect_iterate _ _ _
      rw [Function.iterate_succ_apply', mass_succ T hc hne1,
        mass_succ T (connect_trans hx hc) hne2, ih (by omega)]
      omega
  have := key _ le_rfl
  rwa [pos_spec hxy] at this

/-- The mass of an arc from the masses from a start of the cycle. -/
def massBy {D : Type*} (m p : D → ℕ) (cyc : ℕ) (x y : D) : ℕ :=
  if p x ≤ p y then m y - m x else cyc - (m x - m y)

theorem mass_eq_massBy (T : Finset D) {m p : D → ℕ}
    (hm : ∀ z, fconnect f g z → m z = mass f T g z) (hp : ∀ z, fconnect f g z → p z = pos f g z)
    (hx : fconnect f g x) (hy : fconnect f g y) :
    mass f T x y = massBy m p (cycMass f T g) x y := by
  unfold massBy
  rw [hp x hx, hp y hy, hm x hx, hm y hy]
  split_ifs with h
  · have := mass_add_of_pos_le T hx hy h
    omega
  · have h1 := mass_add_of_pos_le T hy hx (by omega)
    have hne : x ≠ y := by
      rintro rfl
      exact h le_rfl
    have hxy := connect_trans (fconnect_symm hx) hy
    have h2 := mass_add_mass T hxy hne
    have h3 := cycMass_congr T hx
    omega

/-- The mass of the whole cycle from its last element. -/
theorem cycMass_of_last (T : Finset D) (hy : f y = x) (hxy : fconnect f x y) :
    cycMass f T x = mass f T x y + ind T x := by
  classical
  have key : ∀ w, fconnect f x w ↔ (InArc f x y w ∨ w = x) := fun w => by
    constructor
    · intro h
      by_cases hw : w = x
      · exact Or.inr hw
      · exact Or.inl ⟨h, hw, pos_le_of_last hy hxy w⟩
    · rintro (h | rfl)
      · exact h.1
      · exact fconnect_iterate _ _ 0
  unfold cycMass mass ind
  split_ifs with hx
  · have h1 : T.filter (fconnect f x) = insert x (T.filter (InArc f x y)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert, key]
      constructor
      · rintro ⟨hw, h | rfl⟩
        · exact Or.inr ⟨hw, h⟩
        · exact Or.inl rfl
      · rintro (rfl | ⟨hw, h⟩)
        · exact ⟨hx, Or.inr rfl⟩
        · exact ⟨hw, Or.inl h⟩
    have h2 : x ∉ T.filter (InArc f x y) := fun h => (Finset.mem_filter.1 h).2.2.1 rfl
    rw [h1, Finset.card_insert_of_notMem h2]
  · have h1 : T.filter (fconnect f x) = T.filter (InArc f x y) := by
      ext w
      simp only [Finset.mem_filter, key]
      constructor
      · rintro ⟨hw, h | rfl⟩
        · exact ⟨hw, h⟩
        · exact (hx hw).elim
      · rintro ⟨hw, h⟩
        exact ⟨hw, Or.inl h⟩
    rw [h1, Nat.add_zero]

/-- The sum of `arc` along a cycle of `ψ`, from `g₀` to `z`, without `g₀`. -/
noncomputable def offBy (ψ : Equiv.Perm D) (arc : D → ℕ) (g₀ z : D) : ℕ :=
  ∑ j ∈ Finset.range (pos ψ g₀ z), arc ((⇑ψ)^[j + 1] g₀)

theorem offBy_self (ψ : Equiv.Perm D) (arc : D → ℕ) (g₀ : D) : offBy ψ arc g₀ g₀ = 0 := by
  simp [offBy, pos_self]

theorem offBy_apply {ψ : Equiv.Perm D} (arc : D → ℕ) {g₀ g : D} (h : fconnect ψ g₀ g)
    (hne : ψ g ≠ g₀) : offBy ψ arc g₀ (ψ g) = offBy ψ arc g₀ g + arc (ψ g) := by
  unfold offBy
  rw [pos_apply h hne, Finset.sum_range_succ, Function.iterate_succ_apply', pos_spec h]

end MassTools

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace RootedTree

variable {V : Type*} [Fintype V] [DecidableEq V] {t : R.RootedTree V}

variable (t) in
/-- The digon corner at a vertex of its tree edge. -/
def IsR0 (e : D × Bool) : Prop := ∃ u, u ≠ t.root ∧ e = t.r0 u

variable (t) in
/-- The mass on the tour of the corner at the root. -/
noncomputable def phi (T₀ : Finset (D × Bool)) (w₀ z : D × Bool) : ℕ :=
  mass (t.tourL {w₀}) T₀ w₀ z

open Classical in
variable (t) in
/-- The value of `phi` before the arc that follows the corner `e`. -/
noncomputable def phiB (T₀ T : Finset (D × Bool)) (w₀ e : D × Bool) : ℕ :=
  if t.IsR0 e then t.phi T₀ w₀ (R.double.rot e) - ind T (R.double.rot e) else t.phi T₀ w₀ e

open Classical in
variable (t) in
/-- The mass of the arc that ends at the corner `h`. -/
noncomputable def arcV (Γ T₀ T : Finset (D × Bool)) (w₀ h : D × Bool) : ℕ :=
  if R.double.rot⁻¹ h ∈ Γ then ind T h
  else t.phi T₀ w₀ (R.double.rot⁻¹ h) - t.phiB T₀ T w₀ ((R.double.nodeReturn Γ)⁻¹ h) + ind T h

section Pot

variable {w₀ : D × Bool} {Γ : Finset (D × Bool)}

/-- A trail after the first step. -/
theorem trail_tail {f : Equiv.Perm (D × Bool)} {S : Finset (D × Bool)} {y z : D × Bool}
    (h : Trail f S y z) (hy : y ∉ S) : Trail f S (f y) z := by
  cases h with
  | here h' => exact (hy h').elim
  | step _ h' => exact h'

theorem not_mem_marks_of_mem (hL : t.IsLevel Γ) {y : D × Bool} (hy : y ∈ Γ) : y ∉ t.marks Γ := by
  intro h
  obtain ⟨v, hv, rfl | rfl⟩ := t.mem_marks.1 h
  · exact hv _ hy (t.vertM_c1 (hv.ne_root hL))
  · exact hL.c0_not_mem hv hy

variable (hL : t.IsLevel Γ) (hw : w₀ ∈ Γ) (h₀ : t.vertM w₀ = t.root) (h₁ : w₀.2 = true)

include hL hw h₀ h₁ in
/-- Off the corners, a step of the rotation keeps the next corner on the tour. -/
theorem trail_rot_of_not_mem {z h : D × Bool} (hz : z ∉ Γ) (htr : Trail (t.tau w₀) Γ z h) :
    Trail (t.tau w₀) Γ (R.double.rot z) h := by
  obtain ⟨hb, hdep⟩ := exists_dep_bound t
  have hnext := trail_tail htr hz
  by_cases h1 : ∃ w, w ≠ t.root ∧ z = t.c0 w
  · obtain ⟨w, hw', rfl⟩ := h1
    have hn := np_of_c0_not_mem hL hw' hz
    rw [tau_c0 hw'] at hnext
    obtain ⟨x, hx⟩ := exists_trail (S := Γ) hw (fconnect_tau h₀ h₁ (R.double.rot (t.c0 w)) w₀)
    have h3 := tau_walk h₁ Γ hdep w hw' (free_of_np hL hn) x (by rwa [tau_r0 hw']) _ (t.vertM_c1 hw')
    rwa [hnext.unique h3]
  by_cases h2 : ∃ w, w ≠ t.root ∧ z = t.r0 w
  · obtain ⟨w, hw', rfl⟩ := h2
    have hn := np_of_r0_not_mem hL hw' hz
    exact tau_walk h₁ Γ hdep w hw' (free_of_np hL hn) h hnext _ (by
      rw [t.rot_r0]
      exact t.vertM_c1 hw')
  · rwa [tau_eq_rot h₁ fun v hv => ⟨fun e => h2 ⟨v, hv, e⟩, fun e => h1 ⟨v, hv, e⟩⟩] at hnext

include hL h₀ in
/-- The reversal on the marks, after a step of the rotation off the corners, agrees for the level and for the
single corner, and stays off the corners. -/
theorem hop_spec {k : D × Bool} (hk : k ∉ Γ) (hc : ∀ u, u ≠ t.root → k = t.c1 u → t.NP Γ u) :
    (R.double.cone Γ).revOn (t.marks Γ) k = (R.double.cone {w₀}).revOn (t.marks {w₀}) k ∧
      (R.double.cone Γ).revOn (t.marks Γ) k ∉ Γ ∧
      ∀ u, u ≠ t.root → (R.double.cone Γ).revOn (t.marks Γ) k = t.c1 u → t.NP Γ u := by
  have hrc : R.double.RevClosed (t.marks Γ) := t.marks_revClosed _
  have hrc₀ : R.double.RevClosed (t.marks {w₀}) := t.marks_revClosed _
  by_cases hm₀ : k ∈ t.marks {w₀}
  · obtain ⟨u, hu, h | h⟩ := (mem_marks_singleton h₀).1 hm₀
    · have hn := hc u hu h
      have hm : k ∈ t.marks Γ := t.mem_marks.2 ⟨u, hn, Or.inl h⟩
      rw [show (R.double.cone Γ).revOn (t.marks Γ) k = R.double.rev k from
        revOn_of_mem (R := R.double.cone Γ) hrc hm,
        show (R.double.cone {w₀}).revOn (t.marks {w₀}) k = R.double.rev k from
        revOn_of_mem (R := R.double.cone {w₀}) hrc₀ hm₀, h, t.rev_c1]
      exact ⟨rfl, hL.c0_not_mem hn, fun v _ e => (c1_ne_c0 v u e.symm).elim⟩
    · have hn := np_of_c0_not_mem hL hu (h ▸ hk)
      have hm : k ∈ t.marks Γ := t.mem_marks.2 ⟨u, hn, Or.inr h⟩
      rw [show (R.double.cone Γ).revOn (t.marks Γ) k = R.double.rev k from
        revOn_of_mem (R := R.double.cone Γ) hrc hm,
        show (R.double.cone {w₀}).revOn (t.marks {w₀}) k = R.double.rev k from
        revOn_of_mem (R := R.double.cone {w₀}) hrc₀ hm₀, h, t.rev_c0]
      refine ⟨rfl, hn.not_mem (t.vertM_c1 hu), fun v hv e => ?_⟩
      have := t.up_inj hu hv (congrArg Prod.fst e)
      rwa [← this]
  · have hsub : ({w₀} : Finset (D × Bool)) ⊆ Γ ∨ True := Or.inr trivial
    have hm : k ∉ t.marks Γ := by
      intro h
      obtain ⟨v, hv, h'⟩ := t.mem_marks.1 h
      exact hm₀ ((mem_marks_singleton h₀).2 ⟨v, hv.ne_root hL, h'⟩)
    rw [show (R.double.cone Γ).revOn (t.marks Γ) k = k from revOn_of_not_mem hm,
      show (R.double.cone {w₀}).revOn (t.marks {w₀}) k = k from revOn_of_not_mem hm₀]
    exact ⟨rfl, hk, fun v hv e => hc v hv e⟩

include hL h₀ in
/-- The reversal on the marks keeps the next corner on the tour. -/
theorem trail_hop {k h : D × Bool} (hk : k ∉ Γ) (hc : ∀ u, u ≠ t.root → k = t.c1 u → t.NP Γ u)
    (htr : Trail (t.tau w₀) Γ k h) :
    Trail (t.tau w₀) Γ ((R.double.cone Γ).revOn (t.marks Γ) k) h := by
  have hrc : R.double.RevClosed (t.marks Γ) := t.marks_revClosed _
  by_cases hm : k ∈ t.marks Γ
  · rw [show (R.double.cone Γ).revOn (t.marks Γ) k = R.double.rev k from
      revOn_of_mem (R := R.double.cone Γ) hrc hm]
    obtain ⟨u, hu, h' | h'⟩ := t.mem_marks.1 hm
    · have hu' := hu.ne_root hL
      rw [h', t.rev_c1]
      refine Trail.step (hL.c0_not_mem hu) ?_
      rw [tau_c0 hu']
      rwa [h'] at htr
    · have hu' := hu.ne_root hL
      rw [h', t.rev_c0]
      have := trail_tail htr hk
      rwa [h', tau_c0 hu'] at this
  · rwa [show (R.double.cone Γ).revOn (t.marks Γ) k = k from revOn_of_not_mem hm]

variable (hL₀ : t.IsLevel {w₀}) (hR : R.Planar) (hc : R.Connected)
  {T₀ T : Finset (D × Bool)}

include hL₀ hR hc h₀ h₁ in
/-- The tour of the corner at the root is one cycle. -/
theorem fconnect_tourL_w₀ (y : D × Bool) : fconnect (t.tourL {w₀}) w₀ y := by
  have hS₀ := hL₀.spanForest hR hc
  have hMc := R.double_connected hc
  obtain ⟨x, hx, hxy⟩ := R.double.split_meets hMc ⟨w₀, Finset.mem_singleton_self _⟩ y
  rw [Finset.mem_singleton] at hx
  subst hx
  refine (hS₀.fconnect_tour_iff _ _).2 ((R.double.cone_gcomp_iff _ _ _).2 ?_)
  exact Same.symm hxy

include hL₀ hR hc h₀ h₁ in
theorem phi_step (y : D × Bool) (hy : t.tourL {w₀} y ≠ w₀) :
    t.phi T₀ w₀ (t.tourL {w₀} y) = t.phi T₀ w₀ y + ind T₀ (t.tourL {w₀} y) :=
  mass_succ T₀ (fconnect_tourL_w₀ h₀ h₁ hL₀ hR hc y) hy

variable (hT1 : ∀ y ∈ T, y ∈ T₀)
  (hT : ∀ y, y ∉ Γ → (∀ u, u ≠ t.root → y = t.c1 u → t.NP Γ u) → y ∈ T₀ → y ∈ T)
  (off : D × Bool → ℕ)

include hL hw h₀ h₁ hL₀ hR hc hT1 hT in
/-- One step of the tour of a level. -/
theorem pot_step {y : D × Bool} (my : ℕ) (h1 : y ∈ Γ → my = off y)
    (h2 : y ∉ Γ → ∀ h, Trail (t.tau w₀) Γ y h →
      t.phiB T₀ T w₀ ((R.double.nodeReturn Γ)⁻¹ h) ≤ t.phi T₀ w₀ y ∧
      my + t.phiB T₀ T w₀ ((R.double.nodeReturn Γ)⁻¹ h) =
        off ((R.double.psi Γ)⁻¹ h) + t.phi T₀ w₀ y) :
    (t.tourL Γ y ∈ Γ → my + ind T (t.tourL Γ y) =
        off ((R.double.psi Γ)⁻¹ (t.tourL Γ y)) + t.arcV Γ T₀ T w₀ (t.tourL Γ y)) ∧
      (t.tourL Γ y ∉ Γ → ∀ h, Trail (t.tau w₀) Γ (t.tourL Γ y) h →
        t.phiB T₀ T w₀ ((R.double.nodeReturn Γ)⁻¹ h) ≤ t.phi T₀ w₀ (t.tourL Γ y) ∧
        my + ind T (t.tourL Γ y) + t.phiB T₀ T w₀ ((R.double.nodeReturn Γ)⁻¹ h) =
          off ((R.double.psi Γ)⁻¹ h) + t.phi T₀ w₀ (t.tourL Γ y)) := by
  classical
  have hφ : ∀ y, t.tourL {w₀} y ≠ w₀ →
      t.phi T₀ w₀ (t.tourL {w₀} y) = t.phi T₀ w₀ y + ind T₀ (t.tourL {w₀} y) :=
    phi_step h₀ h₁ hL₀ hR hc
  have hσ₀ := fconnect_tourL_w₀ h₀ h₁ hL₀ hR hc
  have hind : ∀ y, y ∉ Γ → (∀ u, u ≠ t.root → y = t.c1 u → t.NP Γ u) → ind T y = ind T₀ y := by
    intro y h1 h2
    unfold ind
    by_cases h3 : y ∈ T₀
    · rw [if_pos h3, if_pos (hT y h1 h2 h3)]
    · rw [if_neg h3, if_neg fun h4 => h3 (hT1 y h4)]
  have hphi_pos : ∀ y, y ≠ w₀ → ind T y ≤ t.phi T₀ w₀ y := by
    intro y hy
    unfold ind
    split_ifs with hyT
    · have hmem : y ∈ T₀.filter (InArc (t.tourL {w₀}) w₀ y) :=
        Finset.mem_filter.2 ⟨hT1 y hyT, inArc_end (hσ₀ y) hy⟩
      exact Finset.card_pos.2 ⟨y, hmem⟩
    · exact Nat.zero_le _
  have hne_w₀ : ∀ {y}, y ∉ Γ → y ≠ w₀ := fun hy e => hy (e ▸ hw)
  by_cases hyΓ : y ∈ Γ
  · -- a corner
    have hih := h1 hyΓ
    set e := R.double.faceReturn Γ y with he
    have heΓ : e ∈ Γ := (firstReturn_mem_iff _ _ _).2 hyΓ
    have hψ : R.double.psi Γ y = R.double.nodeReturn Γ e := rfl
    have hσ : t.tourL Γ y = (R.double.cone Γ).revOn (t.marks Γ) (R.double.rot e) := rfl
    have htr := trail_tau_rot hL h₁ heΓ
    by_cases hk : R.double.rot e ∈ Γ
    · have ha : R.double.nodeReturn Γ e = R.double.rot e :=
        firstReturn_eq_of_trail _ heΓ (Trail.here hk)
      have hσ2 : t.tourL Γ y = R.double.rot e := by
        rw [hσ]
        exact revOn_of_not_mem (not_mem_marks_of_mem hL hk)
      have hψ2 : R.double.psi Γ y = R.double.rot e := hψ.trans ha
      rw [hσ2]
      refine ⟨fun _ => ?_, fun h' => (h' hk).elim⟩
      have h4 : t.arcV Γ T₀ T w₀ (R.double.rot e) = ind T (R.double.rot e) := by
        unfold arcV
        rw [perm_inv_apply_self]
        exact if_pos heΓ
      have h5 : (R.double.psi Γ)⁻¹ (R.double.rot e) = y := by
        rw [← hψ2, perm_inv_apply_self]
      rw [h4, h5, hih]
    · by_cases hr : t.IsR0 e
      · obtain ⟨u, hu, hue⟩ := hr
        have hnp : ¬ t.NP Γ u := fun hn =>
          hn e heΓ (by rw [hue]; exact t.vertM_r0 hu)
        have hrot : R.double.rot e = t.c1 u := by rw [hue]; rfl
        have hnF : t.c1 u ∉ t.marks Γ := by
          intro h'
          obtain ⟨v, hv, h2 | h2⟩ := t.mem_marks.1 h'
          · have := t.up_inj hu (hv.ne_root hL) (congrArg Prod.fst h2)
            rw [← this] at hv
            exact hnp hv
          · exact c1_ne_c0 _ _ h2
        have hσ2 : t.tourL Γ y = t.c1 u := by
          rw [hσ, hrot]
          exact revOn_of_not_mem hnF
        rw [hσ2]
        rw [hrot] at hk htr
        refine ⟨fun h' => (hk h').elim, fun _ h' htr' => ?_⟩
        have hh : h' = R.double.nodeReturn Γ e := htr'.unique htr
        have hinv : (R.double.nodeReturn Γ)⁻¹ h' = e := by
          rw [hh, perm_inv_apply_self]
        have hinv2 : (R.double.psi Γ)⁻¹ h' = y := by
          rw [hh, ← hψ, perm_inv_apply_self]
        have hb : t.phiB T₀ T w₀ e = t.phi T₀ w₀ (t.c1 u) - ind T (t.c1 u) := by
          unfold phiB
          rw [if_pos ⟨u, hu, hue⟩, hrot]
        rw [hinv, hinv2, hb]
        have hp := hphi_pos (t.c1 u) (hne_w₀ hk)
        exact ⟨Nat.sub_le _ _, by omega⟩
      · have hcond : ∀ u, u ≠ t.root → R.double.rot e = t.c1 u → t.NP Γ u := fun u hu h' =>
          (hr ⟨u, hu, R.double.rot.injective (h'.trans (t.rot_r0 u).symm)⟩).elim
        obtain ⟨h1', h2', h3'⟩ := hop_spec hL h₀ hk hcond
        have hσ₀e : t.tourL {w₀} e = t.tourL Γ y := by
          rw [tourL_singleton, hσ, h1']
        rw [hσ]
        refine ⟨fun h' => (h2' h').elim, fun _ h' htr' => ?_⟩
        have hh : h' = R.double.nodeReturn Γ e :=
          htr'.unique (trail_hop hL h₀ hk hcond htr)
        have hinv : (R.double.nodeReturn Γ)⁻¹ h' = e := by
          rw [hh, perm_inv_apply_self]
        have hinv2 : (R.double.psi Γ)⁻¹ h' = y := by
          rw [hh, ← hψ, perm_inv_apply_self]
        have hb : t.phiB T₀ T w₀ e = t.phi T₀ w₀ e := by
          unfold phiB
          rw [if_neg hr]
        rw [hinv, hinv2, hb]
        have hne₀ : t.tourL {w₀} e ≠ w₀ := by
          rw [hσ₀e, hσ]
          exact hne_w₀ h2'
        have hp := hφ e hne₀
        rw [hσ₀e, hσ] at hp
        have hi := hind _ h2' h3'
        exact ⟨by omega, by omega⟩
  · -- off the corners
    obtain ⟨h', htr⟩ := exists_trail (S := Γ) hw (fconnect_tau h₀ h₁ y w₀)
    obtain ⟨hih1, hih2⟩ := h2 hyΓ h' htr
    have hσ : t.tourL Γ y = (R.double.cone Γ).revOn (t.marks Γ) (R.double.rot y) := by
      show (R.double.cone Γ).revOn (t.marks Γ) ((R.double.cone Γ).rot y) = _
      rw [R.double.cone_rot_of_not_mem hyΓ]
    have htr2 := trail_rot_of_not_mem hL hw h₀ h₁ hyΓ htr
    by_cases hk : R.double.rot y ∈ Γ
    · have hσ2 : t.tourL Γ y = R.double.rot y := by
        rw [hσ]
        exact revOn_of_not_mem (not_mem_marks_of_mem hL hk)
      rw [hσ2]
      have hh : h' = R.double.rot y := htr2.unique (Trail.here hk)
      refine ⟨fun _ => ?_, fun h'' => (h'' hk).elim⟩
      have h4 : t.arcV Γ T₀ T w₀ h' = t.phi T₀ w₀ y -
          t.phiB T₀ T w₀ ((R.double.nodeReturn Γ)⁻¹ h') + ind T h' := by
        unfold arcV
        have h5 : R.double.rot⁻¹ h' = y := by rw [hh, perm_inv_apply_self]
        rw [h5]
        exact if_neg hyΓ
      rw [← hh, h4]
      omega
    · have hcond : ∀ u, u ≠ t.root → R.double.rot y = t.c1 u → t.NP Γ u := fun u hu h'' => by
        have h5 : y = t.r0 u := R.double.rot.injective (h''.trans (t.rot_r0 u).symm)
        exact np_of_r0_not_mem hL hu (h5 ▸ hyΓ)
      obtain ⟨h1', h2', h3'⟩ := hop_spec hL h₀ hk hcond
      have hσ₀y : t.tourL {w₀} y = t.tourL Γ y := by
        rw [tourL_singleton, hσ, h1']
      rw [hσ]
      refine ⟨fun h'' => (h2' h'').elim, fun _ h'' htr' => ?_⟩
      have hh : h'' = h' := htr'.unique (trail_hop hL h₀ hk hcond htr2)
      have hne₀ : t.tourL {w₀} y ≠ w₀ := by
        rw [hσ₀y, hσ]
        exact hne_w₀ h2'
      have hp := hφ y hne₀
      rw [hσ₀y, hσ] at hp
      have hi := hind _ h2' h3'
      rw [hh]
      exact ⟨by omega, by omega⟩

variable {g₀ : D × Bool} (hoff0 : off g₀ = 0)
  (hoff : ∀ g ∈ Γ, R.Same Γ g₀ g → R.double.psi Γ g ≠ g₀ →
    off (R.double.psi Γ g) = off g + t.arcV Γ T₀ T w₀ (R.double.psi Γ g))

include hL hw h₀ h₁ hL₀ hR hc hT1 hT hoff0 hoff in
/-- **Masses on the tour of a bag.** On a corner the mass from a corner `g₀` is the offset, and on another dart
it is the offset of the arc plus a difference of the numbers `phi`. -/
theorem pot_spec (hg₀ : g₀ ∈ Γ) (z : D × Bool) (hsz : R.Same Γ g₀ z) :
    (z ∈ Γ → mass (t.tourL Γ) T g₀ z = off z) ∧
      (z ∉ Γ → ∀ h, Trail (t.tau w₀) Γ z h →
        t.phiB T₀ T w₀ ((R.double.nodeReturn Γ)⁻¹ h) ≤ t.phi T₀ w₀ z ∧
        mass (t.tourL Γ) T g₀ z + t.phiB T₀ T w₀ ((R.double.nodeReturn Γ)⁻¹ h) =
          off ((R.double.psi Γ)⁻¹ h) + t.phi T₀ w₀ z) := by
  have hS := hL.spanForest hR hc
  have hσconn : ∀ {y}, R.Same Γ g₀ y → fconnect (t.tourL Γ) g₀ y := fun hy =>
    (hS.fconnect_tour_iff _ _).2 ((R.double.cone_gcomp_iff Γ _ _).2 hy)
  have hsame : ∀ {y}, fconnect (t.tourL Γ) g₀ y → R.Same Γ g₀ y := fun hy =>
    (R.double.cone_gcomp_iff Γ _ _).1 ((hS.fconnect_tour_iff _ _).1 hy)
  have hcz := hσconn hsz
  have hall : ∀ n, n ≤ pos (t.tourL Γ) g₀ z →
      (((⇑(t.tourL Γ))^[n] g₀ ∈ Γ →
          mass (t.tourL Γ) T g₀ ((⇑(t.tourL Γ))^[n] g₀) = off ((⇑(t.tourL Γ))^[n] g₀)) ∧
        ((⇑(t.tourL Γ))^[n] g₀ ∉ Γ → ∀ h, Trail (t.tau w₀) Γ ((⇑(t.tourL Γ))^[n] g₀) h →
          t.phiB T₀ T w₀ ((R.double.nodeReturn Γ)⁻¹ h) ≤ t.phi T₀ w₀ ((⇑(t.tourL Γ))^[n] g₀) ∧
          mass (t.tourL Γ) T g₀ ((⇑(t.tourL Γ))^[n] g₀) +
              t.phiB T₀ T w₀ ((R.double.nodeReturn Γ)⁻¹ h) =
            off ((R.double.psi Γ)⁻¹ h) + t.phi T₀ w₀ ((⇑(t.tourL Γ))^[n] g₀))) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨fun _ => ?_, fun h' => (h' hg₀).elim⟩
      show mass (t.tourL Γ) T g₀ g₀ = off g₀
      rw [mass_self, hoff0]
    | succ n ih =>
      intro hn
      have hne : t.tourL Γ ((⇑(t.tourL Γ))^[n] g₀) ≠ g₀ := by
        rw [← Function.iterate_succ_apply' (t.tourL Γ)]
        exact iterate_ne_start hcz (by omega) hn
      have hy : fconnect (t.tourL Γ) g₀ ((⇑(t.tourL Γ))^[n] g₀) := fconnect_iterate _ _ _
      obtain ⟨h1, h2⟩ := ih (by omega)
      obtain ⟨h3, h4⟩ := pot_step hL hw h₀ h₁ hL₀ hR hc hT1 hT off _ h1 h2
      rw [Function.iterate_succ_apply', mass_succ T hy hne]
      refine ⟨fun hm => ?_, h4⟩
      have hg : (R.double.psi Γ)⁻¹ (t.tourL Γ ((⇑(t.tourL Γ))^[n] g₀)) ∈ Γ :=
        ((R.double.fixesOff_psi Γ).inv.mem_iff _).2 hm
      have hψg : R.double.psi Γ ((R.double.psi Γ)⁻¹ (t.tourL Γ ((⇑(t.tourL Γ))^[n] g₀))) =
          t.tourL Γ ((⇑(t.tourL Γ))^[n] g₀) := perm_apply_inv_self _ _
      have hsg : R.Same Γ ((R.double.psi Γ)⁻¹ (t.tourL Γ ((⇑(t.tourL Γ))^[n] g₀)))
          (t.tourL Γ ((⇑(t.tourL Γ))^[n] g₀)) := by
        have h5 := R.double.gcomp_split_of_fconnect_psi (Γ := Γ)
          (fconnect1 (R.double.psi Γ) ((R.double.psi Γ)⁻¹ (t.tourL Γ ((⇑(t.tourL Γ))^[n] g₀))))
        rwa [hψg] at h5
      have h6 := hoff _ hg ((hsame (fconnect_apply hy)).trans hsg.symm) (by rw [hψg]; exact hne)
      rw [hψg] at h6
      rw [h6]
      exact h3 hm
  have := hall _ le_rfl
  rwa [pos_spec hcz] at this

include hL hw h₀ h₁ hL₀ hR hc hT1 hT hoff0 hoff in
/-- The mass of a whole bag is the sum of the masses of its arcs. -/
theorem cyc_spec (hg₀ : g₀ ∈ Γ) :
    cycMass (t.tourL Γ) T g₀ =
      off ((R.double.psi Γ)⁻¹ g₀) + t.arcV Γ T₀ T w₀ g₀ := by
  have hS := hL.spanForest hR hc
  set y := (t.tourL Γ)⁻¹ g₀ with hy
  have hσy : t.tourL Γ y = g₀ := perm_apply_inv_self _ _
  have hyc : fconnect (t.tourL Γ) g₀ y := by
    have h1 : fconnect (t.tourL Γ) y g₀ := by
      rw [← hσy]
      exact fconnect1 _ y
    exact fconnect_symm h1
  have hsz : R.Same Γ g₀ y := (R.double.cone_gcomp_iff Γ _ _).1 ((hS.fconnect_tour_iff _ _).1 hyc)
  obtain ⟨h1, h2⟩ := pot_spec hL hw h₀ h₁ hL₀ hR hc hT1 hT off hoff0 hoff hg₀ y hsz
  obtain ⟨h3, -⟩ := pot_step hL hw h₀ h₁ hL₀ hR hc hT1 hT off _ h1 h2
  rw [hσy] at h3
  rw [cycMass_of_last T hσy hyc]
  exact h3 hg₀

end Pot

section Interval

variable {w₀ : D × Bool} (h₀ : t.vertM w₀ = t.root) (h₁ : w₀.2 = true)

theorem anc_trans {a b c : V} (h : t.Anc a b) (h' : t.Anc b c) : t.Anc a c := by
  induction h' with
  | refl => exact h
  | step hw _ ih => exact Anc.step hw ih

theorem not_anc_root {w : V} (hw : w ≠ t.root) : ¬ t.Anc w t.root := by
  intro h
  cases h with
  | refl => exact hw rfl
  | step hr _ => exact hr rfl

open Classical in
variable (t) in
/-- The darts at vertices that are not descendants of `w`. -/
noncomputable def offSub (w : V) : Finset (D × Bool) :=
  Finset.univ.filter fun z => ¬ t.Anc w (t.vertM z)

theorem mem_offSub {w : V} {z : D × Bool} : z ∈ t.offSub w ↔ ¬ t.Anc w (t.vertM z) := by
  classical
  simp [offSub]

include h₁ in
/-- From a dart at a descendant of `w`, the tour stays at descendants up to the step after the digon corner
of `w`. -/
theorem trail_sub {w a : V} (hw : w ≠ t.root) (ha : t.Anc w a) :
    ∀ z, t.vertM z = a → Trail (t.tau w₀) (t.offSub w) z (t.tau w₀ (t.r0 w)) := by
  obtain ⟨h, hdep⟩ := exists_dep_bound t
  have he : t.tau w₀ (t.r0 w) ∈ t.offSub w := by
    rw [mem_offSub, tau_r0 hw, t.vertM_rot, t.vertM_c0]
    exact not_anc_par hw
  induction ha with
  | refl =>
    exact fun z hz => tau_walk h₁ _ hdep w hw (fun y hy => mem_offSub.1 hy) _ (Trail.here he) z hz
  | @step b hb hanc ih =>
    intro z hz
    refine tau_walk h₁ _ hdep b hb (fun y hy hab => mem_offSub.1 hy (anc_trans (Anc.step hb hanc) hab))
      _ (ih _ ?_) z hz
    rw [tau_r0 hb, t.vertM_rot, t.vertM_c0]

/-- The trail to the last element before its end. -/
theorem trail_to_last {f : Equiv.Perm (D × Bool)} {S : Finset (D × Bool)} {z e l : D × Bool}
    (h : Trail f S z e) (hl : f l = e) (hz : z ∉ S) : Trail f (insert l S) z l := by
  induction h with
  | here h' => exact (hz h').elim
  | @step y _ hy h' ih =>
    by_cases hyl : y = l
    · rw [hyl]
      exact Trail.here (Finset.mem_insert_self _ _)
    · refine Trail.step (by simp [hyl, hy]) (ih hl ?_)
      intro hm
      exact hyl (f.injective ((h'.unique (Trail.here hm)).symm.trans hl.symm))

/-- Along a trail that avoids the start of the positions, positions grow. -/
theorem pos_le_of_trail_end {f : Equiv.Perm (D × Bool)} {S : Finset (D × Bool)} {z y : D × Bool}
    (h : Trail f S z y) (hw : w₀ ∈ S) (hne : y ≠ w₀) (hconn : ∀ a b, fconnect f a b) :
    pos f w₀ z ≤ pos f w₀ y := by
  induction h with
  | here _ => exact le_rfl
  | @step a _ _ h' ih =>
    have h1 : f a ≠ w₀ := fun e => by
      have hm : f a ∈ S := by rw [e]; exact hw
      exact hne ((h'.unique (Trail.here hm)).trans e)
    have := ih hne
    have h2 := pos_apply (hconn w₀ a) h1
    omega

include h₁ in
/-- A step of the tour into the descendants of `w` is the step to the first dart of `w`. -/
theorem anc_of_tau {w : V} {y : D × Bool} (h : t.Anc w (t.vertM (t.tau w₀ y)))
    (hne : t.tau w₀ y ≠ t.c1 w) : t.Anc w (t.vertM y) := by
  by_cases hr : ∃ u, u ≠ t.root ∧ y = t.r0 u
  · obtain ⟨u, hu, rfl⟩ := hr
    rw [tau_r0 hu, t.vertM_rot, t.vertM_c0] at h
    rw [t.vertM_r0 hu]
    exact Anc.step hu h
  by_cases hc : ∃ u, u ≠ t.root ∧ y = t.c0 u
  · obtain ⟨u, hu, rfl⟩ := hc
    rw [tau_c0 hu] at h hne
    rw [t.vertM_c1 hu] at h
    rw [t.vertM_c0]
    cases h with
    | refl => exact (hne rfl).elim
    | step _ h' => exact h'
  · rw [tau_eq_rot h₁ fun v hv => ⟨fun e => hr ⟨v, hv, e⟩, fun e => hc ⟨v, hv, e⟩⟩, t.vertM_rot] at h
    exact h

include h₀ h₁ in
/-- **The darts at the descendants of a vertex form an interval of the tour.** -/
theorem anc_iff_interval {w : V} (hw : w ≠ t.root) (z : D × Bool) :
    t.Anc w (t.vertM z) ↔
      pos (t.tau w₀) w₀ (t.c1 w) ≤ pos (t.tau w₀) w₀ z ∧
        pos (t.tau w₀) w₀ z ≤ pos (t.tau w₀) w₀ (t.r0 w) := by
  have hconn : ∀ a b, fconnect (t.tau w₀) a b := fconnect_tau h₀ h₁
  have hw₀ : w₀ ∈ t.offSub w := by
    rw [mem_offSub, h₀]
    exact not_anc_root hw
  have hne : ∀ {a}, t.Anc w (t.vertM a) → a ≠ w₀ := fun ha e => (mem_offSub.1 hw₀) (e ▸ ha)
  have hr0 : t.Anc w (t.vertM (t.r0 w)) := by
    rw [t.vertM_r0 hw]
    exact Anc.refl
  have hc1 : t.Anc w (t.vertM (t.c1 w)) := by
    rw [t.vertM_c1 hw]
    exact Anc.refl
  have hup : ∀ {a}, t.Anc w (t.vertM a) → Trail (t.tau w₀) (insert (t.r0 w) (t.offSub w)) a (t.r0 w) :=
    fun {a} ha => trail_to_last (trail_sub h₁ hw ha a rfl) rfl (fun h => mem_offSub.1 h ha)
  constructor
  · intro hz
    refine ⟨?_, pos_le_of_trail_end (hup hz) (Finset.mem_insert_of_mem hw₀) (hne hr0) hconn⟩
    have key : ∀ n, ∀ a, pos (t.tau w₀) w₀ a = n → t.Anc w (t.vertM a) →
        pos (t.tau w₀) w₀ (t.c1 w) ≤ n := by
      intro n
      induction n with
      | zero =>
        intro a ha h
        have : a = w₀ := by
          have h1 := pos_spec (hconn w₀ a)
          rw [ha] at h1
          exact h1.symm
        exact (hne h this).elim
      | succ n ih =>
        intro a ha h
        by_cases hac : a = t.c1 w
        · rw [← hac, ha]
        · have hy : t.tau w₀ ((t.tau w₀)⁻¹ a) = a := perm_apply_inv_self _ _
          have h1 := pos_apply (hconn w₀ ((t.tau w₀)⁻¹ a)) (by rw [hy]; exact hne h)
          rw [hy, ha] at h1
          have h2 : t.Anc w (t.vertM ((t.tau w₀)⁻¹ a)) :=
            anc_of_tau h₁ (by rw [hy]; exact h) (by rw [hy]; exact hac)
          have := ih _ (by omega) h2
          omega
    exact key _ z rfl hz
  · rintro ⟨h1, h2⟩
    obtain ⟨k, hk, hkS⟩ := trail_exists_iterate (hup hc1)
    have hin : ∀ i, i ≤ k → t.Anc w (t.vertM ((⇑(t.tau w₀))^[i] (t.c1 w))) := by
      intro i hi
      rcases Nat.lt_or_ge i k with h | h
      · have := hkS i h
        by_contra hna
        exact this (Finset.mem_insert_of_mem (mem_offSub.2 hna))
      · obtain rfl : i = k := by omega
        rw [hk]
        exact hr0
    have hposi : ∀ i, i ≤ k → pos (t.tau w₀) w₀ ((⇑(t.tau w₀))^[i] (t.c1 w)) =
        pos (t.tau w₀) w₀ (t.c1 w) + i := by
      intro i
      induction i with
      | zero => exact fun _ => rfl
      | succ i ih =>
        intro hi
        have h3 := hin (i + 1) hi
        rw [Function.iterate_succ_apply'] at h3 ⊢
        rw [pos_apply (hconn _ _) (hne h3), ih (by omega)]
        omega
    have hk2 := hposi k le_rfl
    rw [hk] at hk2
    have hi : pos (t.tau w₀) w₀ z - pos (t.tau w₀) w₀ (t.c1 w) ≤ k := by omega
    have h3 := hposi _ hi
    have h4 : (⇑(t.tau w₀))^[pos (t.tau w₀) w₀ z - pos (t.tau w₀) w₀ (t.c1 w)] (t.c1 w) = z := by
      refine pos_inj (hconn w₀ _) (hconn w₀ _) ?_
      rw [h3]
      omega
    have := hin _ hi
    rwa [h4] at this

end Interval

end RootedTree

end RotSystem

end SsspFlow
