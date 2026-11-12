import SsspFlow.Witness

/-!
# One tour through all darts

`tau` is the rotation of the cone over all digon corners of the tree edges and one corner at the root.
It is one cycle through all darts of the doubled map (`fconnect_tau`). The darts at a vertex and its
descendants form an arc of this cycle (`tau_walk`).

For a level `Γ`, a bag is a union of arcs of `tau` that end at corners of `Γ`, and the first return of the
boundary of a bag is the next corner of this bag on `tau` (`pos_psi_le`). Within a bag, a face of the map
lies on one face of the cone, except for a digon with two corners (`fconnect_cone_face`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SsspFlow

open FourColor

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace RootedTree

variable {V : Type*} [Fintype V] [DecidableEq V] {t : R.RootedTree V}

variable (t) in
/-- All digon corners of the tree edges, and one corner at the root. -/
noncomputable def allRails (w₀ : D × Bool) : Finset (D × Bool) :=
  insert w₀ ((Finset.univ.filter fun v => v ≠ t.root).biUnion fun v => {t.r0 v, t.c0 v})

theorem mem_allRails {w₀ z : D × Bool} :
    z ∈ t.allRails w₀ ↔ z = w₀ ∨ ∃ v, v ≠ t.root ∧ (z = t.r0 v ∨ z = t.c0 v) := by
  simp [allRails]

variable (t) in
/-- The tour through all darts. -/
noncomputable def tau (w₀ : D × Bool) : Equiv.Perm (D × Bool) := (R.double.cone (t.allRails w₀)).rot

theorem c0_ne_r0_of_eq {u v : V} (hu : u ≠ t.root) (hv : v ≠ t.root) (h : t.c0 u = t.r0 v) :
    False := by
  have h1 : R.rev (t.up u) = t.up v := congrArg Prod.fst h
  have h2 : t.par u = v := by
    show t.vert (R.rev (t.up u)) = v
    rw [h1, t.vert_up v hv]
  have h3 : t.par v = u := by
    show t.vert (R.rev (t.up v)) = u
    rw [← h1, R.rev_rev, t.vert_up u hu]
  have h4 := t.dep_par_lt hu
  have h5 := t.dep_par_lt hv
  rw [h2] at h4
  rw [h3] at h5
  omega

/-- Faces of the doubled map keep the copy. -/
theorem snd_of_fconnect_face {z z' : D × Bool} (h : fconnect R.double.facePerm z z') : z'.2 = z.2 := by
  obtain ⟨n, rfl⟩ := fconnect_iff_iterate.1 h
  clear h
  have key : ∀ y : D × Bool, (R.double.facePerm y).2 = y.2 := by
    rintro ⟨d, _ | _⟩ <;> rfl
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', key]
    exact ih

section Tau

variable {w₀ : D × Bool}

theorem tau_of_not_mem {z : D × Bool} (hz : z ∉ t.allRails w₀) : t.tau w₀ z = R.double.rot z :=
  R.double.cone_rot_of_not_mem hz

theorem face_r0 (u : V) : R.double.facePerm (t.r0 u) = t.c0 u := rfl

theorem face_c0 (u : V) : R.double.facePerm (t.c0 u) = t.r0 u := by
  show R.double.facePerm (R.rev (t.up u), false) = (t.up u, false)
  rw [double_face_false, R.rev_rev]

theorem tau_r0 {u : V} (hu : u ≠ t.root) : t.tau w₀ (t.r0 u) = R.double.rot (t.c0 u) := by
  show R.double.rot (R.double.faceReturn (t.allRails w₀) (t.r0 u)) = _
  rw [show R.double.faceReturn (t.allRails w₀) (t.r0 u) = t.c0 u from
    firstReturn_eq_of_trail _ (mem_allRails.2 (Or.inr ⟨u, hu, Or.inl rfl⟩))
      (Trail.here (mem_allRails.2 (Or.inr ⟨u, hu, Or.inr rfl⟩)))]

theorem tau_c0 {u : V} (hu : u ≠ t.root) : t.tau w₀ (t.c0 u) = t.c1 u := by
  show R.double.rot (R.double.faceReturn (t.allRails w₀) (t.c0 u)) = _
  have h : R.double.faceReturn (t.allRails w₀) (t.c0 u) = t.r0 u :=
    firstReturn_eq_of_trail _ (mem_allRails.2 (Or.inr ⟨u, hu, Or.inr rfl⟩))
      (by
        rw [face_c0]
        exact Trail.here (mem_allRails.2 (Or.inr ⟨u, hu, Or.inl rfl⟩)))
  rw [h, t.rot_r0]

/-- The corner at the root is alone on its face. -/
theorem tau_w₀ (h₁ : w₀.2 = true) : t.tau w₀ w₀ = R.double.rot w₀ := by
  show R.double.rot (R.double.faceReturn (t.allRails w₀) w₀) = _
  have hm : w₀ ∈ t.allRails w₀ := mem_allRails.2 (Or.inl rfl)
  have h1 := (firstReturn_mem_iff R.double.facePerm (t.allRails w₀) w₀).2 hm
  have h2 := snd_of_fconnect_face (fconnect_firstReturn R.double.facePerm (t.allRails w₀) w₀)
  have h3 : R.double.faceReturn (t.allRails w₀) w₀ = w₀ := by
    rcases mem_allRails.1 h1 with h | ⟨v, _, h | h⟩
    · exact h
    · rw [h, h₁] at h2
      simp [r0] at h2
    · rw [h, h₁] at h2
      simp [c0] at h2
  rw [h3]

/-- Off the digon corners of the tree edges, the tour is the rotation. -/
theorem tau_eq_rot (h₁ : w₀.2 = true) {z : D × Bool}
    (h : ∀ v, v ≠ t.root → z ≠ t.r0 v ∧ z ≠ t.c0 v) : t.tau w₀ z = R.double.rot z := by
  by_cases hz : z = w₀
  · rw [hz]
    exact tau_w₀ h₁
  · refine tau_of_not_mem fun hm => ?_
    rcases mem_allRails.1 hm with h' | ⟨v, hv, h' | h'⟩
    · exact hz h'
    · exact (h v hv).1 h'
    · exact (h v hv).2 h'

/-- **The arc of a subtree.** If no dart of `S` lies at `u` or below `u`, a trail from a dart at `u` runs
to the exit of the arc of `u` and on. -/
theorem tau_walk (h₁ : w₀.2 = true) (S : Finset (D × Bool)) {h : ℕ} (hdep : ∀ v, t.dep v ≤ h) (u : V) :
    u ≠ t.root → (∀ z ∈ S, ¬ t.Anc u (t.vertM z)) → ∀ x,
      Trail (t.tau w₀) S (t.tau w₀ (t.r0 u)) x → ∀ z, t.vertM z = u → Trail (t.tau w₀) S z x := by
  induction u using (measure fun v => h - t.dep v).wf.induction with
  | _ u ih =>
    intro hu hfree x hx z hz
    have hconn : fconnect R.double.rot z (t.r0 u) :=
      (t.vertM_eq_iff _ _).1 (hz.trans (t.vertM_r0 hu).symm)
    obtain ⟨k, hk⟩ := fconnect_iff_iterate.1 hconn
    clear hconn
    induction k generalizing z with
    | zero =>
      obtain rfl : z = t.r0 u := hk
      exact Trail.step (fun hS => hfree _ hS (by rw [hz]; exact Anc.refl)) hx
    | succ k ihk =>
      rw [Function.iterate_succ_apply] at hk
      have hnext := ihk (R.double.rot z) ((t.vertM_rot z).trans hz) hk
      have hzS : z ∉ S := fun hS => hfree _ hS (by rw [hz]; exact Anc.refl)
      by_cases h1 : ∃ w, w ≠ t.root ∧ z = t.c0 w
      · obtain ⟨w, hw, rfl⟩ := h1
        have hpar : t.par w = u := hz
        refine Trail.step hzS ?_
        rw [tau_c0 hw]
        have hlt := t.dep_par_lt hw
        rw [hpar] at hlt
        have hle := hdep w
        refine ih w (show h - t.dep w < h - t.dep u by omega) hw (fun z' hz' ha => ?_) x ?_ _
          (t.vertM_c1 hw)
        · have := ha.par hw
          rw [hpar] at this
          exact hfree z' hz' this
        · rw [tau_r0 hw]
          exact hnext
      by_cases h2 : ∃ w, w ≠ t.root ∧ z = t.r0 w
      · obtain ⟨w, hw, rfl⟩ := h2
        have hwu : w = u := (t.vertM_r0 hw).symm.trans hz
        subst hwu
        exact Trail.step hzS hx
      · refine Trail.step hzS ?_
        rw [tau_eq_rot h₁ fun v hv => ⟨fun e => h2 ⟨v, hv, e⟩, fun e => h1 ⟨v, hv, e⟩⟩]
        exact hnext

theorem not_anc_par {u : V} (hu : u ≠ t.root) : ¬ t.Anc u (t.par u) := fun h => by
  have h1 := h.dep_le
  have h2 := t.dep_par_lt hu
  omega

theorem exists_dep_bound (t : R.RootedTree V) : ∃ h, ∀ v, t.dep v ≤ h :=
  ⟨Finset.univ.sup t.dep, fun v => Finset.le_sup (Finset.mem_univ v)⟩

/-- **The tour is one cycle.** -/
theorem fconnect_tau (h₀ : t.vertM w₀ = t.root) (h₁ : w₀.2 = true) (x y : D × Bool) :
    fconnect (t.tau w₀) x y := by
  classical
  obtain ⟨h, hdep⟩ := exists_dep_bound t
  have hroot : ∀ z, t.vertM z = t.root → fconnect (t.tau w₀) z (R.double.rot z) := by
    intro z hz
    by_cases h1 : ∃ w, w ≠ t.root ∧ z = t.c0 w
    · obtain ⟨w, hw, rfl⟩ := h1
      have hpar : t.par w = t.root := hz
      have htr := tau_walk h₁ {R.double.rot (t.c0 w)} hdep w hw (fun z' hz' => by
        rw [Finset.mem_singleton] at hz'
        rw [hz', t.vertM_rot, t.vertM_c0]
        exact not_anc_par hw) _ (by
          rw [tau_r0 hw]
          exact Trail.here (Finset.mem_singleton_self _)) _ (t.vertM_c1 hw)
      have h2 := fconnect1 (t.tau w₀) (t.c0 w)
      rw [tau_c0 hw] at h2
      exact connect_trans h2 htr.to_fconnect
    · have h2 : ¬ ∃ w, w ≠ t.root ∧ z = t.r0 w := by
        rintro ⟨w, hw, rfl⟩
        exact hw ((t.vertM_r0 hw).symm.trans hz)
      have h3 := fconnect1 (t.tau w₀) z
      rwa [tau_eq_rot h₁ fun v hv => ⟨fun e => h2 ⟨v, hv, e⟩, fun e => h1 ⟨v, hv, e⟩⟩] at h3
  have hall : ∀ a : V, ∀ z, t.vertM z = a → fconnect (t.tau w₀) z w₀ := by
    intro a
    induction a using (measure t.dep).wf.induction with
    | _ a ih =>
      intro z hz
      by_cases ha : a = t.root
      · subst ha
        obtain ⟨k, hk⟩ := fconnect_iff_iterate.1 ((t.vertM_eq_iff z w₀).1 (hz.trans h₀.symm))
        have hj : ∀ j, t.vertM ((⇑R.double.rot)^[j] z) = t.root := by
          intro j
          induction j with
          | zero => exact hz
          | succ j ihj =>
            rw [Function.iterate_succ_apply', t.vertM_rot]
            exact ihj
        have hc : ∀ j, fconnect (t.tau w₀) z ((⇑R.double.rot)^[j] z) := by
          intro j
          induction j with
          | zero => exact connect_refl _
          | succ j ihj =>
            rw [Function.iterate_succ_apply']
            exact connect_trans ihj (hroot _ (hj j))
        have := hc k
        rwa [hk] at this
      · have htr := tau_walk h₁ {t.tau w₀ (t.r0 a)} hdep a ha (fun z' hz' => by
          rw [Finset.mem_singleton] at hz'
          rw [hz', tau_r0 ha, t.vertM_rot, t.vertM_c0]
          exact not_anc_par ha) _ (Trail.here (Finset.mem_singleton_self _)) z hz
        refine connect_trans htr.to_fconnect (ih (t.par a) (t.dep_par_lt ha) _ ?_)
        rw [tau_r0 ha, t.vertM_rot, t.vertM_c0]
  exact connect_trans (hall _ x rfl) (fconnect_symm (hall _ y rfl))

end Tau

/-! ### Trails and positions -/

section Pos

variable {f : Equiv.Perm (D × Bool)} {S : Finset (D × Bool)}

/-- A trail is an initial piece of the orbit that avoids `S`. -/
theorem trail_exists_iterate {x y : D × Bool} (h : Trail f S x y) :
    ∃ k, (⇑f)^[k] x = y ∧ ∀ i, i < k → (⇑f)^[i] x ∉ S := by
  induction h with
  | here _ => exact ⟨0, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | @step a _ ha _ ih =>
    obtain ⟨k, hk, hj⟩ := ih
    refine ⟨k + 1, by rwa [Function.iterate_succ_apply], fun i hi => ?_⟩
    cases i with
    | zero => exact ha
    | succ i =>
      rw [Function.iterate_succ_apply]
      exact hj i (by omega)

/-- The end of a trail from `f x` comes first among the elements of `S` from `x`. -/
theorem pos_le_of_trail {x y p : D × Bool} (h : Trail f S (f x) y) (hp : p ∈ S) (hx : fconnect f x p)
    (hne : p ≠ x) : pos f x y ≤ pos f x p := by
  obtain ⟨k, hk, hj⟩ := trail_exists_iterate h
  have h1 : pos f x y ≤ k + 1 := pos_le (by rwa [Function.iterate_succ_apply])
  have h2 := pos_pos hx hne
  obtain ⟨m, hm⟩ : ∃ m, pos f x p = m + 1 := ⟨pos f x p - 1, by omega⟩
  have h3 := pos_spec hx
  rw [hm, Function.iterate_succ_apply] at h3
  have h4 : k ≤ m := by
    by_contra hlt
    exact hj m (by omega) (h3 ▸ hp)
  omega

/-- An element of `S` after the point `e` comes after the end of a trail from `f e`. -/
theorem pos_le_of_trail_after {x e y p : D × Bool} (he : fconnect f x e) (h : Trail f S (f e) y)
    (hp : p ∈ S) (hx : fconnect f x p) (hlt : pos f x e < pos f x p) : pos f x y ≤ pos f x p := by
  obtain ⟨k, hk, hj⟩ := trail_exists_iterate h
  have h1 : pos f x y ≤ k + 1 + pos f x e := by
    refine pos_le ?_
    rw [Function.iterate_add_apply, pos_spec he, Function.iterate_succ_apply]
    exact hk
  have h3 := pos_spec hx
  obtain ⟨m, hm⟩ : ∃ m, pos f x p = m + 1 + pos f x e := ⟨pos f x p - pos f x e - 1, by omega⟩
  rw [hm, Function.iterate_add_apply, pos_spec he, Function.iterate_succ_apply] at h3
  have h4 : k ≤ m := by
    by_contra hlt'
    exact hj m (by omega) (h3 ▸ hp)
  omega

end Pos

/-! ### Corners on the tour -/

section Corner

variable {w₀ : D × Bool} {Γ : Finset (D × Bool)}

theorem np_of_c0_not_mem (hL : t.IsLevel Γ) {w : V} (hw : w ≠ t.root) (h : t.c0 w ∉ Γ) : t.NP Γ w := by
  intro g hg hgw
  have := (hL.rails g hg (by rw [hgw]; exact hw)).2
  rw [hgw] at this
  exact h this

theorem np_of_r0_not_mem (hL : t.IsLevel Γ) {w : V} (hw : w ≠ t.root) (h : t.r0 w ∉ Γ) : t.NP Γ w := by
  intro g hg hgw
  have := (hL.rails g hg (by rw [hgw]; exact hw)).1
  rw [hgw] at this
  exact h this

theorem free_of_np (hL : t.IsLevel Γ) {w : V} (hw : t.NP Γ w) (z : D × Bool) (hz : z ∈ Γ) :
    ¬ t.Anc w (t.vertM z) := fun ha =>
  hw.not_mem (t.vertM_r0 (hw.ne_root hL)) (hL.rails_of_anc ha (hw.ne_root hL) hz rfl).1

/-- At a vertex with a corner, the tour reaches the same next corner as the rotation. -/
theorem trail_tau_of_rot (hL : t.IsLevel Γ) (h₁ : w₀.2 = true) {z y : D × Bool}
    (hnp : ¬ t.NP Γ (t.vertM z)) (h : Trail R.double.rot Γ z y) : Trail (t.tau w₀) Γ z y := by
  obtain ⟨hb, hdep⟩ := exists_dep_bound t
  induction h with
  | here hy => exact Trail.here hy
  | @step z y hz _ ih =>
    have hnext := ih (by rwa [t.vertM_rot])
    by_cases h1 : ∃ w, w ≠ t.root ∧ z = t.c0 w
    · obtain ⟨w, hw, rfl⟩ := h1
      have hn := np_of_c0_not_mem hL hw hz
      refine Trail.step hz ?_
      rw [tau_c0 hw]
      exact tau_walk h₁ Γ hdep w hw (free_of_np hL hn) y (by rwa [tau_r0 hw]) _ (t.vertM_c1 hw)
    by_cases h2 : ∃ w, w ≠ t.root ∧ z = t.r0 w
    · obtain ⟨w, hw, rfl⟩ := h2
      have hn := np_of_r0_not_mem hL hw hz
      rw [t.vertM_r0 hw] at hnp
      exact (hnp hn).elim
    · refine Trail.step hz ?_
      rw [tau_eq_rot h₁ fun v hv => ⟨fun e => h2 ⟨v, hv, e⟩, fun e => h1 ⟨v, hv, e⟩⟩]
      exact hnext

/-- From the rotation at a corner, the tour reaches the next corner at this vertex. -/
theorem trail_tau_rot (hL : t.IsLevel Γ) (h₁ : w₀.2 = true) {e : D × Bool} (he : e ∈ Γ) :
    Trail (t.tau w₀) Γ (R.double.rot e) (R.double.nodeReturn Γ e) :=
  trail_tau_of_rot hL h₁ (fun hn => hn e he (t.vertM_rot e).symm) (firstReturn_trail _ he)

/-- A digon corner of a tree edge is a corner whose tour goes on with the boundary of its disk. -/
theorem trail_tau_rail (hL : t.IsLevel Γ) (h₁ : w₀.2 = true) {g : D × Bool} (hg : g ∈ Γ)
    (hr : ∃ u, u ≠ t.root ∧ (g = t.r0 u ∨ g = t.c0 u)) :
    Trail (t.tau w₀) Γ (t.tau w₀ g) (R.double.psi Γ g) := by
  obtain ⟨u, hu, rfl | rfl⟩ := hr
  · have hc : t.c0 u ∈ Γ := by
      have := (hL.rails _ hg (by rw [t.vertM_r0 hu]; exact hu)).2
      rwa [t.vertM_r0 hu] at this
    have hb : R.double.faceReturn Γ (t.r0 u) = t.c0 u :=
      firstReturn_eq_of_trail _ hg (Trail.here hc)
    show Trail (t.tau w₀) Γ _ (R.double.nodeReturn Γ (R.double.faceReturn Γ (t.r0 u)))
    rw [hb, tau_r0 hu]
    exact trail_tau_rot hL h₁ hc
  · have hr' : t.r0 u ∈ Γ := by
      have := hL.pairs _ hg
      rwa [R.rev_rev] at this
    have hb : R.double.faceReturn Γ (t.c0 u) = t.r0 u :=
      firstReturn_eq_of_trail _ hg (by
        rw [face_c0]
        exact Trail.here hr')
    show Trail (t.tau w₀) Γ _ (R.double.nodeReturn Γ (R.double.faceReturn Γ (t.c0 u)))
    rw [hb, tau_c0 hu]
    exact trail_tau_rot hL h₁ hr'

/-! ### The side of a dart on the tour -/

variable (h₀ : t.vertM w₀ = t.root) (h₁ : w₀.2 = true)

include h₀ in
theorem np_singleton {v : V} (hv : v ≠ t.root) : t.NP {w₀} v := by
  intro z hz
  rw [Finset.mem_singleton] at hz
  rw [hz, h₀]
  exact hv.symm

include h₀ in
theorem mem_marks_singleton {z : D × Bool} :
    z ∈ t.marks {w₀} ↔ ∃ v, v ≠ t.root ∧ (z = t.c1 v ∨ z = t.c0 v) := by
  rw [t.mem_marks]
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v, ?_, h⟩
    rintro rfl
    exact hv w₀ (Finset.mem_singleton_self _) h₀
  · rintro ⟨v, hv, h⟩
    exact ⟨v, np_singleton h₀ hv, h⟩

theorem rot_c0_not_mark {v : V} (hv : v ≠ t.root) (h' : t.vertM w₀ = t.root) :
    R.double.rot (t.c0 v) ∉ t.marks {w₀} := by
  intro h
  obtain ⟨w, hw, h2 | h2⟩ := (mem_marks_singleton h').1 h
  · have h3 : R.rev (t.up v) = t.up w := congrArg Prod.fst h2
    have h4 : t.par v = w := by
      show t.vert (R.rev (t.up v)) = w
      rw [h3, t.vert_up w hw]
    have h5 : t.par w = v := by
      show t.vert (R.rev (t.up w)) = v
      rw [← h3, R.rev_rev, t.vert_up v hv]
    have h6 := t.dep_par_lt hv
    have h7 := t.dep_par_lt hw
    rw [h4] at h6
    rw [h5] at h7
    omega
  · have := congrArg Prod.snd h2
    simp [c0, double_rot_false] at this

theorem tourL_singleton (z : D × Bool) :
    t.tourL {w₀} z = (R.double.cone {w₀}).revOn (t.marks {w₀}) (R.double.rot z) := by
  show (R.double.cone {w₀}).revOn (t.marks {w₀}) (R.double.rot (firstReturn R.double.facePerm {w₀} z)) = _
  rw [firstReturn_singleton]
  rfl

section Side

variable {g e : D × Bool} (hne : g ≠ e)
  (hgr : ∀ v, v ≠ t.root → g ≠ t.r0 v ∧ g ≠ t.c0 v) (her : ∀ v, v ≠ t.root → e ≠ t.r0 v ∧ e ≠ t.c0 v)

include h₀ in
theorem side_eq_of_not_c0 {z : D × Bool} (h : ∀ v, v ≠ t.root → z ≠ t.c0 v) :
    t.side {w₀} g e z ↔ InArc (t.tourL {w₀}) g e z :=
  side_of_not_c0 (by
    rintro ⟨v, hv, rfl⟩
    refine h v ?_ rfl
    rintro rfl
    exact hv w₀ (Finset.mem_singleton_self _) h₀)

include h₀ h₁ in
/-- A step of the tour from a dart that is not a digon corner of a tree edge follows the tour of the marks. -/
theorem side_tau_of_step {z : D × Bool} (hz : ∀ v, v ≠ t.root → z ≠ t.r0 v ∧ z ≠ t.c0 v)
    (hs : InArc (t.tourL {w₀}) g e (t.tourL {w₀} z)) : t.side {w₀} g e (t.tau w₀ z) := by
  rw [tau_eq_rot h₁ hz]
  rw [tourL_singleton] at hs
  have hrc : R.double.RevClosed (t.marks {w₀}) := t.marks_revClosed _
  by_cases hm : R.double.rot z ∈ t.marks {w₀}
  · rw [show (R.double.cone {w₀}).revOn (t.marks {w₀}) (R.double.rot z) = R.double.rev (R.double.rot z)
      from revOn_of_mem (R := R.double.cone {w₀}) hrc hm] at hs
    obtain ⟨v, hv, h | h⟩ := (mem_marks_singleton h₀).1 hm
    · exact ((hz v hv).1 (R.double.rot.injective (h.trans (t.rot_r0 v).symm))).elim
    · rw [h] at hs ⊢
      rw [t.rev_c0] at hs
      exact (side_c0 (np_singleton h₀ hv)).2 hs
  · rw [show (R.double.cone {w₀}).revOn (t.marks {w₀}) (R.double.rot z) = R.double.rot z
      from revOn_of_not_mem hm] at hs
    refine (side_eq_of_not_c0 h₀ fun v hv e' => hm ?_).2 hs
    exact (mem_marks_singleton h₀).2 ⟨v, hv, Or.inr e'⟩

include h₀ h₁ hgr her in
/-- A step of the tour stays on the side of the arc. -/
theorem side_tau_step {z : D × Bool} (hzg : z ≠ g) (hze : z ≠ e) (hs : t.side {w₀} g e z) :
    t.side {w₀} g e (t.tau w₀ z) := by
  by_cases h1 : ∃ w, w ≠ t.root ∧ z = t.c0 w
  · obtain ⟨w, hw, rfl⟩ := h1
    rw [tau_c0 hw]
    rw [side_c0 (np_singleton h₀ hw)] at hs
    exact (side_c1 w).2 hs
  by_cases h2 : ∃ w, w ≠ t.root ∧ z = t.r0 w
  · obtain ⟨w, hw, rfl⟩ := h2
    have hnc : ∀ v, v ≠ t.root → t.r0 w ≠ t.c0 v := fun v hv e' =>
      c0_ne_r0_of_eq hv hw e'.symm
    rw [side_eq_of_not_c0 h₀ hnc] at hs
    have hs2 : InArc (t.tourL {w₀}) g e (t.tourL {w₀} (t.r0 w)) := (inArc_apply_iff hzg hze).2 hs
    have hrc : R.double.RevClosed (t.marks {w₀}) := t.marks_revClosed _
    have h3 : t.tourL {w₀} (t.r0 w) = t.c0 w := by
      rw [tourL_singleton, t.rot_r0]
      rw [show (R.double.cone {w₀}).revOn (t.marks {w₀}) (t.c1 w) = R.double.rev (t.c1 w) from
        revOn_of_mem (R := R.double.cone {w₀}) hrc ((mem_marks_singleton h₀).2 ⟨w, hw, Or.inl rfl⟩)]
      exact t.rev_c1 w
    rw [h3] at hs2
    have hs3 : InArc (t.tourL {w₀}) g e (t.tourL {w₀} (t.c0 w)) :=
      (inArc_apply_iff (fun e' => (hgr w hw).2 e'.symm) (fun e' => (her w hw).2 e'.symm)).2 hs2
    have h4 : t.tourL {w₀} (t.c0 w) = R.double.rot (t.c0 w) := by
      rw [tourL_singleton]
      exact revOn_of_not_mem (rot_c0_not_mark hw h₀)
    rw [h4] at hs3
    rw [tau_r0 hw]
    refine (side_eq_of_not_c0 h₀ fun v _ e' => ?_).2 hs3
    have := congrArg Prod.snd e'
    simp [c0, double_rot_false] at this
  · have hz : ∀ v, v ≠ t.root → z ≠ t.r0 v ∧ z ≠ t.c0 v :=
      fun v hv => ⟨fun e' => h2 ⟨v, hv, e'⟩, fun e' => h1 ⟨v, hv, e'⟩⟩
    rw [side_eq_of_not_c0 h₀ fun v hv => (hz v hv).2] at hs
    exact side_tau_of_step h₀ h₁ hz ((inArc_apply_iff hzg hze).2 hs)

include h₀ h₁ hne hgr her in
/-- The arc of the tour from `g` to `e` lies on the side of the arc of the tour of the marks. -/
theorem side_of_inArc_tau (hcf : fconnect (t.tourL {w₀}) g e) {p : D × Bool}
    (h : InArc (t.tau w₀) g e p) : t.side {w₀} g e p := by
  obtain ⟨hp, hpg, hle⟩ := h
  have hconn : fconnect (t.tau w₀) g e := fconnect_tau h₀ h₁ g e
  have key : ∀ n, n + 1 ≤ pos (t.tau w₀) g e →
      t.side {w₀} g e ((⇑(t.tau w₀))^[n + 1] g) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact side_tau_of_step h₀ h₁ hgr (inArc_apply_start hcf hne).1
    | succ n ih =>
      intro hn
      rw [Function.iterate_succ_apply']
      have hm := ih (by omega)
      refine side_tau_step h₀ h₁ hgr her ?_ ?_ hm
      · exact iterate_ne_start hconn (by omega) (by omega)
      · intro he
        have := pos_le (f := t.tau w₀) he
        omega
  obtain ⟨m, hm⟩ : ∃ m, pos (t.tau w₀) g p = m + 1 := ⟨pos (t.tau w₀) g p - 1, by
    have := pos_pos hp hpg
    omega⟩
  have := key m (by omega)
  rwa [← hm, pos_spec hp] at this

end Side

variable {g p : D × Bool}

include h₀ h₁ in
/-- **The next corner of a bag on the tour.** The first return of the boundary of a disk comes first on
the tour among the corners of this disk. -/
theorem pos_psi_le (hL₀ : t.IsLevel {w₀}) (hL : t.IsLevel Γ) (hw : w₀ ∈ Γ) (hR : R.Planar)
    (hc : R.Connected) (hg : g ∈ Γ) (hp : p ∈ Γ) (hs : R.Same Γ g p) (hne : p ≠ g) :
    pos (t.tau w₀) g (R.double.psi Γ g) ≤ pos (t.tau w₀) g p := by
  have hconn := fconnect_tau h₀ h₁
  by_cases hrail : ∃ u, u ≠ t.root ∧ (g = t.r0 u ∨ g = t.c0 u)
  · exact pos_le_of_trail (trail_tau_rail hL h₁ hg hrail) hp (hconn _ _) hne
  have hgr : ∀ v, v ≠ t.root → g ≠ t.r0 v ∧ g ≠ t.c0 v :=
    fun v hv => ⟨fun e => hrail ⟨v, hv, Or.inl e⟩, fun e => hrail ⟨v, hv, Or.inr e⟩⟩
  have hτg : t.tau w₀ g = R.double.rot g := tau_eq_rot h₁ hgr
  set e := R.double.faceReturn Γ g with he
  have heΓ : e ∈ Γ := (firstReturn_mem_iff _ _ _).2 hg
  have hpsi : R.double.psi Γ g = R.double.nodeReturn Γ e := rfl
  by_cases heg : e = g
  · rw [hpsi, heg]
    refine pos_le_of_trail ?_ hp (hconn _ _) hne
    rw [hτg]
    exact trail_tau_rot hL h₁ hg
  have hge : fconnect R.double.facePerm g e := fconnect_firstReturn _ _ _
  have her : ∀ v, v ≠ t.root → e ≠ t.r0 v ∧ e ≠ t.c0 v := by
    intro v hv
    have hs2 := snd_of_fconnect_face hge
    constructor
    · intro h
      have h3 := (hL.rails e heΓ (by rw [h, t.vertM_r0 hv]; exact hv)).2
      rw [h, t.vertM_r0 hv] at h3
      -- `g` is a dart of the digon of `v`
      have hg2 : g.2 = false := by
        rw [h] at hs2
        exact hs2.symm
      obtain ⟨d, b⟩ := g
      obtain rfl : b = false := hg2
      have hb : R.double.faceReturn Γ (d, false) = (R.rev d, false) :=
        firstReturn_eq_of_trail _ hg (Trail.here (hL.pairs d hg))
      have h4 : (R.rev d, false) = t.r0 v := hb.symm.trans (he.symm.trans h)
      have h5 : R.rev d = t.up v := congrArg Prod.fst h4
      have h6 : d = R.rev (t.up v) := by rw [← h5, R.rev_rev]
      exact (hgr v hv).2 (by rw [h6]; rfl)
    · intro h
      have hg2 : g.2 = false := by
        rw [h] at hs2
        exact hs2.symm
      obtain ⟨d, b⟩ := g
      obtain rfl : b = false := hg2
      have hb : R.double.faceReturn Γ (d, false) = (R.rev d, false) :=
        firstReturn_eq_of_trail _ hg (Trail.here (hL.pairs d hg))
      have h4 : (R.rev d, false) = t.c0 v := hb.symm.trans (he.symm.trans h)
      have h5 : R.rev d = R.rev (t.up v) := congrArg Prod.fst h4
      have h6 : d = t.up v := by
        have := congrArg R.rev h5
        rwa [R.rev_rev, R.rev_rev] at this
      exact (hgr v hv).1 (by rw [h6]; rfl)
  have hτe : t.tau w₀ e = R.double.rot e := tau_eq_rot h₁ her
  have hne' : g ≠ e := fun h => heg h.symm
  have hf : fconnect (⇑(R.double.cone {w₀}).facePerm⁻¹) g e := by
    rw [R.double.cone_singleton_facePerm, fconnect_inv_iff]
    exact hge
  have hS₀ := hL₀.spanForest hR hc
  have hcf : fconnect (t.tourL {w₀}) g e := hS₀.fconnect_tour_of_face hf
  have hsub : ({w₀} : Finset (D × Bool)) ⊆ Γ := Finset.singleton_subset_iff.2 hw
  have hside : ¬ t.side {w₀} g e p := by
    intro h
    have h3 := (side_gcomp hL₀ hR hc hne' hf hL hg heΓ hsub hs).2 h
    rw [side_eq_of_not_c0 h₀ fun v hv => (hgr v hv).2] at h3
    exact not_inArc_start h3
  have hlt : pos (t.tau w₀) g e < pos (t.tau w₀) g p := by
    by_contra hle
    exact hside (side_of_inArc_tau h₀ h₁ hne' hgr her hcf ⟨hconn _ _, hne, by omega⟩)
  refine pos_le_of_trail_after (hconn _ _) ?_ hp (hconn _ _) hlt
  rw [hτe, hpsi]
  exact trail_tau_rot hL h₁ heΓ

section Section

/-- Off the corners, a face of the cone steps like the face of the map. -/
theorem cone_face_of_not_mem {z : D × Bool} (h : R.double.facePerm z ∉ Γ) :
    (R.double.cone Γ).facePerm z = R.double.facePerm z := by
  rw [R.double.cone_facePerm]
  exact (R.double.fixesOff_faceReturn Γ).inv _ h

/-- A face of the map without a corner is a face of the cone. -/
theorem fconnect_cone_of_no_corner {x y : D × Bool} (hf : fconnect R.double.facePerm x y)
    (h : ∀ w, fconnect R.double.facePerm x w → w ∉ Γ) :
    fconnect (R.double.cone Γ).facePerm x y := by
  obtain ⟨n, rfl⟩ := fconnect_iff_iterate.1 hf
  clear hf
  induction n with
  | zero => exact fconnect_iterate _ _ 0
  | succ n ih =>
    have h1 := h _ (fconnect_iterate _ _ (n + 1))
    rw [Function.iterate_succ_apply'] at h1 ⊢
    have h2 := cone_face_of_not_mem h1
    rw [← h2]
    exact fconnect_apply ih

/-- The darts after a corner up to the next corner of the map lie on one face of the cone. -/
theorem fconnect_cone_of_trail {z c : D × Bool} (h : Trail (R.double.facePerm⁻¹) Γ z c) :
    fconnect (R.double.cone Γ).facePerm c z := by
  induction h with
  | here _ => exact fconnect_iterate _ _ 0
  | @step y _ hy _ ih =>
    have h2 : (R.double.cone Γ).facePerm (R.double.facePerm⁻¹ y) = y := by
      rw [cone_face_of_not_mem (by rwa [perm_apply_inv_self]), perm_apply_inv_self]
    rw [← h2]
    exact fconnect_apply ih

/-- The face of a copy of a dart in the first copy is a digon. -/
theorem fconnect_digon {d : D} {w : D × Bool} (h : fconnect R.double.facePerm (d, false) w) :
    w = (d, false) ∨ w = (R.rev d, false) := by
  have hface : R.double.facePerm (d, false) = (R.rev d, false) := R.double_face_false d
  have hface2 : R.double.facePerm (R.rev d, false) = (d, false) := by
    rw [R.double_face_false, R.rev_rev]
  obtain ⟨n, rfl⟩ := fconnect_iff_iterate.1 h
  clear h
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h <;> rw [h]
    · exact Or.inr hface
    · exact Or.inl hface2

/-- **One section.** Two darts of one bag on one face of the map lie on one face of the cone, except at the
corner of a digon. -/
theorem fconnect_cone_face (hL₀ : t.IsLevel {w₀}) (hL : t.IsLevel Γ) (hw : w₀ ∈ Γ) (hR : R.Planar)
    (hc : R.Connected) {x y : D × Bool} (hs : R.Same Γ x y) (hf : fconnect R.double.facePerm x y)
    (hd : ¬ (x ∈ Γ ∧ x.2 = false)) : fconnect (⇑(R.double.cone Γ).facePerm⁻¹) x y := by
  rw [fconnect_inv_iff]
  have hsym : ∀ {a b : D × Bool}, fconnect R.double.facePerm a b → fconnect R.double.facePerm b a :=
    fun h => fconnect_sym R.double.facePerm.injective _ _ h
  by_cases hcorner : ∃ g ∈ Γ, fconnect R.double.facePerm x g
  · obtain ⟨g, hg, hxg⟩ := hcorner
    cases hx2 : x.2 with
    | false =>
      obtain ⟨d, b⟩ := x
      obtain rfl : b = false := hx2
      have hx : (d, false) ∉ Γ := fun h => hd ⟨h, rfl⟩
      refine fconnect_cone_of_no_corner hf fun w hw' hwm => ?_
      rcases fconnect_digon hw' with rfl | rfl
      · exact hx hwm
      · have := hL.pairs _ hwm
        rw [R.rev_rev] at this
        exact hx this
    | true =>
      have hbf : fconnect (⇑R.double.facePerm⁻¹) x g := (fconnect_inv_iff _).2 hxg
      have hbf' : fconnect (⇑R.double.facePerm⁻¹) y g :=
        (fconnect_inv_iff _).2 (connect_trans (hsym hf) hxg)
      obtain ⟨c, hcx⟩ := exists_trail (f := R.double.facePerm⁻¹) hg hbf
      obtain ⟨c', hcy⟩ := exists_trail (f := R.double.facePerm⁻¹) hg hbf'
      have h1 := fconnect_cone_of_trail hcx
      have h2 := fconnect_cone_of_trail hcy
      have hsameZ : ∀ {a b : D × Bool}, fconnect (R.double.cone Γ).facePerm a b → R.Same Γ a b :=
        fun h => (R.double.cone_gcomp_iff Γ _ _).1 ((R.double.cone Γ).toHypermap.gcomp_of_cface h)
      have hcc' : R.Same Γ c c' := (hsameZ h1).trans (hs.trans (hsameZ h2).symm)
      have hcx' : fconnect R.double.facePerm x c := (fconnect_inv_iff _).1 hcx.to_fconnect
      have hcy' : fconnect R.double.facePerm y c' := (fconnect_inv_iff _).1 hcy.to_fconnect
      have hfcc' : fconnect R.double.facePerm c c' :=
        connect_trans (hsym hcx') (connect_trans hf hcy')
      have hc2 : c.2 = true := by rw [snd_of_fconnect_face hcx', hx2]
      have hc'2 : c'.2 = true := by rw [snd_of_fconnect_face hfcc', hc2]
      have heq : c = c' := by
        by_contra hne
        exact not_same_of_face hL₀ hL hw hR hc hcx.mem hcy.mem hc2 hc'2 hne hfcc' hcc'
      subst heq
      exact connect_trans (fconnect_sym (R.double.cone Γ).facePerm.injective _ _ h1) h2
  · exact fconnect_cone_of_no_corner hf fun w hw' hwm => hcorner ⟨w, hwm, hw'⟩

end Section

end Corner

end RootedTree

end RotSystem

end SsspFlow
