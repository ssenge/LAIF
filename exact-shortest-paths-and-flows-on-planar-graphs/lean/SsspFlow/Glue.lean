import SsspFlow.Crossing
import SsspFlow.Labels

/-!
# Distances in a glued map

Let `A` be a map with marked corners `Γ`, at most one per vertex, and let `B := A.glue ν` for a
permutation `ν` of `Γ`. The vertices of `B` are the vertices of `A`, with those on one cycle of `ν`
merged. `walkDist_glue`: the distance in `B` between marked corners is the least total weight of a
walk through marked corners, whose steps cost the distance in `A`, or nothing on a cycle of `ν`.

`split_faceDrawn`: on the split of a planar connected map, a cycle of `ψ` lies on one face in its
order, so the crossing theorem and (M) hold for it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal

namespace SsspFlow

open FourColor

/-! ### Hub walks -/

section Hub

variable {D : Type*} [DecidableEq D]

/-- The least total weight of a walk through marked corners, with arbitrary steps. -/
noncomputable def hubDist (Γ : Finset D) (w : D → D → ℝ≥0∞) (p q : D) : ℝ≥0∞ :=
  dist (fun _ _ => True) w (Γ : Set D) p q

variable {Γ : Finset D} {w w' : D → D → ℝ≥0∞} {p q r : D}

theorem hubDist_le_step (hp : p ∈ Γ) (hq : q ∈ Γ) : hubDist Γ w p q ≤ w p q := by
  have h : hubDist Γ w p q ≤ (Walk.cons trivial (Walk.nil q) :
      Walk (fun _ _ => True) p q).wt w := iInf₂_le _ (by
    intro z hz
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact hp
    · exact hq)
  simpa using h

theorem hubDist_self_le (hp : p ∈ Γ) : hubDist Γ w p p = 0 := by
  refine le_antisymm ?_ zero_le
  have h : hubDist Γ w p p ≤ (Walk.nil p : Walk (fun _ _ => True) p p).wt w :=
    iInf₂_le _ (by simpa using hp)
  simpa using h

theorem hubDist_triangle (w : D → D → ℝ≥0∞) (p q r : D) :
    hubDist Γ w p r ≤ hubDist Γ w p q + hubDist Γ w q r :=
  dist_triangle' w _ p q r

/-- The length of a hub walk through marked corners does not fall when the weights on marked corners
grow. -/
private theorem wt_le_of_mem (h : ∀ a ∈ Γ, ∀ b ∈ Γ, w a b ≤ w' a b) :
    ∀ {a b : D} (c : Walk (fun _ _ => True) a b), (∀ z ∈ c.support, z ∈ (Γ : Set D)) →
      c.wt w ≤ c.wt w'
  | _, _, .nil _, _ => le_rfl
  | a, _, .cons _ c, hc => by
    have ha : a ∈ Γ := hc a (by simp)
    have hm : ∀ z ∈ c.support, z ∈ (Γ : Set D) := fun z hz => hc z (List.mem_cons_of_mem _ hz)
    have hb := hm _ c.start_mem
    simp only [Walk.wt_cons]
    exact add_le_add (h _ ha _ hb) (wt_le_of_mem h c hm)

theorem hubDist_mono (h : ∀ a ∈ Γ, ∀ b ∈ Γ, w a b ≤ w' a b) (p q : D) :
    hubDist Γ w p q ≤ hubDist Γ w' p q := by
  simp only [hubDist, dist, le_iInf_iff]
  exact fun c hc => (iInf₂_le c hc).trans (wt_le_of_mem h c hc)

private theorem wt_const_mul (c : ℝ≥0∞) :
    ∀ {a b : D} (s : Walk (fun _ _ => True) a b),
      s.wt (fun x y => c * w x y) = c * s.wt w
  | _, _, .nil _ => by simp
  | _, _, .cons _ s => by simp [wt_const_mul c s, mul_add]

/-- A constant factor comes out of a hub walk. -/
theorem hubDist_const_mul {c : ℝ≥0∞} (h0 : c ≠ 0) (hT : c ≠ ⊤) (p q : D) :
    hubDist Γ (fun x y => c * w x y) p q = c * hubDist Γ w p q := by
  simp only [hubDist, dist, ENNReal.mul_iInf_of_ne h0 hT, wt_const_mul]

/-- A function with a triangle inequality that lies below the steps lies below the hub walks. -/
theorem le_hubDist {f : D → D → ℝ≥0∞} (hself : ∀ a, f a a = 0)
    (htri : ∀ a b c, f a c ≤ f a b + f b c) (h : ∀ a ∈ Γ, ∀ b ∈ Γ, f a b ≤ w a b) (p q : D) :
    f p q ≤ hubDist Γ w p q := by
  simp only [hubDist, dist, le_iInf_iff]
  intro c hc
  induction c with
  | nil a => simp [hself]
  | @cons a m b _ s ih =>
    have ha : a ∈ Γ := hc a (by simp)
    have hm : ∀ z ∈ s.support, z ∈ (Γ : Set D) := fun z hz => hc z (List.mem_cons_of_mem _ hz)
    simp only [Walk.wt_cons]
    exact (htri a m b).trans (add_le_add (h _ ha _ (hm _ s.start_mem)) (ih hm))

end Hub

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] {A : RotSystem D} {Γ : Finset D}
  {ν : Equiv.Perm D}

/-! ### Vertices of a glued map -/

/-- Two marked corners at one vertex of a map with at most one per vertex coincide. -/
theorem eq_of_tail_eq (h1 : A.nodeReturn Γ = 1) {p q : D} (hp : p ∈ Γ) (hq : q ∈ Γ)
    (h : A.tail p = A.tail q) : p = q := by
  have h2 : fconnect (firstReturn A.rot Γ) p q :=
    (fconnect_firstReturn_iff A.rot hp hq).2 ((A.tail_eq_iff p q).1 h)
  have h3 : firstReturn A.rot Γ = 1 := h1
  rw [h3] at h2
  exact (eq_of_fconnect_of_fixed (g := (1 : Equiv.Perm D)) rfl h2).symm

/-- Along a trail to a marked corner, the rotation of the glued map is that of `A`. -/
theorem tail_glue_of_trail (hν : FixesOff ν Γ) {y z : D} (h : Trail A.rot Γ y z) :
    (A.glue ν).tail y = (A.glue ν).tail z := by
  induction h with
  | here _ => rfl
  | @step y z hy _ ih =>
    rw [← ih]
    have h2 : (A.glue ν).rot y = A.rot y := by
      show A.rot (ν y) = A.rot y
      rw [hν y hy]
    have h3 := (A.glue ν).tail_rot y
    rw [h2] at h3
    exact h3.symm

theorem tail_glue_rot (h1 : A.nodeReturn Γ = 1) (hν : FixesOff ν Γ) (x : D) :
    (A.glue ν).tail (A.rot x) = (A.glue ν).tail x := by
  by_cases hx : x ∈ Γ
  · have h2 := firstReturn_trail A.rot hx
    have h3 : firstReturn A.rot Γ x = x := by
      have h4 : firstReturn A.rot Γ = 1 := h1
      rw [h4]
      rfl
    rw [h3] at h2
    exact tail_glue_of_trail hν h2
  · have h2 : (A.glue ν).rot x = A.rot x := by
      show A.rot (ν x) = A.rot x
      rw [hν x hx]
    have h3 := (A.glue ν).tail_rot x
    rwa [h2] at h3

/-- Darts at one vertex of `A` are at one vertex of the glued map. -/
theorem tail_glue_of_tail (h1 : A.nodeReturn Γ = 1) (hν : FixesOff ν Γ) {x y : D}
    (h : A.tail x = A.tail y) : (A.glue ν).tail x = (A.glue ν).tail y := by
  obtain ⟨n, rfl⟩ := fconnect_iff_iterate.1 ((A.tail_eq_iff x y).1 h)
  clear h
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show (A.glue ν).tail x = (A.glue ν).tail (A.rot (A.rot^[n] x))
    rw [tail_glue_rot h1 hν]
    exact ih

/-- Darts at one vertex of the glued map are at one vertex of `A`, or at two vertices of `A` whose
marked corners lie on one cycle of `ν`. -/
theorem tail_of_tail_glue (h1 : A.nodeReturn Γ = 1) (hν : FixesOff ν Γ) {x y : D}
    (h : (A.glue ν).tail x = (A.glue ν).tail y) :
    A.tail x = A.tail y ∨ ∃ p ∈ Γ, ∃ q ∈ Γ, A.tail p = A.tail x ∧ A.tail q = A.tail y ∧
      fconnect ν p q := by
  obtain ⟨n, rfl⟩ := fconnect_iff_iterate.1 (((A.glue ν).tail_eq_iff x y).1 h)
  clear h
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    set y' := (A.glue ν).toHypermap.node^[n] x with hy'
    show A.tail x = A.tail (A.rot (ν y')) ∨ ∃ p ∈ Γ, ∃ q ∈ Γ, A.tail p = A.tail x ∧
      A.tail q = A.tail (A.rot (ν y')) ∧ fconnect ν p q
    rw [A.tail_rot]
    by_cases hm : y' ∈ Γ
    · have hνm : ν y' ∈ Γ := (hν.mem_iff y').2 hm
      refine Or.inr ?_
      rcases ih with ih | ⟨p, hp, q, hq, h2, h3, h4⟩
      · exact ⟨y', hm, ν y', hνm, ih.symm, rfl, fconnect1 _ y'⟩
      · obtain rfl : q = y' := eq_of_tail_eq h1 hq hm h3
        exact ⟨p, hp, ν y', hνm, h2, rfl, connect_trans h4 (fconnect1 _ y')⟩
    · rw [hν y' hm]
      exact ih

/-- A walk of `A` is a walk of the glued map. -/
theorem isWalk_glue (h1 : A.nodeReturn Γ = 1) (hν : FixesOff ν Γ) {ws : List D} {u v : D}
    (h : A.IsWalk (A.tail u) ws (A.tail v)) :
    (A.glue ν).IsWalk ((A.glue ν).tail u) ws ((A.glue ν).tail v) := by
  induction ws generalizing u with
  | nil => exact tail_glue_of_tail h1 hν h
  | cons x ws ih =>
    obtain ⟨h2, h3⟩ := h
    exact ⟨tail_glue_of_tail h1 hν h2, ih h3⟩

/-! ### The distance -/

/-- The steps of hub walks: free on a cycle of `ν`, otherwise given by `μ`. -/
noncomputable def stepOf (ν : Equiv.Perm D) (μ : D → D → ℝ≥0∞) (a b : D) : ℝ≥0∞ :=
  open Classical in if fconnect ν a b then 0 else μ a b

theorem stepOf_le (μ : D → D → ℝ≥0∞) (a b : D) : stepOf ν μ a b ≤ μ a b := by
  unfold stepOf
  split_ifs
  · exact zero_le
  · exact le_rfl

theorem stepOf_mono {μ μ' : D → D → ℝ≥0∞} (h : ∀ a ∈ Γ, ∀ b ∈ Γ, μ a b ≤ μ' a b) :
    ∀ a ∈ Γ, ∀ b ∈ Γ, stepOf ν μ a b ≤ stepOf ν μ' a b := by
  intro a ha b hb
  unfold stepOf
  split_ifs
  · exact le_rfl
  · exact h a ha b hb

theorem stepOf_const_mul (c : ℝ≥0∞) (μ : D → D → ℝ≥0∞) (a b : D) :
    stepOf ν (fun x y => c * μ x y) a b = c * stepOf ν μ a b := by
  unfold stepOf
  split_ifs <;> simp

/-- The steps of the hub walks in a glued map. -/
noncomputable def gluedStep (A : RotSystem D) (ν : Equiv.Perm D) (g : D → ℝ≥0∞) : D → D → ℝ≥0∞ :=
  stepOf ν fun a b => A.walkDist g (A.tail a) (A.tail b)

theorem gluedStep_le (g : D → ℝ≥0∞) (a b : D) :
    gluedStep A ν g a b ≤ A.walkDist g (A.tail a) (A.tail b) :=
  stepOf_le _ a b

/-- **Distances in a glued map.** Between marked corners, the distance in `A.glue ν` is the least
total weight of a hub walk, whose steps cost the distance in `A` or nothing on a cycle of `ν`. -/
theorem walkDist_glue (h1 : A.nodeReturn Γ = 1) (hν : FixesOff ν Γ) (g : D → ℝ≥0∞) (p q : D)
    (hq : q ∈ Γ) (hp : p ∈ Γ) :
    (A.glue ν).walkDist g ((A.glue ν).tail p) ((A.glue ν).tail q) =
      hubDist Γ (gluedStep A ν g) p q := by
  have hW : ∀ a ∈ Γ, ∀ b ∈ Γ, hubDist Γ (gluedStep A ν g) a b ≤
      A.walkDist g (A.tail a) (A.tail b) := fun a ha b hb =>
    (hubDist_le_step ha hb).trans (gluedStep_le g a b)
  have hF : ∀ a ∈ Γ, ∀ b ∈ Γ, fconnect ν a b → hubDist Γ (gluedStep A ν g) a b = 0 := by
    intro a ha b hb h
    refine le_antisymm ((hubDist_le_step ha hb).trans ?_) zero_le
    exact (ite_eq_left h).le
  apply le_antisymm
  · -- A hub walk gives a walk of the glued map.
    refine le_hubDist (f := fun a b => (A.glue ν).walkDist g ((A.glue ν).tail a) ((A.glue ν).tail b))
      (fun a => walkDist_self g _) (fun a b c => walkDist_triangle g _ _ _) ?_ p q
    intro a ha b hb
    unfold gluedStep stepOf
    split_ifs with h
    · have h2 : (A.glue ν).tail a = (A.glue ν).tail b := by
        obtain ⟨n, rfl⟩ := fconnect_iff_iterate.1 h
        clear h hb
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [Function.iterate_succ_apply', ih]
          have hm : ν^[n] a ∈ Γ := by
            clear ih
            induction n with
            | zero => exact ha
            | succ n ih => rw [Function.iterate_succ_apply']; exact (hν.mem_iff _).2 ih
          have h3 := tail_glue_rot h1 hν (ν (ν^[n] a))
          have h4 := (A.glue ν).tail_rot (ν^[n] a)
          have h5 : (A.glue ν).rot (ν^[n] a) = A.rot (ν (ν^[n] a)) := rfl
          rw [h5] at h4
          rw [← h3, h4]
      rw [h2, walkDist_self]
    · simp only [walkDist, le_iInf_iff]
      intro ws hws
      exact walkDist_le g (isWalk_glue h1 hν hws)
  · -- A walk of the glued map gives a hub walk.
    have key : ∀ (ws : List D) (z : D), z ∈ Γ → ∀ (u : D) (c : ℝ≥0∞),
        A.walkDist g (A.tail z) (A.tail u) ≤ c →
        (A.glue ν).IsWalk ((A.glue ν).tail u) ws ((A.glue ν).tail q) →
        hubDist Γ (gluedStep A ν g) z q ≤ c + (ws.map g).sum := by
      intro ws
      induction ws with
      | nil =>
        intro z hz u c hc hw
        simp only [List.map_nil, List.sum_nil, add_zero]
        rcases tail_of_tail_glue h1 hν hw with h | ⟨p', hp', q', hq', h2, h3, h4⟩
        · rw [h] at hc
          exact (hW z hz q hq).trans hc
        · obtain rfl : q' = q := eq_of_tail_eq h1 hq' hq h3
          rw [← h2] at hc
          calc hubDist Γ (gluedStep A ν g) z q'
              ≤ hubDist Γ (gluedStep A ν g) z p' + hubDist Γ (gluedStep A ν g) p' q' :=
                hubDist_triangle _ _ _ _
            _ ≤ c + 0 := add_le_add ((hW z hz p' hp').trans hc) (hF p' hp' q' hq' h4).le
            _ = c := add_zero c
      | cons x ws ih =>
        intro z hz u c hc hw
        obtain ⟨h2, h3⟩ := hw
        have hstep : A.walkDist g (A.tail x) (A.tail (A.rev x)) ≤ g x := by
          have h5 := walkDist_le (R := A) g (u := A.tail x) (v := A.tail (A.rev x)) (p := [x])
            ⟨rfl, rfl⟩
          simpa using h5
        rw [List.map_cons, List.sum_cons]
        rcases tail_of_tail_glue h1 hν h2 with h | ⟨x', hx', p', hp', h4, h5, h6⟩
        · have h7 := ih z hz (A.rev x) (c + g x) (by
            refine (walkDist_triangle g _ (A.tail x) _).trans (add_le_add ?_ hstep)
            rw [h]
            exact hc) h3
          rwa [add_assoc] at h7
        · have h7 := ih x' hx' (A.rev x) (g x) (by
            rw [h4]
            exact hstep) h3
          have h8 : hubDist Γ (gluedStep A ν g) p' x' = 0 :=
            hF p' hp' x' hx' (fconnect_sym ν.injective _ _ h6)
          calc hubDist Γ (gluedStep A ν g) z q
              ≤ hubDist Γ (gluedStep A ν g) z p' + hubDist Γ (gluedStep A ν g) p' q :=
                hubDist_triangle _ _ _ _
            _ ≤ hubDist Γ (gluedStep A ν g) z p' + (hubDist Γ (gluedStep A ν g) p' x' +
                hubDist Γ (gluedStep A ν g) x' q) := by
                gcongr
                exact hubDist_triangle _ _ _ _
            _ ≤ c + (0 + (g x + (ws.map g).sum)) := by
                refine add_le_add ?_ (add_le_add h8.le h7)
                have hc' : A.walkDist g (A.tail z) (A.tail p') ≤ c := by
                  rw [h5]
                  exact hc
                exact (hW z hz p' hp').trans hc'
            _ = c + (g x + (ws.map g).sum) := by rw [zero_add]
    simp only [walkDist, le_iInf_iff]
    intro ws hws
    have h2 := key ws p hp p 0 (by rw [walkDist_self]) hws
    rwa [zero_add] at h2

/-- `walkDist_glue` for a map that is equal to the gluing. -/
theorem walkDist_of_eq_glue {B : RotSystem D} (hB : B = A.glue ν) (h1 : A.nodeReturn Γ = 1)
    (hν : FixesOff ν Γ) (g : D → ℝ≥0∞) (p q : D) (hq : q ∈ Γ) (hp : p ∈ Γ) :
    B.walkDist g (B.tail p) (B.tail q) = hubDist Γ (gluedStep A ν g) p q := by
  subst hB
  exact walkDist_glue h1 hν g p q hq hp

/-- The distance in the split at `Γ` between corners of `Γ' ⊇ Γ` is the least total weight of a hub
walk over the distances in the split at `Γ'`. -/
theorem walkDist_split_hub (R : RotSystem D) {Γ₁ Γ₂ : Finset D} (hsub : Γ₁ ⊆ Γ₂) (g : D → ℝ≥0∞)
    {p q : D} (hp : p ∈ Γ₂) (hq : q ∈ Γ₂) :
    (R.split Γ₁).walkDist g ((R.split Γ₁).tail p) ((R.split Γ₁).tail q) =
      hubDist Γ₂ (stepOf ((R.split Γ₁).nodeReturn Γ₂) fun a b =>
        (R.split Γ₂).walkDist g ((R.split Γ₂).tail a) ((R.split Γ₂).tail b)) p q := by
  have e2 : (R.split Γ₁).split Γ₂ = R.split Γ₂ := R.split_split hsub
  have e3 : R.split Γ₁ = (R.split Γ₂).glue ((R.split Γ₁).nodeReturn Γ₂) := by
    conv_lhs => rw [← (R.split Γ₁).glue_split Γ₂, e2]
  exact walkDist_of_eq_glue e3 (R.nodeReturn_split Γ₂)
    ((R.split Γ₁).fixesOff_nodeReturn Γ₂) g p q hq hp

/-! ### Cycles of `ψ` lie on one face of the split -/

/-- The first return of a permutation to an invariant set on which it acts as `f` is `f`. -/
private theorem firstReturn_eq_formPerm {f : Equiv.Perm D} {l : List D}
    (hψ : ∀ x ∈ l, f x = l.formPerm x) : firstReturn f l.toFinset = l.formPerm := by
  ext x
  by_cases hx : x ∈ l
  · refine firstReturn_eq_of_trail _ (List.mem_toFinset.2 hx) ?_
    rw [hψ x hx]
    exact Trail.here (List.mem_toFinset.2 (List.formPerm_apply_mem_of_mem hx))
  · rw [firstReturn_of_not_mem _ (by simpa using hx), List.formPerm_apply_of_notMem hx]

/-- **A cycle of `ψ` lies on one face of the split**, in its order. -/
theorem split_faceDrawn {R : RotSystem D} (hR : R.Planar) (hc : R.Connected) (hΓ : Γ.Nonempty)
    (hS : R.SkeletonConnected Γ) {l : List D} (hn : l.Nodup) (hl : ∀ x ∈ l, x ∈ Γ)
    (hψ : ∀ x ∈ l, R.psi Γ x = l.formPerm x) : (R.split Γ).FaceDrawn l where
  planar := (R.split_planar hR hc hΓ hS).1
  tails_nodup := by
    refine hn.map_on fun x hx y hy h => ?_
    exact eq_of_tail_eq (R.nodeReturn_split Γ) (hl x hx) (hl y hy) h
  order := by
    have hsub : l.toFinset ⊆ Γ := fun x hx => hl x (List.mem_toFinset.1 hx)
    rw [← firstReturn_firstReturn _ hsub]
    have h2 : firstReturn (R.split Γ).facePerm Γ = R.psi Γ := R.faceReturn_split Γ
    rw [h2]
    exact firstReturn_eq_formPerm hψ

end RotSystem

end SsspFlow
