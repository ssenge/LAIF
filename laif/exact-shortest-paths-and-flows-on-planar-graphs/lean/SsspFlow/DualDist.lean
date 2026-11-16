import SsspFlow.DualFlow

/-!
# Distances in the dual network are distances between faces

The corners of one face of a plane network are joined in the dual network by arcs of length `0` in
both directions, and the arc from the corner of a dart `x` to the corner of `rot⁻¹ x`, through the
nodes `m1 x` and `m2 x`, crosses `x` and has its cost. With natural costs, every walk of the dual network
between two corners gives a walk of the dual map between their faces that costs at most as much, and
every walk of the dual map gives a walk of the dual network of the same cost.

* `dualLen`: the lengths of the dual network for natural costs.
* `faceId`: the face of an identifier.
* `walk_proj`: a walk of the dual network gives a walk of the dual map that costs at most as much.
* `walk_lift`: a walk of the dual map gives a walk of the dual network of the same cost.
* `dist_corner`: the distance between two corners is the least cost of a walk between their faces.
-/

set_option autoImplicit false

namespace SsspFlow.Congest

open XNode Kind FourColor
open scoped ENNReal

section DualDist

variable {V : Type} [Fintype V] [DecidableEq V] {W : Type} [Fintype W] [DecidableEq W]
variable (N : Net V) (e : V × V × Kind ≃ W)

/-- The lengths of the dual network for natural costs `g`; `⊤` where there is no arc. -/
def dualLen (g : V → V → ℕ) (a b : W) : ℕ∞ :=
  match dualW e (fun u v => (g u v : ℤ)) a b with
  | some y => (y.toNat : ℕ∞)
  | none => ⊤

/-- The face of a dart with kind `k` of the dual network. -/
def kindFace (k : Kind) (x : N.G.Dart) : N.toRot.dual.Vertex :=
  match k with
  | corner => N.toRot.dual.tail x
  | m1 => N.toRot.dual.tail (N.rotPerm.symm x)
  | m2 => N.toRot.dual.tail (N.rotPerm.symm x)
  | r1 => N.toRot.dual.tail x
  | r2 => N.toRot.dual.tail (N.rotPerm.symm x)

/-- The face of an identifier, a fixed face `f₀` for the centres and the pendant identifiers. -/
noncomputable def faceId (f₀ : N.toRot.dual.Vertex) (a : W) : N.toRot.dual.Vertex :=
  if h : N.G.Adj (e.symm a).1 (e.symm a).2.1 then kindFace N (e.symm a).2.2 ⟨((e.symm a).1, (e.symm a).2.1), h⟩
  else f₀

variable {N e}

theorem faceId_idx (f₀ : N.toRot.dual.Vertex) (k : Kind) (x : N.G.Dart) :
    faceId N e f₀ (idx N e k x) = kindFace N k x := by
  unfold faceId idx
  simp only [Equiv.symm_apply_apply]
  rw [dif_pos x.adj]

/-- The two corners `y` and `rot⁻¹ (rev y)` lie on one face. -/
theorem dualTail_ring (y : N.G.Dart) :
    N.toRot.dual.tail (N.rotPerm.symm y.symm) = N.toRot.dual.tail y := by
  have h := N.toRot.dual.tail_rot (N.rotPerm.symm y.symm)
  have e1 : N.toRot.dual.rot (N.rotPerm.symm y.symm) = y := by
    show N.toRot.rev (N.toRot.rot (N.rotPerm.symm y.symm)) = y
    simp
  rw [e1] at h
  exact h.symm

/-- The dual dart `x` ends at the face of the corner `rot⁻¹ x`. -/
theorem dualHead_eq (x : N.G.Dart) : N.toRot.dual.head x = N.toRot.dual.tail (N.rotPerm.symm x) := by
  have h := dualTail_ring (N := N) x.symm
  rw [SimpleGraph.Dart.symm_symm] at h
  rw [h]
  rfl

/-- **The arcs of the dual network**: an arc of length `0` stays in its face, and an arc of positive
cost crosses a dart. -/
theorem arc_face (f₀ : N.toRot.dual.Vertex) (g : V → V → ℤ) {a b : W} {y : ℤ} (h : DualArc N e g a b y) :
    (y = 0 ∧ faceId N e f₀ a = faceId N e f₀ b) ∨
      (∃ x : N.G.Dart, y = g x.fst x.snd ∧ N.toRot.dual.IsWalk (faceId N e f₀ a) [x] (faceId N e f₀ b)) := by
  cases h with
  | cost x =>
    right
    refine ⟨x, rfl, ?_, ?_⟩
    · rw [faceId_idx]; rfl
    · rw [faceId_idx]; exact dualHead_eq x
  | m12 x => left; refine ⟨rfl, ?_⟩; rw [faceId_idx, faceId_idx]; rfl
  | m2c x => left; refine ⟨rfl, ?_⟩; rw [faceId_idx, faceId_idx]; rfl
  | cr1 x => left; refine ⟨rfl, ?_⟩; rw [faceId_idx, faceId_idx]; rfl
  | r1c x => left; refine ⟨rfl, ?_⟩; rw [faceId_idx, faceId_idx]; rfl
  | r12 x => left; refine ⟨rfl, ?_⟩; rw [faceId_idx, faceId_idx]; exact (dualTail_ring x).symm
  | r21 x =>
    left; refine ⟨rfl, ?_⟩; rw [faceId_idx, faceId_idx]
    have h := dualTail_ring (N := N) x.symm
    rw [SimpleGraph.Dart.symm_symm] at h
    exact h
  | r2c x => left; refine ⟨rfl, ?_⟩; rw [faceId_idx, faceId_idx]; rfl
  | cr2 x =>
    left; refine ⟨rfl, ?_⟩; rw [faceId_idx, faceId_idx]
    show N.toRot.dual.tail x = N.toRot.dual.tail (N.rotPerm.symm (N.rotPerm x))
    rw [Equiv.symm_apply_apply]

variable (g : V → V → ℕ)

theorem lenTop_dualLen_of {a b : W} {y : ℤ} (h : dualW e (fun u v => (g u v : ℤ)) a b = some y) :
    lenTop (dualLen e g) a b = ((y.toNat : ℕ) : ℝ≥0∞) := by
  simp [lenTop, dualLen, h]

theorem lenTop_idx (k l : Kind) (x y : N.G.Dart) {z : ℤ}
    (h : kindW ((g x.fst x.snd : ℕ) : ℤ) k l = some z) :
    lenTop (dualLen e g) (idx N e k x) (idx N e l y) = ((z.toNat : ℕ) : ℝ≥0∞) :=
  lenTop_dualLen_of g (by rw [dualW_idx]; exact h)

/-- **Walks of the dual network project to walks of the dual map** that cost at most as much. -/
theorem walk_proj (f₀ : N.toRot.dual.Vertex) : ∀ {a b : W} (p : Walk (dualNet N e).G.Adj a b),
    p.wt (lenTop (dualLen e g)) < ⊤ →
    ∃ q : List N.G.Dart, N.toRot.dual.IsWalk (faceId N e f₀ a) q (faceId N e f₀ b) ∧
      (((q.map fun x => g x.fst x.snd).sum : ℕ) : ℝ≥0∞) ≤ p.wt (lenTop (dualLen e g))
  | _, _, .nil a, _ => ⟨[], rfl, by simp⟩
  | a, b, @Walk.cons _ _ _ c _ h p, hw => by
    rw [Walk.wt_cons] at hw ⊢
    have hp : p.wt (lenTop (dualLen e g)) < ⊤ := lt_of_le_of_lt le_add_self hw
    obtain ⟨q, hq, hs⟩ := walk_proj f₀ p hp
    cases hd : dualW e (fun u v => (g u v : ℤ)) a c with
    | none =>
      have : lenTop (dualLen e g) a c = ⊤ := by simp [lenTop, dualLen, hd]
      rw [this, top_add] at hw
      exact absurd hw (lt_irrefl _)
    | some y =>
      rw [lenTop_dualLen_of g hd]
      rcases arc_face f₀ _ (dual_arc h hd) with ⟨rfl, hf⟩ | ⟨x, rfl, hx⟩
      · refine ⟨q, hf ▸ hq, ?_⟩
        simpa using hs
      · refine ⟨x :: q, ⟨hx.1, hx.2 ▸ hq⟩, ?_⟩
        simp only [List.map_cons, List.sum_cons, Int.toNat_natCast, Nat.cast_add]
        exact add_le_add le_rfl hs

theorem adj_of_mem {k l : Kind} {x y : N.G.Dart} (h : node l y ∈ N.xList (node k x)) :
    (dualNet N e).G.Adj (idx N e k x) (idx N e l y) := adj_idx h

/-- A walk of length `0` from the corner `x` to the corner `rot⁻¹ (rev x)` of its face. -/
theorem ring_walk (x : N.G.Dart) : ∃ p : Walk (dualNet N e).G.Adj (idx N e corner x)
    (idx N e corner (N.rotPerm.symm x.symm)), p.wt (lenTop (dualLen e g)) = 0 := by
  have a1 : (dualNet N e).G.Adj (idx N e corner x) (idx N e r1 x) := adj_of_mem (by simp [Net.xList])
  have a2 : (dualNet N e).G.Adj (idx N e r1 x) (idx N e r2 x.symm) := adj_of_mem (by simp [Net.xList])
  have a3 : (dualNet N e).G.Adj (idx N e r2 x.symm) (idx N e corner (N.rotPerm.symm x.symm)) :=
    adj_of_mem (by simp [Net.xList])
  refine ⟨.cons a1 (.cons a2 (.cons a3 (.nil _))), ?_⟩
  simp only [Walk.wt_cons, Walk.wt_nil]
  rw [lenTop_idx g corner r1 x x (z := 0) rfl, lenTop_idx g r1 r2 x x.symm (z := 0) rfl,
    lenTop_idx g r2 corner x.symm _ (z := 0) rfl]
  simp

theorem dualRot_inv (x : N.G.Dart) : (N.toRot.dual.rot)⁻¹ x = N.rotPerm.symm x.symm := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
  show x = N.toRot.rev (N.toRot.rot (N.rotPerm.symm x.symm))
  simp

/-- A walk of length `0` between two corners of one face. -/
theorem face_walk {x y : N.G.Dart} (h : N.toRot.dual.tail x = N.toRot.dual.tail y) :
    ∃ p : Walk (dualNet N e).G.Adj (idx N e corner x) (idx N e corner y), p.wt (lenTop (dualLen e g)) = 0 := by
  have hs : Equiv.Perm.SameCycle N.toRot.dual.rot x y := Quotient.exact h
  obtain ⟨k, hk⟩ := (Equiv.Perm.sameCycle_inv.2 hs).exists_nat_pow_eq
  subst hk
  induction k generalizing x with
  | zero => exact ⟨.nil _, rfl⟩
  | succ k ih =>
    obtain ⟨p₁, h₁⟩ := ring_walk (e := e) g x
    have hs' : Equiv.Perm.SameCycle N.toRot.dual.rot (N.rotPerm.symm x.symm)
        (((N.toRot.dual.rot)⁻¹ ^ k) (N.rotPerm.symm x.symm)) :=
      (Equiv.Perm.sameCycle_inv.1 (Equiv.Perm.SameCycle.refl _ _).pow_right)
    obtain ⟨p₂, h₂⟩ := ih (x := N.rotPerm.symm x.symm) (Quotient.sound hs') hs'
    rw [pow_succ, Equiv.Perm.mul_apply, dualRot_inv]
    exact ⟨p₁.append p₂, by rw [Walk.wt_append, h₁, h₂, add_zero]⟩

/-- A walk crossing the dart `x`, from its corner to the corner `rot⁻¹ x`, of length its cost. -/
theorem cross_walk (x : N.G.Dart) : ∃ p : Walk (dualNet N e).G.Adj (idx N e corner x)
    (idx N e corner (N.rotPerm.symm x)), p.wt (lenTop (dualLen e g)) = g x.fst x.snd := by
  have a1 : (dualNet N e).G.Adj (idx N e corner x) (idx N e m1 x) := adj_of_mem (by simp [Net.xList])
  have a2 : (dualNet N e).G.Adj (idx N e m1 x) (idx N e m2 x) := adj_of_mem (by simp [Net.xList])
  have a3 : (dualNet N e).G.Adj (idx N e m2 x) (idx N e corner (N.rotPerm.symm x)) :=
    adj_of_mem (by simp [Net.xList])
  refine ⟨.cons a1 (.cons a2 (.cons a3 (.nil _))), ?_⟩
  simp only [Walk.wt_cons, Walk.wt_nil]
  rw [lenTop_idx g corner m1 x x (z := (g x.fst x.snd : ℤ)) rfl, lenTop_idx g m1 m2 x x (z := 0) rfl,
    lenTop_idx g m2 corner x _ (z := 0) rfl]
  simp

/-- **Walks of the dual map lift to walks of the dual network** of the same cost, between any corners
of the end faces. -/
theorem walk_lift : ∀ (q : List N.G.Dart) {x y : N.G.Dart},
    N.toRot.dual.IsWalk (N.toRot.dual.tail x) q (N.toRot.dual.tail y) →
    ∃ p : Walk (dualNet N e).G.Adj (idx N e corner x) (idx N e corner y),
      p.wt (lenTop (dualLen e g)) = (((q.map fun x => g x.fst x.snd).sum : ℕ) : ℝ≥0∞)
  | [], x, y, hq => by
    obtain ⟨p, hp⟩ := face_walk (e := e) g hq
    exact ⟨p, by simp [hp]⟩
  | z :: q, x, y, hq => by
    obtain ⟨h1, h2⟩ := hq
    obtain ⟨p₁, e₁⟩ := face_walk (e := e) g h1.symm
    obtain ⟨p₂, e₂⟩ := cross_walk (e := e) g z
    rw [dualHead_eq] at h2
    obtain ⟨p₃, e₃⟩ := walk_lift q h2
    refine ⟨p₁.append (p₂.append p₃), ?_⟩
    rw [Walk.wt_append, Walk.wt_append, e₁, e₂, e₃]
    simp

open Classical in
/-- **Distances of the dual network from one corner** are the least costs of walks of the dual map
between the faces. -/
theorem dist_corner (x₀ y : N.G.Dart) :
    (dualNet N e).dsrcTop (dualLen e g) (fun a => if a = idx N e corner x₀ then 0 else ⊤) (idx N e corner y) =
      ⨅ (q : List N.G.Dart) (_ : N.toRot.dual.IsWalk (N.toRot.dual.tail x₀) q (N.toRot.dual.tail y)),
        (((q.map fun x => g x.fst x.snd).sum : ℕ) : ℝ≥0∞) := by
  unfold Net.dsrcTop dsrc
  apply le_antisymm
  · refine le_iInf₂ fun q hq => ?_
    obtain ⟨p, hp⟩ := walk_lift (e := e) g q hq
    refine (iInf_le _ (idx N e corner x₀)).trans ?_
    simp only [offTop, ite_true, ENat.toENNReal_zero, zero_add]
    exact (iInf₂_le p (fun _ _ => Set.mem_univ _)).trans hp.le
  · refine le_iInf fun a => ?_
    by_cases ha : a = idx N e corner x₀
    · subst ha
      simp only [offTop, ite_true, ENat.toENNReal_zero, zero_add]
      refine le_iInf₂ fun p _ => ?_
      by_cases hw : p.wt (lenTop (dualLen e g)) < ⊤
      · obtain ⟨q, hq, hs⟩ := walk_proj g (N.toRot.dual.tail x₀) p hw
        rw [faceId_idx, faceId_idx] at hq
        exact (iInf₂_le q hq).trans hs
      · rw [not_lt, top_le_iff] at hw
        rw [hw]
        exact le_top
    · simp [offTop, ha]

end DualDist

end SsspFlow.Congest
