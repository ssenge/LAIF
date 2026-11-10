import SsspFlow.Run
import SsspFlow.GHatSplit

/-!
# The annuli of a level

A run of the recursion (`Run.lean`) cuts every annulus that is not a leaf along a step and calls the
sides of the step as annuli of the next level. The root is the annulus of level 1, and the annuli at
depth `ℓ` of a run (`CutPath.Run.nodes`) are its annuli of level `ℓ + 1`. The digon corners of the
steps of all annuli above depth `ℓ` (`CutPath.Run.steps`) are the incisions of the levels before,
also those of the annuli whose sides are not called. With the corners of the root they are the
corners of level `ℓ + 1`.

* `CutPath.Run.subset_level`: the corners of an annulus of a level are corners of the level.
* `CutPath.Run.unreach_level`: a corner of the level that is not a corner of an annulus of the
  level lies out of the reach of that annulus. So the further corners of the level do not change
  the walks from the annulus (`CutPath.Run.isWalk_level_iff`): every annulus of a level is a
  component of the split at all the corners of the level.
* `CutPath.Run.ddist_level`, `CutPath.Run.gdist_level`: for the data with all the corners of the
  level (`CutPath.Run.data`), `λ_t` of an annulus of the level is the distance in the token graph
  between the pieces at `κ0(t)` and `κ1(t)`, and below `M` the distance in the repaired graph
  between copies on their paths.

The proof: every annulus below a side of a step, and every step below it, lies in the component of
that side in the cut along the step (`CutPath.Run.inv`), and the two sides of a step lie in
different components of the cut (`WalkCut.not_gcomp`). This is Lemma N of `notes/GHAT_REPAIR.md`
for a whole level.
-/

set_option autoImplicit false

universe u

namespace SsspFlow

open FourColor
open scoped ENNReal

noncomputable section

namespace RotSystem

section Comp

variable {E : Type*} [Fintype E] [DecidableEq E] {M : RotSystem E}

/-- The two ends of a walk lie in one component. -/
theorem IsWalk.gcomp_tail : ∀ {p : List E} {a b : E}, M.IsWalk (M.tail a) p (M.tail b) →
    M.toHypermap.gcomp a b
  | [], a, b, h => M.toHypermap.gcomp_of_cnode ((M.tail_eq_iff a b).1 h)
  | x :: _, _, _, h => by
    have hx : M.toHypermap.gcomp _ x := M.toHypermap.gcomp_of_cnode ((M.tail_eq_iff _ _).1 h.1.symm)
    have hr : M.toHypermap.gcomp _ (M.rev x) :=
      connect_trans hx (connect_of_rel (M.toHypermap.glinkE _))
    exact connect_trans hr (IsWalk.gcomp_tail (a := M.rev x) h.2)

end Comp

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace CutPath

variable {C : R.CutPath} {g : D → ℝ≥0∞}

namespace Live

variable {Γ : Finset (D × Bool)} (L : C.Live g Γ)

/-- The corners of the boundary of a live annulus lie in one component of the split. -/
theorem gcomp_bound {x y : D × Bool}
    (hx : x ∈ liveBoundary L.κ0 L.κ1 L.xa L.xb L.ya L.yb L.La L.Lb)
    (hy : y ∈ liveBoundary L.κ0 L.κ1 L.xa L.xb L.ya L.yb L.La L.Lb) :
    (R.double.split Γ).toHypermap.gcomp x y :=
  R.double.gcomp_split_of_fconnect_psi (L.bound.fconnect hx hy)

theorem κ0_mem {t : ℕ} (h1 : L.xa ≤ t) (h2 : t ≤ L.xb) :
    L.κ0 t ∈ liveBoundary L.κ0 L.κ1 L.xa L.xb L.ya L.yb L.La L.Lb := by
  unfold liveBoundary
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (mem_cornerSeg.2 ⟨t, h1, h2, rfl⟩)))

theorem κ1_mem {t : ℕ} (h1 : L.ya ≤ t) (h2 : t ≤ L.yb) :
    L.κ1 t ∈ liveBoundary L.κ0 L.κ1 L.xa L.xb L.ya L.yb L.La L.Lb := by
  unfold liveBoundary
  simp only [List.mem_append, List.mem_reverse]
  exact Or.inl (Or.inr (mem_cornerSeg.2 ⟨t, h1, h2, rfl⟩))

/-- A corner `κ0(t)` lies in the component of `κ0(x_a)`. -/
theorem gcomp_κ0 {t : ℕ} (h1 : L.xa ≤ t) (h2 : t ≤ L.xb) :
    (R.double.split Γ).toHypermap.gcomp (L.κ0 L.xa) (L.κ0 t) :=
  L.gcomp_bound (L.κ0_mem le_rfl L.le_x) (L.κ0_mem h1 h2)

/-- A corner `κ1(t)` lies in the component of `κ0(x_a)`. -/
theorem gcomp_κ1 {t : ℕ} (h1 : L.ya ≤ t) (h2 : t ≤ L.yb) :
    (R.double.split Γ).toHypermap.gcomp (L.κ0 L.xa) (L.κ1 t) :=
  L.gcomp_bound (L.κ0_mem le_rfl L.le_x) (L.κ1_mem h1 h2)

namespace Step

variable {L} (S : L.Step)

/-- The digon corners of the edges of a step. -/
def corners : Finset (D × Bool) :=
  (Finset.range S.n).image (fun j => ((S.q j).1, false)) ∪
    (Finset.range S.n).image (fun j => (R.rev (S.q j).1, false))

theorem mem_corners {z : D × Bool} : z ∈ S.corners ↔
    ∃ j, j < S.n ∧ (z = ((S.q j).1, false) ∨ z = (R.rev (S.q j).1, false)) := by
  simp only [corners, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact ⟨j, hj, Or.inl rfl⟩
    · exact ⟨j, hj, Or.inr rfl⟩
  · rintro ⟨j, hj, rfl | rfl⟩
    · exact Or.inl ⟨j, hj, rfl⟩
    · exact Or.inr ⟨j, hj, rfl⟩

theorem pair_corners {d : D} (h : (d, false) ∈ S.corners) : (R.rev d, false) ∈ S.corners := by
  obtain ⟨j, hj, e | e⟩ := S.mem_corners.1 h
  · obtain rfl : d = (S.q j).1 := congrArg Prod.fst e
    exact S.mem_corners.2 ⟨j, hj, Or.inr rfl⟩
  · obtain rfl : d = R.rev (S.q j).1 := congrArg Prod.fst e
    exact S.mem_corners.2 ⟨j, hj, Or.inl (by rw [R.rev_rev])⟩

/-- The digon corners of a step lie in the component of `κ0(x)`. -/
theorem gcomp_corners {z : D × Bool} (hz : z ∈ S.corners) (hzΓ : z ∉ Γ) :
    (R.double.split Γ).toHypermap.gcomp (L.κ0 S.x) z := by
  obtain ⟨j, hj, rfl | rfl⟩ := S.mem_corners.1 hz
  · exact connect_trans (gcomp_walk (M := R.double.split Γ) S.start S.walk j hj).1
      ((R.double.split Γ).toHypermap.gcomp_of_cnode
        (fconnect_symm (fconnect_digon (R := R) hzΓ (S.q j).2)))
  · exact connect_trans (gcomp_walk (M := R.double.split Γ) S.start S.walk j hj).2
      ((R.double.split Γ).toHypermap.gcomp_of_cnode
        (fconnect_symm (fconnect_digon (R := R) hzΓ (!(S.q j).2))))

end Step

section Cuts

variable (hR : R.Planar) (hC : R.Connected) (S : L.Step)

theorem mem_hiCut_Γ'
    (noB : ∀ j, 0 < j → j < S.n → ∀ c ∈ L.Lb, ¬ fconnect (R.double.split Γ).rot (S.q j) c)
    (hdeg : L.hiA S.x S.y ≠ [] ∨ 1 < S.n ∨ ((S.q 0).1, false) ∉ Γ) {z : D × Bool} :
    z ∈ (L.hiCut hR hC S noB hdeg).Γ' ↔ z ∈ Γ ∪ S.corners := by
  rw [WalkCut.Γ', WalkCut.mem_Γs, Finset.mem_union, S.mem_corners]
  simp only [hiCut_n, hiCut_q, WalkCut.mc, WalkCut.rc]

theorem mem_loCut_Γ'
    (noA : ∀ j, 0 < j → j < S.n → ∀ c ∈ L.La, ¬ fconnect (R.double.split Γ).rot (S.q j) c)
    (hdeg : L.hiB S.x S.y ≠ [] ∨ 1 < S.n ∨ ((S.rq 0).1, false) ∉ Γ) {z : D × Bool} :
    z ∈ (L.loCut hR hC S noA hdeg).Γ' ↔ z ∈ Γ ∪ S.corners := by
  rw [WalkCut.Γ', WalkCut.mem_Γs, Finset.mem_union, S.mem_corners]
  simp only [loCut_n, loCut_q, WalkCut.mc, WalkCut.rc, Step.rq]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨i, hi, h | h⟩
    · exact ⟨S.n - 1 - i, by omega, Or.inr h⟩
    · refine ⟨S.n - 1 - i, by omega, Or.inl ?_⟩
      rw [h]
      exact congrArg (·, false) (R.rev_rev _)
  · rintro ⟨j, hj, h | h⟩
    · have e : S.n - 1 - (S.n - 1 - j) = j := by omega
      refine ⟨S.n - 1 - j, by omega, Or.inr ?_⟩
      rw [e, h]
      exact congrArg (·, false) (R.rev_rev _).symm
    · have e : S.n - 1 - (S.n - 1 - j) = j := by omega
      refine ⟨S.n - 1 - j, by omega, Or.inl ?_⟩
      rw [e]
      exact h

theorem hiCut_Γ'
    (noB : ∀ j, 0 < j → j < S.n → ∀ c ∈ L.Lb, ¬ fconnect (R.double.split Γ).rot (S.q j) c)
    (hdeg : L.hiA S.x S.y ≠ [] ∨ 1 < S.n ∨ ((S.q 0).1, false) ∉ Γ) :
    (L.hiCut hR hC S noB hdeg).Γ' = Γ ∪ S.corners :=
  Finset.ext fun _ => L.mem_hiCut_Γ' hR hC S noB hdeg

include hR hC in
/-- **The two sides of a step.** If both sides of a step are cut, `κ0(x)` and `κ1(y)` lie in
different components of the cut. -/
theorem not_gcomp_sides
    (noA : ∀ j, 0 < j → j < S.n → ∀ c ∈ L.La, ¬ fconnect (R.double.split Γ).rot (S.q j) c)
    (hdegA : L.hiB S.x S.y ≠ [] ∨ 1 < S.n ∨ ((S.rq 0).1, false) ∉ Γ)
    (noB : ∀ j, 0 < j → j < S.n → ∀ c ∈ L.Lb, ¬ fconnect (R.double.split Γ).rot (S.q j) c)
    (hdegB : L.hiA S.x S.y ≠ [] ∨ 1 < S.n ∨ ((S.q 0).1, false) ∉ Γ) :
    ¬ (R.double.split (Γ ∪ S.corners)).toHypermap.gcomp (L.κ0 S.x) (L.κ1 S.y) := by
  have h := (L.hiCut hR hC S noB hdegB).not_gcomp hR hC L.skel fun hΓ => by
    have h1 : (!(S.q (S.n - 1)).2) = true := (L.loCut hR hC S noA hdegA).first hΓ
    simpa using h1
  rw [L.hiCut_Γ' hR hC S noB hdegB, hiCut_ka, hiCut_kb] at h
  exact h

end Cuts

end Live

section Run

variable {hR : R.Planar} {hC : R.Connected} {hg : ∀ x, g (R.rev x) = g x}

mutual
/-- The annuli of a run at depth `ℓ`, with their corners: its annuli of level `ℓ + 1`. -/
def Run.nodes : {Γ : Finset (D × Bool)} → {L : C.Live g Γ} → {j k : ℕ} →
    Run hR hC hg Γ L j k → ℕ → List (Σ Γ' : Finset (D × Bool), C.Live g Γ')
  | Γ, L, _, _, .leaf .., 0 => [⟨Γ, L⟩]
  | _, _, _, _, .leaf .., _ + 1 => []
  | Γ, L, _, _, .node .., 0 => [⟨Γ, L⟩]
  | _, _, _, _, .node _ _ _ _ _ _ _ _ _ _ _ _ _ left right, ℓ + 1 => left.nodes ℓ ++ right.nodes ℓ
/-- The annuli below a side, at depth `ℓ` below it. -/
def SideA.nodes : {Γ : Finset (D × Bool)} → {L : C.Live g Γ} → {p : List (D × Bool)} → {i : ℕ} →
    {S : L.Step} → {lo hi : ℕ} → SideA hR hC hg Γ L p i S lo hi → ℕ →
      List (Σ Γ' : Finset (D × Bool), C.Live g Γ')
  | _, _, _, _, _, _, _, .overlap .., _ => []
  | _, _, _, _, _, _, _, .child _ _ r, ℓ => r.nodes ℓ
  | _, _, _, _, _, _, _, .empty _, _ => []
/-- The annuli below a side, at depth `ℓ` below it. -/
def SideB.nodes : {Γ : Finset (D × Bool)} → {L : C.Live g Γ} → {p : List (D × Bool)} → {i : ℕ} →
    {S : L.Step} → {lo hi : ℕ} → SideB hR hC hg Γ L p i S lo hi → ℕ →
      List (Σ Γ' : Finset (D × Bool), C.Live g Γ')
  | _, _, _, _, _, _, _, .overlap .., _ => []
  | _, _, _, _, _, _, _, .child _ _ r, ℓ => r.nodes ℓ
  | _, _, _, _, _, _, _, .empty _, _ => []
end

mutual
/-- The digon corners of the steps of the annuli of a run above depth `ℓ`: its incisions before
level `ℓ + 1`. -/
def Run.steps : {Γ : Finset (D × Bool)} → {L : C.Live g Γ} → {j k : ℕ} →
    Run hR hC hg Γ L j k → ℕ → Finset (D × Bool)
  | _, _, _, _, .leaf .., _ => ∅
  | _, _, _, _, .node .., 0 => ∅
  | _, _, _, _, .node _ _ _ _ _ _ _ _ _ _ _ S _ left right, ℓ + 1 =>
    S.corners ∪ left.steps ℓ ∪ right.steps ℓ
/-- The digon corners of the steps below a side, above depth `ℓ` below it. -/
def SideA.steps : {Γ : Finset (D × Bool)} → {L : C.Live g Γ} → {p : List (D × Bool)} → {i : ℕ} →
    {S : L.Step} → {lo hi : ℕ} → SideA hR hC hg Γ L p i S lo hi → ℕ → Finset (D × Bool)
  | _, _, _, _, _, _, _, .overlap .., _ => ∅
  | _, _, _, _, _, _, _, .child _ _ r, ℓ => r.steps ℓ
  | _, _, _, _, _, _, _, .empty _, _ => ∅
/-- The digon corners of the steps below a side, above depth `ℓ` below it. -/
def SideB.steps : {Γ : Finset (D × Bool)} → {L : C.Live g Γ} → {p : List (D × Bool)} → {i : ℕ} →
    {S : L.Step} → {lo hi : ℕ} → SideB hR hC hg Γ L p i S lo hi → ℕ → Finset (D × Bool)
  | _, _, _, _, _, _, _, .overlap .., _ => ∅
  | _, _, _, _, _, _, _, .child _ _ r, ℓ => r.steps ℓ
  | _, _, _, _, _, _, _, .empty _, _ => ∅
end

mutual
/-- The incisions of a run come in digon pairs. -/
theorem Run.pair_steps : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ : ℕ) (d : D), (d, false) ∈ r.steps ℓ →
      (R.rev d, false) ∈ r.steps ℓ
  | _, _, _, _, .leaf .., _, _, h => by simp [Run.steps] at h
  | _, _, _, _, .node .., 0, _, h => by simp [Run.steps] at h
  | _, _, _, _, .node _ _ _ _ _ _ _ _ _ _ _ S _ left right, ℓ + 1, d, h => by
    simp only [Run.steps, Finset.mem_union] at h ⊢
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (S.pair_corners h))
    · exact Or.inl (Or.inr (SideA.pair_steps left ℓ d h))
    · exact Or.inr (SideB.pair_steps right ℓ d h)
theorem SideA.pair_steps : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ : ℕ) (d : D),
      (d, false) ∈ s.steps ℓ → (R.rev d, false) ∈ s.steps ℓ
  | _, _, _, _, _, _, _, .overlap .., _, _, h => by simp [SideA.steps] at h
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, d, h => by
    simp only [SideA.steps] at h ⊢
    exact Run.pair_steps r ℓ d h
  | _, _, _, _, _, _, _, .empty _, _, _, h => by simp [SideA.steps] at h
theorem SideB.pair_steps : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ : ℕ) (d : D),
      (d, false) ∈ s.steps ℓ → (R.rev d, false) ∈ s.steps ℓ
  | _, _, _, _, _, _, _, .overlap .., _, _, h => by simp [SideB.steps] at h
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, d, h => by
    simp only [SideB.steps] at h ⊢
    exact Run.pair_steps r ℓ d h
  | _, _, _, _, _, _, _, .empty _, _, _, h => by simp [SideB.steps] at h
end

mutual
/-- **Every annulus and every incision below an annulus lie in its component.** The corners of an
annulus of a run at depth `ℓ` hold those of the root and lie among the corners of the root and the
incisions before level `ℓ`, and the annulus and the incisions off the corners of the root lie in
the component of `κ0(x_a)` of the root. -/
theorem Run.inv : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ : ℕ),
    (∀ A ∈ r.nodes ℓ, Γ ⊆ A.1 ∧ A.1 ⊆ Γ ∪ r.steps ℓ ∧
      (R.double.split Γ).toHypermap.gcomp (L.κ0 L.xa) (A.2.κ0 A.2.xa)) ∧
    (∀ w ∈ r.steps ℓ, w ∉ Γ → (R.double.split Γ).toHypermap.gcomp (L.κ0 L.xa) w)
  | Γ, L, _, _, .leaf .., 0 => by
    refine ⟨fun A hA => ?_, fun w hw => by simp [Run.steps] at hw⟩
    simp only [Run.nodes, List.mem_singleton] at hA
    subst hA
    exact ⟨subset_rfl, Finset.subset_union_left, connect_refl _⟩
  | _, _, _, _, .leaf .., _ + 1 => ⟨fun A hA => by simp [Run.nodes] at hA,
      fun w hw => by simp [Run.steps] at hw⟩
  | Γ, L, _, _, .node .., 0 => by
    refine ⟨fun A hA => ?_, fun w hw => by simp [Run.steps] at hw⟩
    simp only [Run.nodes, List.mem_singleton] at hA
    subst hA
    exact ⟨subset_rfl, Finset.subset_union_left, connect_refl _⟩
  | Γ, L, _, _, .node _ _ _ _ _ _ _ _ _ _ _ S _ left right, ℓ + 1 => by
    obtain ⟨ihA, ihA'⟩ := SideA.inv left ℓ
    obtain ⟨ihB, ihB'⟩ := SideB.inv right ℓ
    have hsub : Γ ⊆ Γ ∪ S.corners := Finset.subset_union_left
    have g1 : (R.double.split Γ).toHypermap.gcomp (L.κ0 L.xa) (L.κ1 S.y) :=
      L.gcomp_κ1 S.hya S.hyb
    have g0 : (R.double.split Γ).toHypermap.gcomp (L.κ0 L.xa) (L.κ0 S.x) :=
      L.gcomp_κ0 S.hxa S.hxb
    refine ⟨fun A hA => ?_, fun w hw hwΓ => ?_⟩
    · simp only [Run.nodes, List.mem_append] at hA
      rcases hA with hA | hA
      · obtain ⟨h1, h2, h3⟩ := ihA A hA
        refine ⟨hsub.trans h1, fun z hz => ?_,
          connect_trans g1 (RootedTree.gcomp_split_mono hsub h3)⟩
        have h := h2 hz
        simp only [Run.steps, Finset.mem_union] at h ⊢
        rcases h with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inl (Or.inr h))
      · obtain ⟨h1, h2, h3⟩ := ihB A hA
        refine ⟨hsub.trans h1, fun z hz => ?_,
          connect_trans g0 (RootedTree.gcomp_split_mono hsub h3)⟩
        have h := h2 hz
        simp only [Run.steps, Finset.mem_union] at h ⊢
        rcases h with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inr h)
    · simp only [Run.steps, Finset.mem_union] at hw
      by_cases hS : w ∈ S.corners
      · exact connect_trans g0 (S.gcomp_corners hS hwΓ)
      have hw' : w ∉ Γ ∪ S.corners := fun h => (Finset.mem_union.1 h).elim hwΓ hS
      rcases hw with (h | h) | h
      · exact absurd h hS
      · exact connect_trans g1 (RootedTree.gcomp_split_mono hsub (ihA' w h hw'))
      · exact connect_trans g0 (RootedTree.gcomp_split_mono hsub (ihB' w h hw'))
theorem SideA.inv : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ : ℕ),
    (∀ A ∈ s.nodes ℓ, Γ ∪ S.corners ⊆ A.1 ∧ A.1 ⊆ Γ ∪ S.corners ∪ s.steps ℓ ∧
      (R.double.split (Γ ∪ S.corners)).toHypermap.gcomp (L.κ1 S.y) (A.2.κ0 A.2.xa)) ∧
    (∀ w ∈ s.steps ℓ, w ∉ Γ ∪ S.corners →
      (R.double.split (Γ ∪ S.corners)).toHypermap.gcomp (L.κ1 S.y) w)
  | _, _, _, _, _, _, _, .overlap .., _ => ⟨fun A hA => by simp [SideA.nodes] at hA,
      fun w hw => by simp [SideA.steps] at hw⟩
  | Γ, L, _, _, S, _, _, .child noA hdeg r, ℓ => by
    obtain ⟨ih, ih'⟩ := Run.inv r ℓ
    have e : ∀ {z}, z ∈ (L.loCut hR hC S noA hdeg).Γ' ↔ z ∈ Γ ∪ S.corners :=
      L.mem_loCut_Γ' hR hC S noA hdeg
    have hsub : Γ ∪ S.corners ⊆ (L.loCut hR hC S noA hdeg).Γ' := fun z hz => e.2 hz
    have gb : (R.double.split (Γ ∪ S.corners)).toHypermap.gcomp (L.κ1 S.y)
        ((L.lo hR hC S noA hdeg hg).κ0 (L.lo hR hC S noA hdeg hg).xa) :=
      RootedTree.gcomp_split_mono hsub ((L.lo hR hC S noA hdeg hg).gcomp_bound
        ((L.mem_lo hR hC S noA hdeg).2 (List.mem_append_left _ List.mem_cons_self))
        ((L.lo hR hC S noA hdeg hg).κ0_mem le_rfl (L.lo hR hC S noA hdeg hg).le_x))
    refine ⟨fun A hA => ?_, fun w hw hwΓ => ?_⟩
    · simp only [SideA.nodes] at hA
      obtain ⟨h1, h2, h3⟩ := ih A hA
      refine ⟨hsub.trans h1, fun z hz => ?_,
        connect_trans gb (RootedTree.gcomp_split_mono hsub h3)⟩
      have h := h2 hz
      rw [Finset.mem_union, e] at h
      simpa only [SideA.steps, Finset.mem_union] using h
    · simp only [SideA.steps] at hw
      exact connect_trans gb (RootedTree.gcomp_split_mono hsub (ih' w hw fun h => hwΓ (e.1 h)))
  | _, _, _, _, _, _, _, .empty _, _ => ⟨fun A hA => by simp [SideA.nodes] at hA,
      fun w hw => by simp [SideA.steps] at hw⟩
theorem SideB.inv : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ : ℕ),
    (∀ A ∈ s.nodes ℓ, Γ ∪ S.corners ⊆ A.1 ∧ A.1 ⊆ Γ ∪ S.corners ∪ s.steps ℓ ∧
      (R.double.split (Γ ∪ S.corners)).toHypermap.gcomp (L.κ0 S.x) (A.2.κ0 A.2.xa)) ∧
    (∀ w ∈ s.steps ℓ, w ∉ Γ ∪ S.corners →
      (R.double.split (Γ ∪ S.corners)).toHypermap.gcomp (L.κ0 S.x) w)
  | _, _, _, _, _, _, _, .overlap .., _ => ⟨fun A hA => by simp [SideB.nodes] at hA,
      fun w hw => by simp [SideB.steps] at hw⟩
  | Γ, L, _, _, S, _, _, .child noB hdeg r, ℓ => by
    obtain ⟨ih, ih'⟩ := Run.inv r ℓ
    have e : ∀ {z}, z ∈ (L.hiCut hR hC S noB hdeg).Γ' ↔ z ∈ Γ ∪ S.corners :=
      L.mem_hiCut_Γ' hR hC S noB hdeg
    have hsub : Γ ∪ S.corners ⊆ (L.hiCut hR hC S noB hdeg).Γ' := fun z hz => e.2 hz
    refine ⟨fun A hA => ?_, fun w hw hwΓ => ?_⟩
    · simp only [SideB.nodes] at hA
      obtain ⟨h1, h2, h3⟩ := ih A hA
      refine ⟨hsub.trans h1, fun z hz => ?_, RootedTree.gcomp_split_mono hsub h3⟩
      have h := h2 hz
      rw [Finset.mem_union, e] at h
      simpa only [SideB.steps, Finset.mem_union] using h
    · simp only [SideB.steps] at hw
      exact RootedTree.gcomp_split_mono hsub (ih' w hw fun h => hwΓ (e.1 h))
  | _, _, _, _, _, _, _, .empty _, _ => ⟨fun A hA => by simp [SideB.nodes] at hA,
      fun w hw => by simp [SideB.steps] at hw⟩
end

/-- An annulus below one side of a step does not reach an incision below the other side. -/
theorem unreach_sides {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi lo' hi' : ℕ} (sA : SideA hR hC hg Γ L p i S lo hi)
    (sB : SideB hR hC hg Γ L p i S lo' hi') (ℓ : ℕ)
    (hsep : ¬ (R.double.split (Γ ∪ S.corners)).toHypermap.gcomp (L.κ0 S.x) (L.κ1 S.y))
    {A : Σ Γ' : Finset (D × Bool), C.Live g Γ'} {w : D × Bool}
    (hw : (A ∈ sA.nodes ℓ ∧ w ∈ sB.steps ℓ) ∨ (A ∈ sB.nodes ℓ ∧ w ∈ sA.steps ℓ))
    (hwA : w ∉ A.1) {t : ℕ} (h1 : A.2.xa ≤ t) (h2 : t ≤ A.2.xb) (q : List (D × Bool)) :
    ¬ (R.double.split A.1).IsWalk ((R.double.split A.1).tail (A.2.κ0 t)) q
      ((R.double.split A.1).tail w) := by
  intro hq
  have key : ∀ a b : D × Bool, Γ ∪ S.corners ⊆ A.1 →
      (R.double.split (Γ ∪ S.corners)).toHypermap.gcomp a (A.2.κ0 A.2.xa) →
      (R.double.split (Γ ∪ S.corners)).toHypermap.gcomp b w →
      (R.double.split (Γ ∪ S.corners)).toHypermap.gcomp a b := fun a b hsub ha hb =>
    connect_trans (connect_trans ha (RootedTree.gcomp_split_mono hsub (A.2.gcomp_κ0 h1 h2)))
      (connect_trans (IsWalk.gcomp_tail (isWalk_of_split_subset hsub hq))
        ((R.double.split (Γ ∪ S.corners)).toHypermap.glinkC _ _ hb))
  rcases hw with ⟨hA, hw⟩ | ⟨hA, hw⟩
  · obtain ⟨hsub, -, h3⟩ := (SideA.inv sA ℓ).1 A hA
    exact hsep ((R.double.split (Γ ∪ S.corners)).toHypermap.glinkC _ _
      (key _ _ hsub h3 ((SideB.inv sB ℓ).2 w hw fun h => hwA (hsub h))))
  · obtain ⟨hsub, -, h3⟩ := (SideB.inv sB ℓ).1 A hA
    exact hsep (key _ _ hsub h3 ((SideA.inv sA ℓ).2 w hw fun h => hwA (hsub h)))

mutual
/-- An incision above depth `ℓ` that is not a corner of an annulus at depth `ℓ` lies out of the
reach of that annulus. -/
theorem Run.unreach : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ : ℕ), ∀ A ∈ r.nodes ℓ, ∀ w ∈ r.steps ℓ, w ∉ A.1 →
      ∀ t, A.2.xa ≤ t → t ≤ A.2.xb → ∀ q : List (D × Bool),
        ¬ (R.double.split A.1).IsWalk ((R.double.split A.1).tail (A.2.κ0 t)) q
          ((R.double.split A.1).tail w)
  | _, _, _, _, .leaf .., _ => fun _ _ w hw => by simp [Run.steps] at hw
  | _, _, _, _, .node .., 0 => fun _ _ w hw => by simp [Run.steps] at hw
  | _, L, _, _, .node _ _ _ _ _ _ _ _ _ _ _ S _ left right, ℓ + 1 => by
    intro A hA w hw hwA t h1 h2 q
    simp only [Run.nodes, List.mem_append] at hA
    simp only [Run.steps, Finset.mem_union] at hw
    have hcor : w ∉ S.corners := fun h => by
      rcases hA with hA | hA
      · exact hwA (((SideA.inv left ℓ).1 A hA).1 (Finset.mem_union_right _ h))
      · exact hwA (((SideB.inv right ℓ).1 A hA).1 (Finset.mem_union_right _ h))
    rcases hw with (hw | hw) | hw
    · exact absurd hw hcor
    · rcases hA with hA | hA
      · exact SideA.unreach left ℓ A hA w hw hwA t h1 h2 q
      · cases left with
        | overlap => simp [SideA.steps] at hw
        | empty => simp [SideA.steps] at hw
        | child noA hdegA rA =>
          cases right with
          | overlap => simp [SideB.nodes] at hA
          | empty => simp [SideB.nodes] at hA
          | child noB hdegB rB =>
            exact unreach_sides _ _ ℓ (L.not_gcomp_sides hR hC S noA hdegA noB hdegB)
              (Or.inr ⟨hA, hw⟩) hwA h1 h2 q
    · rcases hA with hA | hA
      · cases left with
        | overlap => simp [SideA.nodes] at hA
        | empty => simp [SideA.nodes] at hA
        | child noA hdegA rA =>
          cases right with
          | overlap => simp [SideB.steps] at hw
          | empty => simp [SideB.steps] at hw
          | child noB hdegB rB =>
            exact unreach_sides _ _ ℓ (L.not_gcomp_sides hR hC S noA hdegA noB hdegB)
              (Or.inl ⟨hA, hw⟩) hwA h1 h2 q
      · exact SideB.unreach right ℓ A hA w hw hwA t h1 h2 q
theorem SideA.unreach : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ : ℕ),
      ∀ A ∈ s.nodes ℓ, ∀ w ∈ s.steps ℓ, w ∉ A.1 →
      ∀ t, A.2.xa ≤ t → t ≤ A.2.xb → ∀ q : List (D × Bool),
        ¬ (R.double.split A.1).IsWalk ((R.double.split A.1).tail (A.2.κ0 t)) q
          ((R.double.split A.1).tail w)
  | _, _, _, _, _, _, _, .overlap .., _ => fun _ _ w hw => by simp [SideA.steps] at hw
  | _, _, _, _, _, _, _, .child _ _ r, ℓ => by
    simp only [SideA.nodes, SideA.steps]
    exact Run.unreach r ℓ
  | _, _, _, _, _, _, _, .empty _, _ => fun _ _ w hw => by simp [SideA.steps] at hw
theorem SideB.unreach : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ : ℕ),
      ∀ A ∈ s.nodes ℓ, ∀ w ∈ s.steps ℓ, w ∉ A.1 →
      ∀ t, A.2.xa ≤ t → t ≤ A.2.xb → ∀ q : List (D × Bool),
        ¬ (R.double.split A.1).IsWalk ((R.double.split A.1).tail (A.2.κ0 t)) q
          ((R.double.split A.1).tail w)
  | _, _, _, _, _, _, _, .overlap .., _ => fun _ _ w hw => by simp [SideB.steps] at hw
  | _, _, _, _, _, _, _, .child _ _ r, ℓ => by
    simp only [SideB.nodes, SideB.steps]
    exact Run.unreach r ℓ
  | _, _, _, _, _, _, _, .empty _, _ => fun _ _ w hw => by simp [SideB.steps] at hw
end

variable {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}

/-- The corners of an annulus at depth `ℓ` are corners of its level. -/
theorem Run.subset_level (r : Run hR hC hg Γ L j k) (ℓ : ℕ)
    {A : Σ Γ' : Finset (D × Bool), C.Live g Γ'} (hA : A ∈ r.nodes ℓ) : A.1 ⊆ Γ ∪ r.steps ℓ :=
  ((r.inv ℓ).1 A hA).2.1

/-- **Lemma N for a level.** A corner of the level of the annuli at depth `ℓ` that is not a corner
of such an annulus lies out of the reach of that annulus. -/
theorem Run.unreach_level (r : Run hR hC hg Γ L j k) (ℓ : ℕ)
    {A : Σ Γ' : Finset (D × Bool), C.Live g Γ'} (hA : A ∈ r.nodes ℓ) {w : D × Bool}
    (hw : w ∈ Γ ∪ r.steps ℓ) (hwA : w ∉ A.1) {t : ℕ} (h1 : A.2.xa ≤ t) (h2 : t ≤ A.2.xb)
    (q : List (D × Bool)) :
    ¬ (R.double.split A.1).IsWalk ((R.double.split A.1).tail (A.2.κ0 t)) q
      ((R.double.split A.1).tail w) := by
  rcases Finset.mem_union.1 hw with hw | hw
  · exact absurd (((r.inv ℓ).1 A hA).1 hw) hwA
  · exact r.unreach ℓ A hA w hw hwA t h1 h2 q

/-- **The annuli of a level are components.** From every vertex of an annulus at depth `ℓ`, the
walks in the split at all the corners of its level are the walks in the split at the corners of
the annulus. -/
theorem Run.isWalk_level_iff (r : Run hR hC hg Γ L j k) (ℓ : ℕ)
    {A : Σ Γ' : Finset (D × Bool), C.Live g Γ'} (hA : A ∈ r.nodes ℓ) {t : ℕ} (h1 : A.2.xa ≤ t)
    (h2 : t ≤ A.2.xb) (p : List (D × Bool)) {u : D × Bool}
    (hu : ∃ q, (R.double.split A.1).IsWalk ((R.double.split A.1).tail (A.2.κ0 t)) q
      ((R.double.split A.1).tail u)) (y : D × Bool) :
    (R.double.split (Γ ∪ r.steps ℓ)).IsWalk ((R.double.split (Γ ∪ r.steps ℓ)).tail u) p
        ((R.double.split (Γ ∪ r.steps ℓ)).tail y) ↔
      (R.double.split A.1).IsWalk ((R.double.split A.1).tail u) p ((R.double.split A.1).tail y) :=
  R.double.isWalk_split_split_iff (r.subset_level ℓ hA)
    (fun _ hw hwA q => r.unreach_level ℓ hA hw hwA h1 h2 q) p hu y

/-- The corners of a level come in digon pairs. -/
theorem Run.pair_level (r : Run hR hC hg Γ L j k) (ℓ : ℕ) (d : D)
    (hd : (d, false) ∈ Γ ∪ r.steps ℓ) : (R.rev d, false) ∈ Γ ∪ r.steps ℓ := by
  rcases Finset.mem_union.1 hd with h | h
  · exact Finset.mem_union_left _ (L.pair d h)
  · exact Finset.mem_union_right _ (r.pair_steps ℓ d h)

end Run

end CutPath

section Tokens

variable {E : Type u} [Fintype E] [DecidableEq E] {G : RotSystem E} {C : G.dual.CutPath}
  {g : E → ℝ≥0∞} {hR : G.dual.Planar} {hC : G.dual.Connected} {hg : ∀ x, g (G.dual.rev x) = g x}
  {Γ : Finset (E × Bool)} {L : C.Live g Γ} {j k : ℕ}

namespace CutPath

/-- The data of the token graph of a level: all the corners of the level, with any modes and any
hosts of the unincised pairs. -/
def Run.data (r : Run hR hC hg Γ L j k) (ℓ : ℕ) (modeL hostT : E → Bool)
    (hhost : ∀ d, (d, false) ∉ Γ ∪ r.steps ℓ → hostT (G.rev d) = !hostT d) : G.RData :=
  RData.ofCorners (G := G) (Γ ∪ r.steps ℓ) (r.pair_level ℓ) modeL hostT hhost

variable (r : Run hR hC hg Γ L j k) (ℓ : ℕ) (modeL hostT : E → Bool)
  (hhost : ∀ d, (d, false) ∉ Γ ∪ r.steps ℓ → hostT (G.rev d) = !hostT d)

theorem Run.data_Γ : (r.data ℓ modeL hostT hhost).Γ = Γ ∪ r.steps ℓ :=
  RData.Γ_ofCorners (G := G) _ (r.pair_level ℓ) modeL hostT hhost

theorem Run.subset_data {A : Σ Γ' : Finset (E × Bool), C.Live g Γ'} (hA : A ∈ r.nodes ℓ) :
    A.1 ⊆ (r.data ℓ modeL hostT hhost).Γ := by
  rw [r.data_Γ]
  exact r.subset_level ℓ hA

theorem Run.unreach_data {A : Σ Γ' : Finset (E × Bool), C.Live g Γ'} (hA : A ∈ r.nodes ℓ)
    {t : ℕ} (h1 : A.2.xa ≤ t) (h2 : t ≤ A.2.xb) :
    ∀ w ∈ (r.data ℓ modeL hostT hhost).Γ, w ∉ A.1 → ∀ q : List (E × Bool),
      ¬ (G.dual.double.split A.1).IsWalk ((G.dual.double.split A.1).tail (A.2.κ0 t)) q
        ((G.dual.double.split A.1).tail w) := by
  intro w hw hwA q
  rw [r.data_Γ] at hw
  exact r.unreach_level ℓ hA hw hwA h1 h2 q

variable (c : E → ℝ) (hc0 : ∀ d, 0 ≤ c d) (hcr : ∀ d, c (G.rev d) = c d)
  (hgc : ∀ d, g d = ENNReal.ofReal (c d))
include hc0 hcr hgc

/-- **Lemma N for a level, the distances.** For weights `c ≥ 0` that agree on the two darts of an
edge and give `g`, `λ_t` of an annulus at depth `ℓ` is the distance in the token graph of its level
between its pieces at `κ0(t)` and `κ1(t)`. -/
theorem Run.ddist_level {A : Σ Γ' : Finset (E × Bool), C.Live g Γ'} (hA : A ∈ r.nodes ℓ) {t : ℕ}
    (h1 : A.2.xa ≤ t) (h2 : A.2.ya ≤ t) (h3 : t ≤ A.2.xb) (h4 : t ≤ A.2.yb) :
    (r.data ℓ modeL hostT hhost).ddist (fun x => c x.1.1)
        ((r.data ℓ modeL hostT hhost).pieceAt (A.2.κ0 t))
        ((r.data ℓ modeL hostT hhost).pieceAt (A.2.κ1 t)) =
      (C.lamD g t : EReal) :=
  (r.data ℓ modeL hostT hhost).ddist_live c hc0 hcr hgc A.2 (r.subset_data ℓ modeL hostT hhost hA)
    (r.unreach_data ℓ modeL hostT hhost hA h1 h3) h1 h2 h3 h4

/-- **`λ_t` in the repaired graph of a level.** Under the same conditions, for copies `a` and `b`
on E_R edges of the pieces at `κ0(t)` and `κ1(t)`, the distance in the repaired graph of the level
is `λ_t` if `λ_t < M`, and at least `M` otherwise. -/
theorem Run.gdist_level {A : Σ Γ' : Finset (E × Bool), C.Live g Γ'} (hA : A ∈ r.nodes ℓ) {t : ℕ}
    (h1 : A.2.xa ≤ t) (h2 : A.2.ya ≤ t) (h3 : t ≤ A.2.xb) (h4 : t ≤ A.2.yb) {M : ℝ} (hM : 0 ≤ M)
    (a b : (r.data ℓ modeL hostT hhost).EndCopy)
    (ha : (r.data ℓ modeL hostT hhost).pieceOf a = (r.data ℓ modeL hostT hhost).pieceAt (A.2.κ0 t))
    (hb : (r.data ℓ modeL hostT hhost).pieceOf b = (r.data ℓ modeL hostT hhost).pieceAt (A.2.κ1 t)) :
    ((C.lamD g t : EReal) < M →
      (r.data ℓ modeL hostT hhost).gdist (fun x => c x.1.1) M a.1 b.1 = C.lamD g t) ∧
    ((M : EReal) ≤ C.lamD g t →
      (M : EReal) ≤ (r.data ℓ modeL hostT hhost).gdist (fun x => c x.1.1) M a.1 b.1) :=
  (r.data ℓ modeL hostT hhost).gdist_live c hc0 hcr hgc A.2 (r.subset_data ℓ modeL hostT hhost hA)
    (r.unreach_data ℓ modeL hostT hhost hA h1 h3) h1 h2 h3 h4 hM a b ha hb

end CutPath

end Tokens

end RotSystem

end

end SsspFlow
