import SsspFlow.AnnuliSep
import SsspFlow.GHatLevelI12Spec

/-!
# Sources and targets of the annuli of a level

For a level of a run, every annulus that computes a shortest walk at an index `t` gets one source
and one target in the network of the level: the copies at the first ends of the tokens at `κ0(t)`
and at `κ1(t)`. Copies of different annuli lie in different components of `Ĝ_ℓ[E_R ∪ E_C]`, and
below `M` the distance from the source of an annulus to its target is at most `λ_t`. So the
conditions of `RData.level_i12_of_marked` hold for every annulus at once.

* `RData.exists_awt_of_gdist`: the distance in `Ĝ_ℓ` for natural lengths is the length of a walk.
* `RData.le_arcDist_of_not_erc`: copies that are not joined by E_R and E_C edges are at distance at
  least `M`.
* `RData.annulus_eq`: copies of two annuli of a level that are joined by E_R and E_C edges belong
  to the same annulus.
* `RData.tgt_dist_le`: below `M`, the distance at the target of each annulus is at most `λ_t`.
* `RData.tgt_same`: an annulus whose component reaches the target of another by E_R and E_C edges
  is that annulus, with the same index.
* `RData.level_roots_cond`: for the sources and targets of a list of annuli of a level, each with
  one index and `λ_t < M`, every annulus of the list meets the conditions of
  `RData.level_i12_of_marked`.
* `RData.level_i12_roots`: so the least values over the marked copies at each target are the least
  and `m` minus the greatest index on the cut path of one shortest walk of its annulus, whose
  indices are read at the copies of the nodes of the chain of the target.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

section Gen

variable {E : Type} [Fintype E] [DecidableEq E] {G : RotSystem E} (S : G.RData) (lam : S.Tok → ℕ)
  (M : ℕ)

/-- **Distances are attained.** For natural lengths, a distance of `Ĝ_ℓ` with a real value is the
length of a walk. -/
theorem exists_awt_of_gdist {a b : Copy G.Vertex E} {y : ℝ}
    (h : S.gdist (fun x => (lam x : ℝ)) M a b = (y : EReal)) :
    ∃ q : FaceDisjoint.Walk S.Arc a b, ((S.awt lam M q : ℕ) : ℝ) = y := by
  by_contra hne
  push Not at hne
  have hlt : ∀ q : FaceDisjoint.Walk S.Arc a b, y < ((S.awt lam M q : ℕ) : ℝ) := fun q => by
    have hq : S.gdist (fun x => (lam x : ℝ)) M a b ≤ (((S.awt lam M q : ℕ) : ℝ) : EReal) := by
      rw [S.awt_eq_wt]
      exact iInf_le (fun p : FaceDisjoint.Walk S.Arc a b =>
        ((p.wt (S.w (fun x => (lam x : ℝ)) M) : ℝ) : EReal)) q
    rw [h] at hq
    exact lt_of_le_of_ne (EReal.coe_le_coe_iff.1 hq) (hne q).symm
  have hge : ((((⌊y⌋ + 1 : ℤ) : ℝ)) : EReal) ≤ S.gdist (fun x => (lam x : ℝ)) M a b := by
    unfold gdist
    refine le_iInf fun q => ?_
    rw [← S.awt_eq_wt]
    refine EReal.coe_le_coe_iff.2 ?_
    have h1 : ⌊y⌋ < ((S.awt lam M q : ℕ) : ℤ) := Int.floor_lt.2 (by exact_mod_cast hlt q)
    have h2 : ⌊y⌋ + 1 ≤ ((S.awt lam M q : ℕ) : ℤ) := h1
    exact_mod_cast h2
  rw [h] at hge
  have h3 := EReal.coe_le_coe_iff.1 hge
  have h4 := Int.lt_floor_add_one y
  push_cast at h3
  linarith

/-- A distance of `Ĝ_ℓ` with a finite value `x` bounds the distance for natural lengths. -/
theorem arcDist_le_of_gdist {a b : Copy G.Vertex E} {x : ℝ≥0∞} (hx : x ≠ ⊤)
    (h : S.gdist (fun x => (lam x : ℝ)) M a b = (x : EReal)) : S.arcDist lam M a b ≤ x := by
  rw [← EReal.coe_ennreal_toReal hx] at h
  obtain ⟨q, hq⟩ := S.exists_awt_of_gdist lam M h
  refine (iInf_le _ q).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_toReal hx, ← hq, ENNReal.ofReal_natCast]

/-- Copies that are not joined by E_R and E_C edges are at distance at least `M`. -/
theorem le_arcDist_of_not_erc {a b : Copy G.Vertex E} (h : ¬ Relation.ReflTransGen S.ERC a b) :
    (M : ℝ≥0∞) ≤ S.arcDist lam M a b := by
  refine le_iInf fun q => ?_
  by_contra hq
  have hlt : S.awt lam M q < M := by exact_mod_cast not_le.1 hq
  have hmem : a ∈ q.support := by cases q <;> simp
  exact h (S.erc_of_walk lam M q hlt a hmem).1

end Gen

section Level

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

/-- The vertex of the repaired graph at the first end of the token at a dart of the doubled dual. -/
noncomputable def endV (z : N.G.Dart × Bool) : S.hRot.Vertex :=
  S.hRot.tail (HE.tok ⟨S.tokOf z, S.isTok_tokOf z⟩, false)

theorem vcopy_endV (z : N.G.Dart × Bool) : S.vcopy (S.endV z) = S.alpha (S.tokOf z) := rfl

theorem endV_end (z : N.G.Dart × Bool) : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy (S.endV z)) :=
  ⟨⟨S.tokOf z, S.isTok_tokOf z⟩, .inl rfl⟩

theorem pieceOf_endV (z : N.G.Dart × Bool) :
    S.pieceOf ⟨S.vcopy (S.endV z), S.endV_end z⟩ = S.pieceAt z :=
  S.pieceOf_eq _ (x := ⟨S.tokOf z, S.isTok_tokOf z⟩) (.inl rfl)

variable {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞} {hR : N.toRot.dual.Planar}
  {hC : N.toRot.dual.Connected} {hg : ∀ x, g (N.toRot.dual.rev x) = g x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : C.Live g Γ₀} {j k : ℕ}
  (r : CutPath.Run hR hC hg Γ₀ L₀ j k) (ℓ : ℕ)

/-- **Copies of two annuli.** Copies on E_R edges of the components of two annuli of a level that
are joined by E_R and E_C edges belong to the same annulus. -/
theorem annulus_eq (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ)
    {A B : Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ'} (hA : A ∈ r.nodes ℓ) (hB : B ∈ r.nodes ℓ)
    (a b : S.EndCopy) {z z' : N.G.Dart × Bool} (ha : S.pieceOf a = S.pieceAt z)
    (hb : S.pieceOf b = S.pieceAt z')
    (hz : (N.toRot.dual.double.split A.1).toHypermap.gcomp (A.2.κ0 A.2.xa) z)
    (hz' : (N.toRot.dual.double.split B.1).toHypermap.gcomp (B.2.κ0 B.2.xa) z')
    (h : Relation.ReflTransGen S.ERC a.1 b.1) : A = B := by
  obtain ⟨p, hp⟩ := (S.tg_comp_iff _ _).1 ((S.erc_comp_iff a b).1 h)
  rw [ha, hb, S.vertexEquiv_pieceAt, S.vertexEquiv_pieceAt] at hp
  have hzz : (N.toRot.dual.double.split S.Γ).toHypermap.gcomp z z' := IsWalk.gcomp_tail hp
  rw [hΓ] at hzz
  exact r.sep ℓ A hA B hB z' (connect_trans hz (RootedTree.gcomp_split_mono (r.subset_level ℓ hA) hzz)) hz'

open Classical in
/-- The offsets of the sources of a list of annuli with indices: `0` at the copy at the first end of
the token at `κ0(t)` of each, `⊤` elsewhere. -/
noncomputable def srcOff (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
    (z : Fin (n * (n * 21))) : ℕ∞ :=
  if ∃ q ∈ Q, z = (S.levelPad hN).ι (.inl (S.endV (q.1.2.κ0 q.2))) then 0 else ⊤

open Classical in
/-- The targets of a list of annuli with indices: the copies at the first ends of the tokens at
`κ1(t)`. -/
noncomputable def tgtFlag (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
    (z : Fin (n * (n * 21))) : Bool :=
  decide (∃ q ∈ Q, z = (S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2))))

/-- **The distance at a target.** For an output of the oracle on the network of a level from the
sources of a list `Q` of annuli of a level with one index each and `λ_t < M`, the distance at the
target of each annulus of `Q` is at most `λ_t`. -/
theorem tgt_dist_le (lam : S.Tok → ℕ) (M : ℕ) (c : N.G.Dart → ℕ)
    (hcr : ∀ d, c (N.toRot.rev d) = c d) (hlam : ∀ x, lam x = c x.1.1) (hgc : ∀ d, g d = c d)
    (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ) (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
    (hQ : ∀ q ∈ Q, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧ q.2 ≤ q.1.2.xb ∧
      q.2 ≤ q.1.2.yb ∧ C.lamD g q.2 < M)
    (R : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) (S.srcOff hN Q) R) :
    ∀ q ∈ Q, ((R ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2))))).1 : ℝ≥0∞) ≤ C.lamD g q.2 := by
  classical
  have hsub : ∀ {B : Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ'}, B ∈ r.nodes ℓ → B.1 ⊆ S.Γ :=
    fun hB => hΓ ▸ r.subset_level ℓ hB
  have hunr : ∀ {B : Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ'}, B ∈ r.nodes ℓ → ∀ {t' : ℕ},
      B.2.xa ≤ t' → t' ≤ B.2.xb → ∀ w ∈ S.Γ, w ∉ B.1 → ∀ p, ¬ (N.toRot.dual.double.split B.1).IsWalk
        ((N.toRot.dual.double.split B.1).tail (B.2.κ0 t')) p ((N.toRot.dual.double.split B.1).tail w) :=
    fun hB _ h1 h3 w hw hwB p => r.unreach_level ℓ hB (hΓ ▸ hw) hwB h1 h3 p
  have hlamR : (fun x => (lam x : ℝ)) = fun x => ((c x.1.1 : ℕ) : ℝ) := funext fun x => by rw [hlam]
  intro q hq
  obtain ⟨hB, h1, h2, h3, h4, hM⟩ := hQ q hq
  have hψ : ∀ z, (∀ u, z ≠ (S.levelPad hN).ι (.inl u)) → S.srcOff hN Q z = ⊤ := fun z hz => by
    unfold srcOff
    refine ite_eq_right_of_eq_false _ _ (eq_false ?_)
    rintro ⟨q', -, rfl⟩
    exact hz _ rfl
  rw [hr.dist_eq, S.dsrcTop_copies hN lam M _ hψ]
  refine iInf_le_of_le (S.endV (q.1.2.κ0 q.2)) ?_
  have h0 : S.srcOff hN Q ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ0 q.2)))) = 0 := by
    unfold srcOff
    exact ite_eq_left_of_eq_true _ _ (eq_true ⟨q, hq, rfl⟩)
  rw [h0, ENat.toENNReal_zero, zero_add]
  have hne : C.lamD g q.2 ≠ ⊤ := ne_top_of_lt hM
  have hMe : (C.lamD g q.2 : EReal) < ((M : ℝ) : EReal) := by
    rw [← EReal.coe_ennreal_toReal hne, EReal.coe_lt_coe_iff]
    have := (ENNReal.toReal_lt_toReal hne (ENNReal.natCast_ne_top M)).2 hM
    simpa using this
  have hgd := (S.gdist_live (fun d => (c d : ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun d => by simp only [hcr]) (fun d => by rw [hgc, ENNReal.ofReal_natCast]) q.1.2 (hsub hB)
    (hunr hB h1 h3) h1 h2 h3 h4 (M := (M : ℝ)) (Nat.cast_nonneg _)
    ⟨_, S.endV_end (q.1.2.κ0 q.2)⟩ ⟨_, S.endV_end (q.1.2.κ1 q.2)⟩ (S.pieceOf_endV _)
    (S.pieceOf_endV _)).1 hMe
  exact S.arcDist_le_of_gdist lam M hne (by rw [hlamR]; exact hgd)

/-- **One target per component.** Two annuli of a list `Q` of annuli of a level with one index each,
such that a corner of the component of the first is joined by E_R and E_C edges to the target of the
second, are equal, with the same index. -/
theorem tgt_same (M : ℕ) (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ)
    (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
    (hQ : ∀ q ∈ Q, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧ q.2 ≤ q.1.2.xb ∧
      q.2 ≤ q.1.2.yb ∧ C.lamD g q.2 < M)
    (hQu : ∀ q ∈ Q, ∀ q' ∈ Q, q.1 = q'.1 → q.2 = q'.2) :
    ∀ q ∈ Q, ∀ q' ∈ Q, ∀ (z : N.G.Dart × Bool),
      (N.toRot.dual.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) z →
      Relation.ReflTransGen S.ERC (S.vcopy (S.endV z)) (S.vcopy (S.endV (q'.1.2.κ1 q'.2))) → q = q' := by
  intro q hq q' hq' z hz he
  obtain ⟨hB, -⟩ := hQ q hq
  obtain ⟨hA, -, h2, -, h4, -⟩ := hQ q' hq'
  have e := S.annulus_eq r ℓ hΓ hB hA ⟨_, S.endV_end z⟩ ⟨_, S.endV_end (q'.1.2.κ1 q'.2)⟩
    (S.pieceOf_endV z) (S.pieceOf_endV _) hz (q'.1.2.gcomp_κ1 h2 h4) he
  exact Prod.ext e (hQu q hq q' hq' e)

/-- **The conditions of a level hold for its annuli.** Let the token lengths be the costs `c` of
their darts, with `g = c`, and let `Q` list annuli of a level with one index `t` each in their
ranges and `λ_t < M`. For an output of the oracle on the network of the level from the sources of
`Q`, an annulus of `Q` meets the conditions of `RData.level_i12_of_marked` with the targets of `Q`:
its corners lie in those of the level, the other corners are out of its reach, every source lies
at its piece at `κ0(t)` or at distance at least `M`, the distance of its target is at most `λ_t`, and
each target of distance below `M` is the only target of its component. -/
theorem level_roots_cond (lam : S.Tok → ℕ) (M : ℕ) (c : N.G.Dart → ℕ)
    (hcr : ∀ d, c (N.toRot.rev d) = c d) (hlam : ∀ x, lam x = c x.1.1) (hgc : ∀ d, g d = c d)
    (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ) (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
    (hQ : ∀ q ∈ Q, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧ q.2 ≤ q.1.2.xb ∧
      q.2 ≤ q.1.2.yb ∧ C.lamD g q.2 < M)
    (hQu : ∀ q ∈ Q, ∀ q' ∈ Q, q.1 = q'.1 → q.2 = q'.2)
    (R : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) (S.srcOff hN Q) R)
    {A : Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ'} {t : ℕ} (hAt : (A, t) ∈ Q) :
    A.1 ⊆ S.Γ ∧ (∀ w ∈ S.Γ, w ∉ A.1 → ∀ p, ¬ (N.toRot.dual.double.split A.1).IsWalk
        ((N.toRot.dual.double.split A.1).tail (A.2.κ0 t)) p ((N.toRot.dual.double.split A.1).tail w)) ∧
      A.2.xa ≤ t ∧ A.2.ya ≤ t ∧ t ≤ A.2.xb ∧ t ≤ A.2.yb ∧
      (∀ z, S.srcOff hN Q z ≠ ⊤ → S.srcOff hN Q z = 0 ∧ ∃ u, z = (S.levelPad hN).ι (.inl u) ∧
        ∃ hu : (∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
          S.pieceOf ⟨S.vcopy u, hu⟩ = S.pieceAt (A.2.κ0 t) ∨
            (M : ℝ≥0∞) ≤ S.arcDist lam M (S.vcopy u) (S.vcopy (S.endV (A.2.κ1 t)))) ∧
      ((R ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t))))).1 : ℝ≥0∞) ≤ C.lamD g t ∧
      (∀ t', S.tgtFlag hN Q t' = true → ((R t').1 : ℝ≥0∞) < M ∧ ∃ v', t' = (S.levelPad hN).ι (.inl v') ∧
        ∃ _ : (∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v')),
          (Relation.ReflTransGen S.ERC (S.vcopy v') (S.vcopy (S.endV (A.2.κ1 t))) → v' = S.endV (A.2.κ1 t))) ∧
      S.tgtFlag hN Q ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t)))) = true := by
  classical
  have hsub : ∀ {B : Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ'}, B ∈ r.nodes ℓ → B.1 ⊆ S.Γ :=
    fun hB => hΓ ▸ r.subset_level ℓ hB
  have hunr : ∀ {B : Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ'}, B ∈ r.nodes ℓ → ∀ {t' : ℕ},
      B.2.xa ≤ t' → t' ≤ B.2.xb → ∀ w ∈ S.Γ, w ∉ B.1 → ∀ p, ¬ (N.toRot.dual.double.split B.1).IsWalk
        ((N.toRot.dual.double.split B.1).tail (B.2.κ0 t')) p ((N.toRot.dual.double.split B.1).tail w) :=
    fun hB _ h1 h3 w hw hwB p => r.unreach_level ℓ hB (hΓ ▸ hw) hwB h1 h3 p
  have upper := S.tgt_dist_le hN r ℓ lam M c hcr hlam hgc hΓ Q hQ R hr
  have same : ∀ q ∈ Q, ∀ (z : N.G.Dart × Bool),
      (N.toRot.dual.double.split q.1.1).toHypermap.gcomp (q.1.2.κ0 q.1.2.xa) z →
      Relation.ReflTransGen S.ERC (S.vcopy (S.endV z)) (S.vcopy (S.endV (A.2.κ1 t))) → q = (A, t) :=
    fun q hq z hz he => S.tgt_same r ℓ M hΓ Q hQ hQu q hq (A, t) hAt z hz he
  obtain ⟨hA, h1, h2, h3, h4, -⟩ := hQ (A, t) hAt
  have hup : ((R ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t))))).1 : ℝ≥0∞) ≤ C.lamD g t := upper (A, t) hAt
  refine ⟨hsub hA, hunr hA h1 h3, h1, h2, h3, h4, ?_, hup, ?_, ?_⟩
  · intro z hz
    unfold srcOff at hz ⊢
    by_cases hc : ∃ q ∈ Q, z = (S.levelPad hN).ι (.inl (S.endV (q.1.2.κ0 q.2)))
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
      obtain ⟨q, hq, rfl⟩ := hc
      refine ⟨rfl, _, rfl, S.endV_end _, ?_⟩
      by_cases hd : (M : ℝ≥0∞) ≤ S.arcDist lam M (S.vcopy (S.endV (q.1.2.κ0 q.2)))
          (S.vcopy (S.endV (A.2.κ1 t)))
      · exact .inr hd
      · have he : Relation.ReflTransGen S.ERC (S.vcopy (S.endV (q.1.2.κ0 q.2)))
            (S.vcopy (S.endV (A.2.κ1 t))) := by
          by_contra hn
          exact hd (S.le_arcDist_of_not_erc lam M hn)
        obtain ⟨-, k1, -, k3, -, -⟩ := hQ q hq
        have hqA := same q hq _ (q.1.2.gcomp_κ0 k1 k3) he
        subst hqA
        exact .inl (S.pieceOf_endV _)
    · exact absurd (ite_eq_right_of_eq_false _ _ (eq_false hc)) hz
  · intro t' ht'
    have ht'' : ∃ q ∈ Q, t' = (S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2))) := by
      simpa [tgtFlag] using ht'
    obtain ⟨q, hq, rfl⟩ := ht''
    obtain ⟨-, -, k2, -, k4, hM⟩ := hQ q hq
    refine ⟨(upper q hq).trans_lt hM, _, rfl, S.endV_end _, fun he => ?_⟩
    have hqA := same q hq _ (q.1.2.gcomp_κ1 k2 k4) he
    subst hqA
    rfl
  · unfold tgtFlag
    exact decide_eq_true ⟨(A, t), hAt, rfl⟩

/-- **The least and the greatest index of the annuli of a level.** Under the conditions of
`RData.level_roots_cond`, for values `x1`, `x2` that agree, capped at `M`, with the least `ix` and
the least `jx` over the copies of the component of the target of an annulus whose identifiers lie on
the chain of a target of `Q`, there is a shortest walk of the annulus of the length of the distance
at its target whose least index and `m` minus its greatest index agree, capped at `M`, with `x1` and
`x2`, and whose indices are read at the copies of the nodes of the chain of the target. -/
theorem level_i12_roots (lam : S.Tok → ℕ) (M : ℕ) (c : N.G.Dart → ℕ)
    (hcr : ∀ d, c (N.toRot.rev d) = c d) (hlam : ∀ x, lam x = c x.1.1) (hgc : ∀ d, g d = c d)
    (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ) (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
    (hQ : ∀ q ∈ Q, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧ q.2 ≤ q.1.2.xb ∧
      q.2 ≤ q.1.2.yb ∧ C.lamD g q.2 < M)
    (hQu : ∀ q ∈ Q, ∀ q' ∈ Q, q.1 = q'.1 → q.2 = q'.2)
    (R : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) (S.srcOff hN Q) R)
    (ixI jxI : Fin (n * (n * 21)) → ℕ∞)
    (hix : ∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
      ixI ((S.levelPad hN).ι (.inl u)) = ⨅ r' ∈ S.cutIdx C ⟨S.vcopy u, hu⟩, (r' : ℕ∞))
    (hjx : ∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
      jxI ((S.levelPad hN).ι (.inl u)) = ⨅ r' ∈ S.cutIdx C ⟨S.vcopy u, hu⟩, ((C.m - r' : ℕ) : ℕ∞))
    {A : Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ'} {t : ℕ} (hAt : (A, t) ∈ Q) (x1 x2 : ℝ≥0∞)
    (hx1 : min x1 M = min (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ERC (S.vcopy u)
        (S.vcopy (S.endV (A.2.κ1 t)))),
      ⨅ (_ : ∃ t' i, S.tgtFlag hN Q t' = true ∧ (Net.parOf R)^[i] t' = (S.levelPad hN).ι (.inl u)),
        (ixI ((S.levelPad hN).ι (.inl u)) : ℝ≥0∞)) M)
    (hx2 : min x2 M = min (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ERC (S.vcopy u)
        (S.vcopy (S.endV (A.2.κ1 t)))),
      ⨅ (_ : ∃ t' i, S.tgtFlag hN Q t' = true ∧ (Net.parOf R)^[i] t' = (S.levelPad hN).ι (.inl u)),
        (jxI ((S.levelPad hN).ι (.inl u)) : ℝ≥0∞)) M) :
    ∃ (ps : List (N.G.Dart × Bool)) (i1 i2 : ℕ), A.2.Shortest t ps ∧
      (ps.map (g ∘ Prod.fst)).sum = ((R ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t))))).1 : ℝ≥0∞) ∧
      IsLeast (C.idx (A.2.κ0 t) ps) i1 ∧ IsGreatest (C.idx (A.2.κ0 t) ps) i2 ∧
      min x1 M = min (i1 : ℝ≥0∞) M ∧ min x2 M = min ((C.m - i2 : ℕ) : ℝ≥0∞) M ∧
      ∀ r', r' ∈ C.idx (A.2.κ0 t) ps ↔ r' ≤ C.m ∧ ∃ σ, ∃ y,
        (∃ i, (Net.parOf R)^[i] ((S.levelPad hN).ι (.inl (S.endV (A.2.κ1 t)))) = y) ∧
        ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)), ∃ z,
          S.dualSplit.tail z = S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) ∧
          C.cut.tail z = C.cut.tail (C.k σ r') := by
  obtain ⟨hA, hu, h1, h2, h3, h4, hroot, hup, hT, hTv⟩ :=
    S.level_roots_cond hN r ℓ lam M c hcr hlam hgc hΓ Q hQ hQu R hr hAt
  exact S.level_i12_of_marked hN lam M c hcr hlam hgc A.2 hA hu h1 h2 h3 h4 (S.srcOff hN Q) R hr
    (v := S.endV (A.2.κ1 t)) (S.endV_end (A.2.κ1 t)) (S.pieceOf_endV (A.2.κ1 t)) hroot hup (S.tgtFlag hN Q)
    hT hTv ixI jxI hix hjx x1 x2 hx1 hx2

end Level

end RData

end RotSystem

end SsspFlow
