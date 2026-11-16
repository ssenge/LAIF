import SsspFlow.GHatLevelRoots

/-!
# The distance at a target is the length of the cut

For an output of the oracle on the network of a level from the sources of a list `Q` of annuli of
the level with one index `t` each, every source lies at the piece at `κ0(t)` of the annulus of a
target or at distance at least `M` from it. Every walk of `Ĝ_ℓ` from that piece to the target is at
least `λ_t` long, so the distance at the target is at least `λ_t`, and with `RData.tgt_dist_le` it is
`λ_t`.

* `RData.lamD_le_arcDist`: walks between the pieces at `κ0(t)` and `κ1(t)` of an annulus of a level
  are at least `λ_t` long.
* `RData.tgt_dist_eq`: the distance at the target of each annulus of `Q` is `λ_t`.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

variable {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞} {hR : N.toRot.dual.Planar}
  {hC : N.toRot.dual.Connected} {hg : ∀ x, g (N.toRot.dual.rev x) = g x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : C.Live g Γ₀} {j k : ℕ}
  (r : CutPath.Run hR hC hg Γ₀ L₀ j k) (ℓ : ℕ)

/-- **Walks between the pieces of an annulus are long.** For an annulus of a level and an index `t`
in its ranges with `λ_t < M`, every walk of `Ĝ_ℓ` from a copy on an E_R edge of the piece at `κ0(t)`
to the copy at the first end of the token at `κ1(t)` is at least `λ_t` long. -/
theorem lamD_le_arcDist (lam : S.Tok → ℕ) (M : ℕ) (c : N.G.Dart → ℕ)
    (hcr : ∀ d, c (N.toRot.rev d) = c d) (hlam : ∀ x, lam x = c x.1.1) (hgc : ∀ d, g d = c d)
    (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ) {A : Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ'}
    (hA : A ∈ r.nodes ℓ) {t : ℕ} (h1 : A.2.xa ≤ t) (h2 : A.2.ya ≤ t) (h3 : t ≤ A.2.xb)
    (h4 : t ≤ A.2.yb) (hM : C.lamD g t < M) (a : S.EndCopy) (ha : S.pieceOf a = S.pieceAt (A.2.κ0 t)) :
    C.lamD g t ≤ S.arcDist lam M a.1 (S.vcopy (S.endV (A.2.κ1 t))) := by
  have hsub : A.1 ⊆ S.Γ := hΓ ▸ r.subset_level ℓ hA
  have hunr : ∀ w ∈ S.Γ, w ∉ A.1 → ∀ p, ¬ (N.toRot.dual.double.split A.1).IsWalk
      ((N.toRot.dual.double.split A.1).tail (A.2.κ0 t)) p ((N.toRot.dual.double.split A.1).tail w) :=
    fun w hw hwA p => r.unreach_level ℓ hA (hΓ ▸ hw) hwA h1 h3 p
  have hlamR : (fun x => (lam x : ℝ)) = fun x => ((c x.1.1 : ℕ) : ℝ) := funext fun x => by rw [hlam]
  have hne : C.lamD g t ≠ ⊤ := ne_top_of_lt hM
  have hMe : (C.lamD g t : EReal) < ((M : ℝ) : EReal) := by
    rw [← EReal.coe_ennreal_toReal hne, EReal.coe_lt_coe_iff]
    have := (ENNReal.toReal_lt_toReal hne (ENNReal.natCast_ne_top M)).2 hM
    simpa using this
  have hgd := (S.gdist_live (fun d => (c d : ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun d => by simp only [hcr]) (fun d => by rw [hgc, ENNReal.ofReal_natCast]) A.2 hsub
    hunr h1 h2 h3 h4 (M := (M : ℝ)) (Nat.cast_nonneg _)
    a ⟨_, S.endV_end (A.2.κ1 t)⟩ ha (S.pieceOf_endV _)).1 hMe
  rw [← hlamR] at hgd
  refine le_iInf fun q => ?_
  have hq : S.gdist (fun x => (lam x : ℝ)) M a.1 (S.vcopy (S.endV (A.2.κ1 t))) ≤
      (((S.awt lam M q : ℕ) : ℝ) : EReal) := by
    rw [S.awt_eq_wt]
    exact iInf_le (fun p : FaceDisjoint.Walk S.Arc _ _ =>
      ((p.wt (S.w (fun x => (lam x : ℝ)) M) : ℝ) : EReal)) q
  rw [hgd] at hq
  have e : (((S.awt lam M q : ℕ) : ℝ) : EReal) = (((S.awt lam M q : ℕ) : ℝ≥0∞) : EReal) := by
    simp
  rw [e] at hq
  exact EReal.coe_ennreal_le_coe_ennreal_iff.1 hq

/-- **The distance at a target.** For an output of the oracle on the network of a level from the
sources of a list `Q` of annuli of a level with one index each and `λ_t < M`, the distance at the
target of each annulus of `Q` is `λ_t`. -/
theorem tgt_dist_eq (lam : S.Tok → ℕ) (M : ℕ) (c : N.G.Dart → ℕ)
    (hcr : ∀ d, c (N.toRot.rev d) = c d) (hlam : ∀ x, lam x = c x.1.1) (hgc : ∀ d, g d = c d)
    (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ) (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
    (hQ : ∀ q ∈ Q, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧ q.2 ≤ q.1.2.xb ∧
      q.2 ≤ q.1.2.yb ∧ C.lamD g q.2 < M)
    (hQu : ∀ q ∈ Q, ∀ q' ∈ Q, q.1 = q'.1 → q.2 = q'.2)
    (R : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) (S.srcOff hN Q) R) :
    ∀ q ∈ Q, ((R ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2))))).1 : ℝ≥0∞) = C.lamD g q.2 := by
  intro q hq
  refine le_antisymm (S.tgt_dist_le hN r ℓ lam M c hcr hlam hgc hΓ Q hQ R hr q hq) ?_
  obtain ⟨-, -, h1, h2, h3, h4, hsrc, -⟩ := S.level_roots_cond hN r ℓ lam M c hcr hlam hgc hΓ Q hQ hQu R hr hq
  obtain ⟨hA, -, -, -, -, hM⟩ := hQ q hq
  have hψ : ∀ z, (∀ u, z ≠ (S.levelPad hN).ι (.inl u)) → S.srcOff hN Q z = ⊤ := fun z hz => by
    unfold srcOff
    refine ite_eq_right_of_eq_false _ _ (eq_false ?_)
    rintro ⟨q', -, rfl⟩
    exact hz _ rfl
  rw [hr.dist_eq, S.dsrcTop_copies hN lam M _ hψ]
  refine le_iInf fun u => ?_
  by_cases ht : S.srcOff hN Q ((S.levelPad hN).ι (.inl u)) = ⊤
  · rw [ht]; simp
  obtain ⟨h0, u', hu', hu, hcase⟩ := hsrc _ ht
  obtain rfl := Sum.inl_injective ((S.levelPad hN).ι_injective hu')
  rw [h0, ENat.toENNReal_zero, zero_add]
  rcases hcase with hp | hp
  · exact S.lamD_le_arcDist r ℓ lam M c hcr hlam hgc hΓ hA h1 h2 h3 h4 hM ⟨_, hu⟩ hp
  · exact hM.le.trans hp

end RData

end RotSystem

end SsspFlow
