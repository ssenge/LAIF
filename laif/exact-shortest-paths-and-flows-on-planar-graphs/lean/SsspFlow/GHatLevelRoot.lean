import SsspFlow.GHatLevelMinIdx
import SsspFlow.GHatLevelRoots
import SsspFlow.OracleChainSum

/-!
# The root of the chain of a target is its source

For an output of the oracle on the network of a level from the sources of a list of annuli, the
distances along valid parent steps stay finite, and a node without a parent and with a finite
distance has its offset as its distance, so it is a source. The chain of the target of an annulus
stays in the component of `Ĝ_ℓ[E_R ∪ E_C]` of the target, which holds no other source, so its root is
the source of the annulus.

* `Net.ExactSpec.parSteps_ne_top`: valid parent steps keep the distance finite.
* `Net.parSteps_root_unique`: the number of valid parent steps to a root is unique.
* `RData.root_eq_src`: the root of the chain of a target is the source of its annulus.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace Congest

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Valid parent steps keep the distance finite.** -/
theorem Net.ExactSpec.parSteps_ne_top {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) {a : V} :
    ∀ {i : ℕ}, Net.ParSteps r a i → (r a).1 ≠ ⊤ → (r ((Net.parOf r)^[i] a)).1 ≠ ⊤
  | 0, _, ha => ha
  | i + 1, hs, ha => by
    have ih := Net.ExactSpec.parSteps_ne_top h (i := i) (fun k hk => hs k (by omega)) ha
    have hp := hs i (by omega)
    obtain ⟨rank, hrank⟩ := h.parent
    rcases hrank ((Net.parOf r)^[i] a) with ⟨p, e, -, -, hsum, -⟩ | ⟨e, -⟩
    · rw [e] at hp
      obtain rfl := Option.some_injective _ hp
      intro htop
      rw [htop, top_add] at hsum
      exact ih hsum.symm
    · rw [e] at hp
      exact absurd hp (by simp)

/-- **The number of valid parent steps to a root is unique.** -/
theorem Net.parSteps_root_unique {r : V → ℕ∞ × Option V} {a : V} {k k' : ℕ}
    (hs : Net.ParSteps r a k) (hn : (r ((Net.parOf r)^[k] a)).2 = none)
    (hs' : Net.ParSteps r a k') (hn' : (r ((Net.parOf r)^[k'] a)).2 = none) : k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := hs' k h
    rw [hn] at this
    exact absurd this (by simp)
  · have := hs k' h
    rw [hn'] at this
    exact absurd this (by simp)

end Congest

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞} {hR : N.toRot.dual.Planar}
  {hC : N.toRot.dual.Connected} {hg : ∀ x, g (N.toRot.dual.rev x) = g x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : C.Live g Γ₀} {j k : ℕ}
  (r : CutPath.Run hR hC hg Γ₀ L₀ j k) (ℓ : ℕ)

/-- **The root of the chain of a target is its source.** For an output of the oracle on the network
of a level from the sources of a list `Q` of annuli of the level with one index each and `λ_t < M`,
the root reached by valid parent steps from the target of an annulus of `Q` is its source. -/
theorem root_eq_src (lam : S.Tok → ℕ) (M : ℕ) (c : N.G.Dart → ℕ)
    (hcr : ∀ d, c (N.toRot.rev d) = c d) (hlam : ∀ x, lam x = c x.1.1) (hgc : ∀ d, g d = c d)
    (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ) (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
    (hQ : ∀ q ∈ Q, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧ q.2 ≤ q.1.2.xb ∧
      q.2 ≤ q.1.2.yb ∧ C.lamD g q.2 < M)
    (hQu : ∀ q ∈ Q, ∀ q' ∈ Q, q.1 = q'.1 → q.2 = q'.2)
    (R : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) (S.srcOff hN Q) R)
    {At : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ} (hAt : At ∈ Q) {kk : ℕ}
    (hs : Net.ParSteps R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) kk)
    (hn : (R ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))).2 = none) :
    (Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) =
      (S.levelPad hN).ι (.inl (S.endV (At.1.2.κ0 At.2))) := by
  classical
  set v := (S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))
  have hle := S.tgt_dist_le hN r ℓ lam M c hcr hlam hgc hΓ Q hQ R hr At hAt
  have hlt : ((R v).1 : ℝ≥0∞) < M := lt_of_le_of_lt hle (hQ At hAt).2.2.2.2.2
  have hv : (R v).1 ≠ ⊤ := fun e => by simp [e] at hlt
  have hy := hr.parSteps_ne_top hs hv
  obtain ⟨rank, hrank⟩ := hr.parent
  have hφ : S.srcOff hN Q ((Net.parOf R)^[kk] v) ≠ ⊤ := by
    rcases hrank ((Net.parOf R)^[kk] v) with ⟨p, e, -⟩ | ⟨-, e | e⟩
    · rw [hn] at e
      exact absurd e (by simp)
    · exact absurd e hy
    · rw [← e]
      exact hy
  have hex : ∃ q' ∈ Q, (Net.parOf R)^[kk] v = (S.levelPad hN).ι (.inl (S.endV (q'.1.2.κ0 q'.2))) := by
    by_contra hne
    exact hφ (by unfold srcOff; exact ite_eq_right_of_eq_false _ _ (eq_false hne))
  obtain ⟨q', hq', hroot⟩ := hex
  have he := (S.chain_erc hN lam M (S.srcOff hN Q) R hr hlt ⟨kk, rfl⟩).1
  rw [hroot, S.copyAt_ι] at he
  obtain ⟨-, h1, -, h3, -⟩ := hQ q' hq'
  have e := S.tgt_same r ℓ M hΓ Q hQ hQu q' hq' At hAt (q'.1.2.κ0 q'.2) (q'.1.2.gcomp_κ0 h1 h3) he
  rw [hroot, e]

end RData

end RotSystem

end SsspFlow
