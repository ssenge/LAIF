import SsspFlow.GHatChainOut
import SsspFlow.OracleChainStep

/-!
# The darts of the step, decided at the nodes

On the chain of a target, the darts of the step of `RData.chain_step_flags` are the darts of the
tokens of the arcs from the nodes to their parents for exactly those nodes that have count `0`, are
not flagged for `0`, and have distance `0` in the run down the chains. Each node reads these three
facts from its own outputs.

* `RData.chain_step_local`: the darts of the step are the darts of the parent arcs of the nodes of the
  chain that meet the three local conditions.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ)

open Classical in
/-- **The darts of the step, decided at the nodes.** Under the conditions of `RData.chain_step_out`,
there is a step whose darts are exactly the darts of the tokens of the arcs from the nodes of the
chain of `v` to their parents, for the nodes with count `0`, not flagged for `0`, and with distance
`0` in the run down the chains. In order, they are the darts of the parent steps from `ia - 1` down
to `iy`. -/
theorem chain_step_local {C : N.toRot.dual.CutPath} {Γ : Finset (N.G.Dart × Bool)}
    (hR : N.toRot.dual.Planar) (hC : N.toRot.dual.Connected) (c : N.G.Dart → ℕ) (hc1 : ∀ d, 1 ≤ c d)
    (hcr : ∀ d, c (N.toRot.rev d) = c d) (hlam : ∀ x, lam x = c x.1.1)
    (L : C.Live (Nat.cast ∘ c) Γ) (hS : Γ ⊆ S.Γ) {t : ℕ}
    (hz : ∀ w ∈ S.Γ, w ∉ Γ → ∀ p, ¬ (N.toRot.dual.double.split Γ).IsWalk
      ((N.toRot.dual.double.split Γ).tail (L.κ0 t)) p ((N.toRot.dual.double.split Γ).tail w))
    (h1 : L.xa ≤ t) (h2 : L.ya ≤ t) (h3 : t ≤ L.xb) (h4 : t ≤ L.yb)
    (isT : Fin (n * (n * 21)) → Bool) (ψ : Fin (n * (n * 21)) → ℕ∞)
    (r : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (r₂ r₃ : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (fl : Fin (n * (n * 21)) → Bool × Bool × Bool)
    (hfl : ∀ a, fl a = (isT a, decide (S.nodeFlag hN C 0 a), decide (S.nodeFlag hN C 1 a)))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) ψ r)
    (hr₂ : (S.levelNet hN).ExactSpec (Net.markLenW r fun a => ((fl a).2.1.toNat : ℕ∞))
      (Net.markOffB fun a => (fl a).1) r₂)
    (hr₃ : (S.levelNet hN).ExactSpec (Net.downLenW r fun a => ((fl a).2.2.toNat : ℕ∞))
      (Net.markOffB fun a => (fl a).2.1 && decide ((r₂ a).1 = 0)) r₃)
    {u v : S.hRot.Vertex} {k : ℕ}
    (hs : Net.ParSteps r ((S.levelPad hN).ι (.inl v)) k)
    (hroot : (Net.parOf r)^[k] ((S.levelPad hN).ι (.inl v)) = (S.levelPad hN).ι (.inl u))
    (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)) (hv : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v))
    (hpu : S.pieceOf ⟨S.vcopy u, hu⟩ = S.pieceAt (L.κ0 t))
    (hpv : S.pieceOf ⟨S.vcopy v, hv⟩ = S.pieceAt (L.κ1 t))
    (hlt : ((∑ l ∈ Finset.range k, S.levelLen hN lam M ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
      ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) : ℕ∞) : ℝ≥0∞) < M)
    (hle : ((∑ l ∈ Finset.range k, S.levelLen hN lam M ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
      ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) : ℕ∞) : ℝ≥0∞) ≤ C.lamD (Nat.cast ∘ c) t)
    (hT : ∀ t t' i i', isT t = true → isT t' = true → Net.ParSteps r t i → Net.ParSteps r t' i' →
      (Net.parOf r)^[i] t = (Net.parOf r)^[i'] t' → t = t')
    (hvT : isT ((S.levelPad hN).ι (.inl v)) = true) :
    ∃ ia iy : ℕ, iy ≤ ia ∧ ia ≤ k ∧ ∃ St : L.Step, (∀ z, z ∈ (List.range St.n).map St.q ↔ ∃ l,
      Net.ParSteps r ((S.levelPad hN).ι (.inl v)) (l + 1) ∧
      (r₂ ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v)))).1 = 0 ∧
      (fl ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v)))).2.1 = false ∧
      (r₃ ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v)))).1 = 0 ∧ ∃ x,
        S.edgeTok hN ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
          ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) = some x ∧ z = N.toRot.tokDart x.1) ∧
      (List.range St.n).map St.q = S.chainDarts hN r ((S.levelPad hN).ι (.inl v)) iy (ia - iy) := by
  have e₂ : (Net.markLenW r fun a => ((fl a).2.1.toNat : ℕ∞)) =
      Net.markLenW r fun a => if S.nodeFlag hN C 0 a then 1 else 0 := by
    congr 1
    funext a
    by_cases h : S.nodeFlag hN C 0 a <;> simp [hfl, h]
  have o₂ : (Net.markOffB fun a => (fl a).1) = Net.markOffB isT := by
    congr 1
    funext a
    simp [hfl]
  rw [e₂, o₂] at hr₂
  have eX : (fun a => (fl a).2.1 && decide ((r₂ a).1 = 0)) = fun a => decide (S.nodeFlag hN C 0 a ∧
      (S.levelNet hN).dsrcTop (Net.markLenW r fun a => if S.nodeFlag hN C 0 a then 1 else 0)
        (Net.markOffB isT) a = 0) := by
    funext a
    rw [hfl]
    show (decide (S.nodeFlag hN C 0 a) && decide ((r₂ a).1 = 0)) = _
    rw [← Bool.decide_and]
    exact decide_eq_decide.2 (and_congr_right fun _ => by rw [← hr₂.dist_eq a, ENat.toENNReal_eq_zero])
  have e₃ : (Net.downLenW r fun a => ((fl a).2.2.toNat : ℕ∞)) =
      Net.downLenW r fun a => if S.nodeFlag hN C 1 a then 1 else 0 := by
    congr 1
    funext a
    by_cases h : S.nodeFlag hN C 1 a <;> simp [hfl, h]
  rw [e₃, eX] at hr₃
  obtain ⟨ia, iy, hya, hak, hA0, hmin, hA1, hmax, St, hSt⟩ := S.chain_step_flags hN lam M hR hC c hc1
    hcr hlam L hS hz h1 h2 h3 h4 ψ r hr hs hroot hu hv hpu hpv hlt hle
  have hA0' : S.nodeFlag hN C 0 ((Net.parOf r)^[ia] ((S.levelPad hN).ι (.inl v))) := hA0
  have hmin' : ∀ m < ia, ¬ S.nodeFlag hN C 0 ((Net.parOf r)^[m] ((S.levelPad hN).ι (.inl v))) := hmin
  have hA1' : S.nodeFlag hN C 1 ((Net.parOf r)^[iy] ((S.levelPad hN).ι (.inl v))) := hA1
  have hmax' : ∀ m, iy < m → m ≤ ia → ¬ S.nodeFlag hN C 1 ((Net.parOf r)^[m] ((S.levelPad hN).ι (.inl v))) :=
    hmax
  have hia : Net.ParSteps r ((S.levelPad hN).ι (.inl v)) ia := fun l hl => hs l (by omega)
  -- the three outputs at a node are the three conditions of `step_iff`
  have hcrit : ∀ w, ((r₂ w).1 = 0 ∧ (fl w).2.1 = false ∧ (r₃ w).1 = 0) ↔
      ((S.levelNet hN).dsrcTop (Net.markLenW r fun a => if S.nodeFlag hN C 0 a then 1 else 0)
        (Net.markOffB isT) w = 0 ∧ ¬ S.nodeFlag hN C 0 w ∧
        (S.levelNet hN).dsrcTop (Net.downLenW r fun a => if S.nodeFlag hN C 1 a then 1 else 0)
          (Net.markOffB fun a => decide (S.nodeFlag hN C 0 a ∧ (S.levelNet hN).dsrcTop
            (Net.markLenW r fun a => if S.nodeFlag hN C 0 a then 1 else 0) (Net.markOffB isT) a = 0)) w = 0) := by
    intro w
    rw [← hr₂.dist_eq, ← hr₃.dist_eq, ENat.toENNReal_eq_zero, ENat.toENNReal_eq_zero, hfl]
    simp
  -- on the chain of `v`, the conditions hold exactly from `iy` to below `ia`
  have key : ∀ l, Net.ParSteps r ((S.levelPad hN).ι (.inl v)) l →
      (((r₂ ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v)))).1 = 0 ∧
        (fl ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v)))).2.1 = false ∧
        (r₃ ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v)))).1 = 0) ↔ iy ≤ l ∧ l < ia) := by
    intro l hl
    rw [hcrit, hr.step_iff (S.nodeFlag hN C 0) (S.nodeFlag hN C 1) isT hT]
    constructor
    · rintro ⟨v', l', ia', hv', hia', hl', h0, h0', h1', he⟩
      obtain rfl : (S.levelPad hN).ι (.inl v) = v' :=
        hT _ _ l l' hvT hv' hl (fun m hm => hia' m (by omega)) he
      obtain rfl : l = l' := hr.parSteps_inj hl (fun m hm => hia' m (by omega)) he
      obtain rfl : ia = ia' := by
        rcases lt_trichotomy ia ia' with h | h | h
        · exact absurd hA0' (h0' ia h)
        · exact h
        · exact absurd h0 (hmin' ia' h)
      refine ⟨?_, hl'⟩
      by_contra hc
      exact h1' iy (by omega) hya hA1'
    · rintro ⟨h1l, h2l⟩
      exact ⟨_, l, ia, hvT, hia, h2l, hA0', hmin', fun m hm1 hm2 => hmax' m (by omega) hm2, rfl⟩
  refine ⟨ia, iy, hya, hak, St, fun z => (hSt.1 z).trans ⟨?_, ?_⟩, hSt.2⟩
  · rintro ⟨l, h1l, h2l, x, he, rfl⟩
    have hl1 : Net.ParSteps r ((S.levelPad hN).ι (.inl v)) (l + 1) := fun m hm => hs m (by omega)
    obtain ⟨c1, c2, c3⟩ := (key l fun m hm => hs m (by omega)).2 ⟨h1l, h2l⟩
    exact ⟨l, hl1, c1, c2, c3, x, he, rfl⟩
  · rintro ⟨l, hl1, c1, c2, c3, x, he, rfl⟩
    obtain ⟨h1l, h2l⟩ := (key l fun m hm => hl1 m (by omega)).1 ⟨c1, c2, c3⟩
    exact ⟨l, h1l, h2l, x, he, rfl⟩

end RData

end RotSystem

end SsspFlow
