import SsspFlow.GHatLevelNode

/-!
# The step bit of a copy

The test that decides the darts of a step on a chain reads, at a node of the chain, only its own
outputs and the arc to its parent. So it is a bit of the copy alone, the step bit. Every copy with the
step bit lies on the chain of a target, and the arc to its parent is the arc of a rim token whose two
ends are hosted at the first end of its dart.

* `Net.ExactSpec.chain_of_markW`: a node of finite distance in a run along the chains lies on the
  chain of a target.
* `RData.stepBit`: the step bit of a copy.
* `RData.edgeTok_host`: the dart of the token of an arc ends at the host of the arc and at the
  neighbour in the name of the arc.
* `RData.crit_iff`: the test at the node `l` of a chain is the step bit with `l` valid steps.
* `RData.stepBit_chain`: a copy with the step bit lies on the chain of a target of `Q`.
* `RData.stepBitD`, `RData.stepBit_iff_D`: the step bit is fixed by the distances of the two runs.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace Congest

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Finite distance along the chains.** In a run with the lengths `f` on the arcs to the parents and
offset `0` at the targets, a node of finite distance lies `i` valid steps above a target. -/
theorem Net.ExactSpec.chain_of_markW {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) (f : V → ℕ∞) (isT : V → Bool) {r₂ : V → ℕ∞ × Option V}
    (h₂ : N.ExactSpec (Net.markLenW r f) (Net.markOffB isT) r₂) {x : V} (hx : (r₂ x).1 ≠ ⊤) :
    ∃ t i, isT t = true ∧ Net.ParSteps r t i ∧ (Net.parOf r)^[i] t = x := by
  by_contra hc
  apply hx
  have e := h₂.dist_eq x
  rw [h.dsrcTop_markW] at e
  have htop : (⨅ t, ⨅ (_ : isT t = true), ⨅ i, ⨅ (_ : Net.ParSteps r t i ∧ (Net.parOf r)^[i] t = x),
      ((∑ k ∈ Finset.range i, f ((Net.parOf r)^[k] t) : ℕ∞) : ℝ≥0∞)) = ⊤ := by
    simp only [iInf_eq_top]
    intro t ht i hi
    exact absurd ⟨t, i, ht, hi.1, hi.2⟩ hc
  rw [htop] at e
  exact_mod_cast e

end Congest

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

/-- The step bit of a copy: it has a parent by a token arc, the counts of the two runs along the
chains are `0` there, and it is not flagged for the first run. -/
def stepBit (R r₂ r₃ : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (fl : Fin (n * (n * 21)) → Bool × Bool × Bool) (y : Fin (n * (n * 21))) : Prop :=
  (R y).2 ≠ none ∧ (r₂ y).1 = 0 ∧ (fl y).2.1 = false ∧ (r₃ y).1 = 0 ∧
    S.edgeTok hN (Net.parOf R y) y ≠ none

/-- **The dart of the token of an arc.** If the arc from `y'` to `y` carries a token, then its dart or
the reverse of its dart is the dart from the host of `y` to the neighbour in the name of `y`. -/
theorem edgeTok_host {y' y : Fin (n * (n * 21))} {x : S.Tok} (h : S.edgeTok hN y' y = some x) :
    ∃ d : N.G.Dart, hostOf y = d.fst ∧ (idEquiv.symm y).2.1 = d.snd ∧
      ((N.toRot.tokDart x.1).1 = d ∨ (N.toRot.tokDart x.1).1 = N.toRot.rev d) := by
  unfold edgeTok at h
  split_ifs at h with hc
  obtain ⟨-, hy⟩ := hc.choose_spec
  generalize hc.choose = e at h hy
  obtain ⟨e, b⟩ := e
  have hn : ∀ (d : N.G.Dart) (b : Bool),
      hostOf ((S.levelPad hN).ι (.inr (S.hrev (HE.rim d, b)))) = d.fst ∧
      (idEquiv.symm ((S.levelPad hN).ι (.inr (S.hrev (HE.rim d, b))))).2.1 = d.snd := fun d b => by
    unfold hostOf
    rw [S.levelPad_ι hN, Equiv.symm_apply_apply]
    cases b <;> exact ⟨rfl, rfl⟩
  rcases e with c | d | t | c | c | c <;> cases b <;> simp only [hdTok, reduceCtorEq] at h
  · cases h
    subst hy
    refine ⟨d, (hn d false).1, (hn d false).2, .inr ?_⟩
    rw [N.toRot.tokDart_fst]
    unfold rimTok
    split_ifs <;> rfl
  · cases h
    subst hy
    refine ⟨d, (hn d true).1, (hn d true).2, .inl ?_⟩
    rw [N.toRot.tokDart_fst]
    show N.toRot.rev (N.toRot.partner (S.rimTok d).1).1 = d
    unfold rimTok
    split_ifs <;> exact N.toRot.rev_rev d

/-- **The test at a node of a chain.** The test that decides the darts of a step at the node `l` of the
chain of `v` is the step bit at that node with `l` valid steps from `v`. -/
theorem crit_iff (R r₂ r₃ : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (fl : Fin (n * (n * 21)) → Bool × Bool × Bool) (v : Fin (n * (n * 21))) (l : ℕ)
    (z : N.G.Dart × Bool) :
    (Net.ParSteps R v (l + 1) ∧ (r₂ ((Net.parOf R)^[l] v)).1 = 0 ∧
      (fl ((Net.parOf R)^[l] v)).2.1 = false ∧ (r₃ ((Net.parOf R)^[l] v)).1 = 0 ∧ ∃ x,
        S.edgeTok hN ((Net.parOf R)^[l + 1] v) ((Net.parOf R)^[l] v) = some x ∧
        z = N.toRot.tokDart x.1) ↔
    (Net.ParSteps R v l ∧ S.stepBit hN R r₂ r₃ fl ((Net.parOf R)^[l] v) ∧ ∃ x,
      S.edgeTok hN (Net.parOf R ((Net.parOf R)^[l] v)) ((Net.parOf R)^[l] v) = some x ∧
        z = N.toRot.tokDart x.1) := by
  have hit : (Net.parOf R)^[l + 1] v = Net.parOf R ((Net.parOf R)^[l] v) :=
    Function.iterate_succ_apply' _ _ _
  have hps : Net.ParSteps R v (l + 1) ↔
      Net.ParSteps R v l ∧ (R ((Net.parOf R)^[l] v)).2 ≠ none := by
    constructor
    · intro h
      refine ⟨fun k hk => h k (by omega), ?_⟩
      rw [h l (by omega)]
      exact Option.some_ne_none _
    · rintro ⟨h, hn⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h k hk
      · rw [hit]
        obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 hn
        rw [hp, Net.parOf_some hp]
  rw [hps, hit]
  unfold stepBit
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5, x, hx, hz⟩
    exact ⟨h1, ⟨h2, h3, h4, h5, by rw [hx]; exact Option.some_ne_none _⟩, x, hx, hz⟩
  · rintro ⟨h1, ⟨h2, h3, h4, h5, -⟩, x, hx, hz⟩
    exact ⟨⟨h1, h2⟩, h3, h4, h5, x, hx, hz⟩

variable {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞}

/-- **Copies with the step bit lie on chains of targets.** With the run along the chains from the
targets of `Q`, every copy with the step bit lies `i` valid steps above the target of an annulus of
`Q`. -/
theorem stepBit_chain {ℓ : Fin (n * (n * 21)) → Fin (n * (n * 21)) → ℕ∞} {φ : Fin (n * (n * 21)) → ℕ∞}
    (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
    (R r₂ r₃ : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec ℓ φ R)
    (fl : Fin (n * (n * 21)) → Bool × Bool × Bool) (hfl : ∀ a, (fl a).1 = S.tgtFlag hN Q a)
    (hr₂ : (S.levelNet hN).ExactSpec (Net.markLenW R fun a => ((fl a).2.1.toNat : ℕ∞))
      (Net.markOffB fun a => (fl a).1) r₂)
    {y : Fin (n * (n * 21))} (hy : S.stepBit hN R r₂ r₃ fl y) :
    ∃ q ∈ Q, ∃ i, Net.ParSteps R ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) i ∧
      (Net.parOf R)^[i] ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) = y := by
  obtain ⟨t, i, ht, hs, hi⟩ := hr.chain_of_markW _ _ hr₂ (by rw [hy.2.1]; exact ENat.zero_ne_top)
  rw [hfl, tgtFlag, decide_eq_true_iff] at ht
  obtain ⟨q, hq, rfl⟩ := ht
  exact ⟨q, hq, i, hs, hi⟩


/-- The step bit read from distances: the counts of the two runs along the chains replaced by the
distances that every output of these runs holds. -/
def stepBitD (R : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (fl : Fin (n * (n * 21)) → Bool × Bool × Bool) (y : Fin (n * (n * 21))) : Prop :=
  (R y).2 ≠ none ∧
    (S.levelNet hN).dsrcTop (Net.markLenW R fun a => (((fl a).2.1).toNat : ℕ∞))
      (Net.markOffB fun a => (fl a).1) y = 0 ∧ (fl y).2.1 = false ∧
    (S.levelNet hN).dsrcTop (Net.downLenW R fun a => (((fl a).2.2).toNat : ℕ∞))
      (Net.markOffB fun a => (fl a).2.1 && decide ((S.levelNet hN).dsrcTop
        (Net.markLenW R fun a => (((fl a).2.1).toNat : ℕ∞)) (Net.markOffB fun a => (fl a).1) a = 0)) y = 0 ∧
    S.edgeTok hN (Net.parOf R y) y ≠ none

/-- **The step bit is fixed by the distances.** For any outputs of the two runs along the chains, the
step bit is the step bit read from distances. -/
theorem stepBit_iff_D (R r₂ r₃ : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (fl : Fin (n * (n * 21)) → Bool × Bool × Bool)
    (h₂ : (S.levelNet hN).ExactSpec (Net.markLenW R fun a => (((fl a).2.1).toNat : ℕ∞))
      (Net.markOffB fun a => (fl a).1) r₂)
    (h₃ : (S.levelNet hN).ExactSpec (Net.downLenW R fun a => (((fl a).2.2).toNat : ℕ∞))
      (Net.markOffB fun a => (fl a).2.1 && decide ((r₂ a).1 = 0)) r₃) (y : Fin (n * (n * 21))) :
    S.stepBit hN R r₂ r₃ fl y ↔ S.stepBitD hN R fl y := by
  have e2 : ∀ a, (r₂ a).1 = 0 ↔ (S.levelNet hN).dsrcTop (Net.markLenW R fun a => (((fl a).2.1).toNat : ℕ∞))
      (Net.markOffB fun a => (fl a).1) a = 0 := fun a => by
    rw [← h₂.dist_eq a, ENat.toENNReal_eq_zero]
  have hoff : (fun a => (fl a).2.1 && decide ((r₂ a).1 = 0)) = fun a => (fl a).2.1 && decide
      ((S.levelNet hN).dsrcTop (Net.markLenW R fun a => (((fl a).2.1).toNat : ℕ∞))
        (Net.markOffB fun a => (fl a).1) a = 0) := by
    funext a
    rw [decide_eq_decide.2 (e2 a)]
  rw [hoff] at h₃
  have e3 : (r₃ y).1 = 0 ↔ (S.levelNet hN).dsrcTop (Net.downLenW R fun a => (((fl a).2.2).toNat : ℕ∞))
      (Net.markOffB fun a => (fl a).2.1 && decide ((S.levelNet hN).dsrcTop
        (Net.markLenW R fun a => (((fl a).2.1).toNat : ℕ∞)) (Net.markOffB fun a => (fl a).1) a = 0)) y = 0 := by
    rw [← h₃.dist_eq y, ENat.toENNReal_eq_zero]
  unfold stepBit stepBitD
  rw [e2 y, e3]

end RData

end RotSystem

end SsspFlow
