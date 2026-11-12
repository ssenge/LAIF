import Mathlib.Tactic.FinCases
import SsspFlow.Congest

/-!
# Hosts that simulate an algorithm on identifiers

An algorithm `A` runs on a graph `G'` on identifiers `W`. Every identifier has a host in `V`. If the
edges of `G'` between two different hosts follow the edges of `G`, at most two per edge and direction,
then the hosts run `A` on `G` in the same number of rounds with messages of twice the width
(`Algorithm.simulate`, `Algorithm.run_simulate`).
-/

set_option autoImplicit false

namespace Cslib.Congest.Algorithm

variable {V W I J σ : Type*} {B : ℕ}

/-- Two messages in one. -/
def msgPair (m₀ m₁ : Msg B) : Msg (B + B) :=
  fun i => if h : i.1 < B then m₀ ⟨i.1, h⟩ else m₁ ⟨i.1 - B, by omega⟩

/-- The first message of a pair. -/
def msgFst (m : Msg (B + B)) : Msg B := fun i => m ⟨i.1, by omega⟩

/-- The second message of a pair. -/
def msgSnd (m : Msg (B + B)) : Msg B := fun i => m ⟨B + i.1, by omega⟩

@[simp] theorem msgFst_pair (m₀ m₁ : Msg B) : msgFst (msgPair m₀ m₁) = m₀ := by
  funext i
  simp [msgFst, msgPair]

@[simp] theorem msgSnd_pair (m₀ m₁ : Msg B) : msgSnd (msgPair m₀ m₁) = m₁ := by
  funext i
  simp [msgSnd, msgPair]

open Classical in
/-- Hosts in `V` run `A` on the identifiers `W`. The host `h a` of `a` holds the state of `a`.
`locAdj v i b a` is the local knowledge of `v` with input `i` about an edge from `b` to `a`, both at `v`,
and `cross v u j` is the pair of identifiers that uses the slot `j` on the edge from `v` to `u`. -/
noncomputable def simulate (A : Algorithm W J σ B) (h : W → V) (locAdj : V → I → W → W → Prop)
    (cross : V → V → Fin 2 → W × W) (vin : V → I → W → J) :
    Algorithm V I (I × (W → σ)) (B + B) where
  init v i := (i, fun a => A.init a (vin v i a))
  send v s u := msgPair (A.send (cross v u 0).1 (s.2 (cross v u 0).1) (cross v u 0).2)
    (A.send (cross v u 1).1 (s.2 (cross v u 1).1) (cross v u 1).2)
  step v s m := (s.1, fun a => A.step a (s.2 a) fun b =>
    if h b = v then (if locAdj v s.1 b a then some (A.send b (s.2 b) a) else none)
    else (m (h b)).bind fun msg =>
      if cross (h b) v 0 = (b, a) then some (msgFst msg)
      else if cross (h b) v 1 = (b, a) then some (msgSnd msg) else none)
  out _ _ := true

/-- **The simulation is correct.** -/
theorem run_simulate (A : Algorithm W J σ B) (h : W → V) (locAdj : V → I → W → W → Prop)
    (cross : V → V → Fin 2 → W × W) (vin : V → I → W → J) (G : SimpleGraph V) [DecidableRel G.Adj]
    (G' : SimpleGraph W) [DecidableRel G'.Adj] (inp : V → I) (inp' : W → J)
    (hin : ∀ a, inp' a = vin (h a) (inp (h a)) a)
    (hloc : ∀ b a, h b = h a → (locAdj (h a) (inp (h a)) b a ↔ G'.Adj b a))
    (hcross : ∀ b a, h b ≠ h a →
      (G'.Adj b a ↔ G.Adj (h b) (h a) ∧ ∃ j, cross (h b) (h a) j = (b, a))) (t : ℕ) (v : V) :
    ((simulate A h locAdj cross vin).run G inp t v).1 = inp v ∧
      ∀ a, h a = v → ((simulate A h locAdj cross vin).run G inp t v).2 a = A.run G' inp' t a := by
  classical
  induction t generalizing v with
  | zero =>
    refine ⟨rfl, fun a ha => ?_⟩
    show A.init a (vin v (inp v) a) = A.init a (inp' a)
    rw [hin, ha]
  | succ t ih =>
    refine ⟨(ih v).1, fun a ha => ?_⟩
    show A.step a (((simulate A h locAdj cross vin).run G inp t v).2 a) _ =
      A.step a (A.run G' inp' t a) _
    rw [(ih v).2 a ha]
    congr 1
    funext b
    subst ha
    by_cases hb : h b = h a
    · rw [ite_eq_left hb, (ih (h a)).1, (ih (h a)).2 b hb]
      by_cases hadj : G'.Adj b a
      · rw [ite_eq_left hadj, ite_eq_left ((hloc b a hb).2 hadj)]
      · rw [ite_eq_right hadj, ite_eq_right fun x => hadj ((hloc b a hb).1 x)]
    · rw [ite_eq_right hb]
      have hc := hcross b a hb
      have hS : ((simulate A h locAdj cross vin).run G inp t (h b)).2 b = A.run G' inp' t b :=
        (ih (h b)).2 b rfl
      beta_reduce
      by_cases hadj : G.Adj (h b) (h a)
      · rw [ite_eq_left hadj, Option.bind_some]
        by_cases h0 : cross (h b) (h a) 0 = (b, a)
        · rw [ite_eq_left h0, ite_eq_left (hc.2 ⟨hadj, 0, h0⟩)]
          show some (msgFst (msgPair _ _)) = _
          rw [msgFst_pair, h0]
          simp only
          rw [hS]
        · rw [ite_eq_right h0]
          by_cases h1 : cross (h b) (h a) 1 = (b, a)
          · rw [ite_eq_left h1, ite_eq_left (hc.2 ⟨hadj, 1, h1⟩)]
            show some (msgSnd (msgPair _ _)) = _
            rw [msgSnd_pair, h1]
            simp only
            rw [hS]
          · rw [ite_eq_right h1, ite_eq_right]
            intro hg
            obtain ⟨-, j, hj⟩ := hc.1 hg
            fin_cases j
            · exact h0 hj
            · exact h1 hj
      · rw [ite_eq_right hadj, Option.bind_none, ite_eq_right]
        exact fun hg => hadj (hc.1 hg).1

end Cslib.Congest.Algorithm
