import Mathlib.Logic.Equiv.Fin.Basic
import SsspFlow.HostSim

/-!
# Hosts that simulate an algorithm with `k` slots per edge

The same simulation as `Algorithm.simulate`, with up to `k` edges of `G'` on each edge of `G` and
direction. The hosts run `A` on `G` in the same number of rounds with messages of width `k * B`
(`Algorithm.simulateView`, `Algorithm.run_simulateView`). The slots on an edge need not be fixed in
advance: each host knows the edges of `G'` at its own identifiers, and both ends of an edge of `G`
list the pairs between them in the same order.
-/

set_option autoImplicit false

namespace Cslib.Congest.Algorithm

variable {V W I J σ : Type*} {B k : ℕ}

/-- `k` messages in one. -/
def msgPack (ms : Fin k → Msg B) : Msg (k * B) := fun i =>
  ms (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

/-- The message in slot `j`. -/
def msgUnpack (m : Msg (k * B)) (j : Fin k) : Msg B := fun b => m (finProdFinEquiv (j, b))

@[simp] theorem msgUnpack_pack (ms : Fin k → Msg B) (j : Fin k) :
    msgUnpack (msgPack ms) j = ms j := by
  funext b
  simp [msgUnpack, msgPack]

variable [Fintype W]

open Classical in
/-- The pairs of identifiers `(b, a)` with `b` at `v`, `a` at `u` and an edge from `b` to `a` in the
view `i`, in a fixed order. -/
noncomputable def viewPairs (h : W → V) (view : I → W → W → Prop) (i : I) (v u : V) : List (W × W) :=
  (Finset.univ.filter fun p : W × W => h p.1 = v ∧ h p.2 = u ∧ view i p.1 p.2).toList

open Classical in
/-- The pairs `(b, a)` with `b` at `v`, `a` at `u` and an edge from `b` to `a` in `G'`, in a fixed
order. -/
noncomputable def truePairs (h : W → V) (G' : SimpleGraph W) (v u : V) : List (W × W) :=
  (Finset.univ.filter fun p : W × W => h p.1 = v ∧ h p.2 = u ∧ G'.Adj p.1 p.2).toList

/-- A view that is correct on the pairs from `v` to `u` gives the true pairs. -/
theorem viewPairs_eq (h : W → V) (view : I → W → W → Prop) (G' : SimpleGraph W) (i : I) (v u : V)
    (hv : ∀ b a, h b = v → h a = u → (view i b a ↔ G'.Adj b a)) :
    viewPairs h view i v u = truePairs h G' v u := by
  classical
  unfold viewPairs truePairs
  congr 1
  apply Finset.filter_congr
  rintro ⟨b, a⟩ -
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (hv b a h1 h2).1 h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (hv b a h1 h2).2 h3⟩

open Classical in
/-- Hosts in `V` run `A` on the identifiers `W`. The host `h a` of `a` holds the state of `a`. The
input `i` of a host gives its view `view i b a` of the edges of `G'`. The slot `j` on the edge from
`v` to `u` carries the message of the `j`-th pair of `viewPairs`. -/
noncomputable def simulateView (A : Algorithm W J σ B) (h : W → V) (view : I → W → W → Prop)
    (vin : V → I → W → J) : Algorithm V I (I × (W → σ)) (k * B) where
  init v i := (i, fun a => A.init a (vin v i a))
  send v s u := msgPack fun j =>
    ((viewPairs h view s.1 v u)[j.1]?).elim (fun _ => false) fun p => A.send p.1 (s.2 p.1) p.2
  step v s m := (s.1, fun a => A.step a (s.2 a) fun b =>
    if h b = v then (if view s.1 b a then some (A.send b (s.2 b) a) else none)
    else (m (h b)).bind fun msg =>
      if hj : ∃ j : Fin k, (viewPairs h view s.1 (h b) v)[j.1]? = some (b, a) then
        some (msgUnpack msg hj.choose) else none)
  out _ _ := true

theorem simulateView_send (A : Algorithm W J σ B) (h : W → V) (view : I → W → W → Prop)
    (vin : V → I → W → J) (v : V) (s : I × (W → σ)) (u : V) :
    (simulateView (k := k) A h view vin).send v s u = msgPack fun j =>
      ((viewPairs h view s.1 v u)[j.1]?).elim (fun _ => false) fun p => A.send p.1 (s.2 p.1) p.2 :=
  rfl

/-- **The simulation is correct.** Each host has a view of the edges of `G'` that is correct on the
edges at its identifiers, every edge of `G'` between two hosts follows an edge of `G`, and at most `k`
edges of `G'` go from one host to another. -/
theorem run_simulateView (A : Algorithm W J σ B) (h : W → V) (view : I → W → W → Prop)
    (vin : V → I → W → J) (G : SimpleGraph V) [DecidableRel G.Adj]
    (G' : SimpleGraph W) [DecidableRel G'.Adj] (inp : V → I) (inp' : W → J)
    (hin : ∀ a, inp' a = vin (h a) (inp (h a)) a)
    (hview : ∀ v b a, (h b = v ∨ h a = v) → (view (inp v) b a ↔ G'.Adj b a))
    (hhost : ∀ b a, G'.Adj b a → h b ≠ h a → G.Adj (h b) (h a))
    (hk : ∀ v u, v ≠ u → Nat.card {p : W × W // h p.1 = v ∧ h p.2 = u ∧ G'.Adj p.1 p.2} ≤ k)
    (t : ℕ) (v : V) :
    ((simulateView (k := k) A h view vin).run G inp t v).1 = inp v ∧
      ∀ a, h a = v → ((simulateView (k := k) A h view vin).run G inp t v).2 a = A.run G' inp' t a := by
  classical
  induction t generalizing v with
  | zero =>
    refine ⟨rfl, fun a ha => ?_⟩
    show A.init a (vin v (inp v) a) = A.init a (inp' a)
    rw [hin, ha]
  | succ t ih =>
    refine ⟨(ih v).1, fun a ha => ?_⟩
    show A.step a (((simulateView (k := k) A h view vin).run G inp t v).2 a) _ =
      A.step a (A.run G' inp' t a) _
    rw [(ih v).2 a ha]
    congr 1
    funext b
    subst ha
    by_cases hb : h b = h a
    · rw [ite_eq_left hb, (ih (h a)).1, (ih (h a)).2 b hb]
      by_cases hadj : G'.Adj b a
      · rw [ite_eq_left hadj, ite_eq_left ((hview _ b a (.inr rfl)).2 hadj)]
      · rw [ite_eq_right hadj, ite_eq_right fun x => hadj ((hview _ b a (.inr rfl)).1 x)]
    · rw [ite_eq_right hb]
      have hS : ((simulateView (k := k) A h view vin).run G inp t (h b)).2 b = A.run G' inp' t b :=
        (ih (h b)).2 b rfl
      have hP : ∀ w, (w = h b ∨ w = h a) →
          viewPairs h view (inp w) (h b) (h a) = truePairs h G' (h b) (h a) := by
        intro w hw
        refine viewPairs_eq h view G' _ _ _ fun b' a' h1 h2 => hview w b' a' ?_
        rcases hw with rfl | rfl
        · exact .inl h1
        · exact .inr h2
      have hmem : ∀ p, p ∈ truePairs h G' (h b) (h a) ↔ h p.1 = h b ∧ h p.2 = h a ∧ G'.Adj p.1 p.2 := by
        intro p
        simp [truePairs]
      beta_reduce
      simp only [simulateView_send, (ih (h a)).1, (ih (h b)).1, hP _ (.inl rfl), hP _ (.inr rfl)]
      by_cases hadj : G.Adj (h b) (h a)
      · rw [ite_eq_left hadj, Option.bind_some]
        by_cases hj : ∃ j : Fin k, (truePairs h G' (h b) (h a))[j.1]? = some (b, a)
        · rw [dite_eq_left_of_eq_true (eq_true hj), msgUnpack_pack, hj.choose_spec, Option.elim_some, hS]
          have hm := List.mem_of_getElem? hj.choose_spec
          rw [ite_eq_left ((hmem _).1 hm).2.2]
        · rw [dite_eq_right_of_eq_false (eq_false hj), ite_eq_right]
          intro hg
          obtain ⟨i, hi, hx⟩ := List.getElem_of_mem ((hmem (b, a)).2 ⟨rfl, rfl, hg⟩)
          have hl : (truePairs h G' (h b) (h a)).length ≤ k := by
            unfold truePairs
            rw [Finset.length_toList, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
            exact hk _ _ hb
          exact hj ⟨⟨i, by omega⟩, by rw [List.getElem?_eq_getElem hi, hx]⟩
      · rw [ite_eq_right hadj, Option.bind_none, ite_eq_right]
        exact fun hg => hadj (hhost b a hg hb)

end Cslib.Congest.Algorithm
