import SsspFlow.GHatChainCorners
import SsspFlow.GHatChainTargets

/-!
# The first flagged node on the chain of a target

After a counting run up the parent chains from the targets of a list `Q` of annuli of a level, with
the flag of a choice of corners as lengths, a node is marked when it is flagged and its count is `0`.
The marked nodes are the first flagged nodes on the chains of the targets. So the region of each
annulus of `Q` holds at most one marked node, and it holds one when the chain of its target has a
flagged node.

* `RData.mark_onChain`: a marked node is the first flagged node on the chain of the target of an
  annulus of `Q`.
* `RData.mark_unique`: two marked nodes whose copies lie at corners of the region of one annulus of `Q`
  are equal.
* `RData.mark_exists`: a flagged node on the chain of a target gives a marked node on that chain.
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

variable {ℓ' : Fin (n * (n * 21)) → Fin (n * (n * 21)) → ℕ∞} {φ : Fin (n * (n * 21)) → ℕ∞}
  {R r₂ : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21)))}
  (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
  (P : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') → N.G.Dart × Bool → Prop)

open Classical in
/-- **A marked node lies first on a chain.** A node that is flagged with count `0` is the first
flagged node, `i` valid steps above the target of an annulus of `Q`. -/
theorem mark_onChain (hRs : (S.levelNet hN).ExactSpec ℓ' φ R)
    (h₂ : (S.levelNet hN).ExactSpec (Net.markLenW R fun a => ((decide (S.cornerFlag hN Q P a)).toNat : ℕ∞))
      (Net.markOffB (S.tgtFlag hN Q)) r₂)
    (hT : ∀ t t' i i', S.tgtFlag hN Q t = true → S.tgtFlag hN Q t' = true → Net.ParSteps R t i →
      Net.ParSteps R t' i' → (Net.parOf R)^[i] t = (Net.parOf R)^[i'] t' → t = t')
    {a : Fin (n * (n * 21))} (ha : (r₂ a).1 = 0) :
    ∃ q ∈ Q, ∃ i, Net.ParSteps R ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) i ∧
      (Net.parOf R)^[i] ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) = a ∧
      ∀ l < i, ¬ S.cornerFlag hN Q P ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2))))) := by
  have e : (Net.markLenW R fun a => ((decide (S.cornerFlag hN Q P a)).toNat : ℕ∞)) =
      Net.markLenW R fun a => if S.cornerFlag hN Q P a then 1 else 0 := by
    congr 1
    funext a
    by_cases h : S.cornerFlag hN Q P a <;> simp [h]
  rw [e] at h₂
  have h0 : (S.levelNet hN).dsrcTop (Net.markLenW R fun a => if S.cornerFlag hN Q P a then 1 else 0)
      (Net.markOffB (S.tgtFlag hN Q)) a = 0 := by
    rw [← h₂.dist_eq, ha]; exact ENat.toENNReal_zero
  have hex : ∃ t, S.tgtFlag hN Q t = true ∧ ∃ i, Net.ParSteps R t i ∧ (Net.parOf R)^[i] t = a := by
    by_contra hne
    push_neg at hne
    rw [hRs.dsrcTop_markW] at h0
    have htop : (⨅ t, ⨅ (_ : S.tgtFlag hN Q t = true), ⨅ i, ⨅ (_ : Net.ParSteps R t i ∧ (Net.parOf R)^[i] t = a),
        ((∑ k ∈ Finset.range i, (fun a => if S.cornerFlag hN Q P a then (1 : ℕ∞) else 0)
          ((Net.parOf R)^[k] t) : ℕ∞) : ℝ≥0∞)) = ⊤ := by
      refine iInf_eq_top.2 fun t => iInf_eq_top.2 fun ht => iInf_eq_top.2 fun i => iInf_eq_top.2 fun hi => ?_
      exact absurd hi.2 (hne t ht i hi.1)
    rw [htop] at h0
    exact ENNReal.top_ne_zero h0
  obtain ⟨t, ht, i, hs, rfl⟩ := hex
  have ht' := ht
  unfold tgtFlag at ht'
  obtain ⟨q, hq, rfl⟩ := of_decide_eq_true ht'
  refine ⟨q, hq, i, hs, rfl, ?_⟩
  exact (hRs.dsrcTop_flag_eq_zero (fun a => S.cornerFlag hN Q P a) (S.tgtFlag hN Q) hT ht hs).1 h0

variable {r : CutPath.Run hR hC hg Γ₀ L₀ j k} {ℓ : ℕ}

open Classical in
/-- **At most one marked node per region.** Two nodes that are flagged with count `0` and whose
copies have pieces at corners of the region of one annulus of `Q` are equal. -/
theorem mark_unique (hRs : (S.levelNet hN).ExactSpec ℓ' φ R)
    (h₂ : (S.levelNet hN).ExactSpec (Net.markLenW R fun a => ((decide (S.cornerFlag hN Q P a)).toNat : ℕ∞))
      (Net.markOffB (S.tgtFlag hN Q)) r₂)
    (hT : ∀ t t' i i', S.tgtFlag hN Q t = true → S.tgtFlag hN Q t' = true → Net.ParSteps R t i →
      Net.ParSteps R t' i' → (Net.parOf R)^[i] t = (Net.parOf R)^[i'] t' → t = t')
    (hQ : ∀ q ∈ Q, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧ q.2 ≤ q.1.2.xb ∧ q.2 ≤ q.1.2.yb)
    (hQu : ∀ q ∈ Q, ∀ q' ∈ Q, q.1 = q'.1 → q.2 = q'.2)
    (hvc : ∀ q ∈ Q, ∃ (p : List (N.G.Dart × Bool)) (b : (N.toRot.dual.double.split q.1.1).Vertex),
      (N.toRot.dual.double.split q.1.1).IsWalk ((N.toRot.dual.double.split q.1.1).tail (q.1.2.κ0 q.2)) p b ∧
      ∀ c, q.1.2.Visits q.2 p c ↔ ∃ y, (∃ i, (Net.parOf R)^[i] ((S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2)))) = y) ∧
        ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)),
          S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) = S.dualSplit.tail c)
    {A : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ} (hA : A ∈ Q)
    {a a' : Fin (n * (n * 21))} (hfa : S.cornerFlag hN Q P a) (ha : (r₂ a).1 = 0)
    (hfa' : S.cornerFlag hN Q P a') (ha' : (r₂ a').1 = 0) {y y' : N.G.Dart × Bool}
    (hy : (N.toRot.dual.double.split A.1.1).toHypermap.gcomp (A.1.2.κ0 A.1.2.xa) y)
    (hy' : (N.toRot.dual.double.split A.1.1).toHypermap.gcomp (A.1.2.κ0 A.1.2.xa) y')
    (hpa : ∃ he : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN a)),
      S.vertexEquiv (S.pieceOf ⟨S.copyAt hN a, he⟩) = S.dualSplit.tail y)
    (hpa' : ∃ he : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN a')),
      S.vertexEquiv (S.pieceOf ⟨S.copyAt hN a', he⟩) = S.dualSplit.tail y') : a = a' := by
  -- the annulus of the chain of a marked node with a piece in the region of `A` is `A`
  have own : ∀ {b : Fin (n * (n * 21))} {z : N.G.Dart × Bool}, (r₂ b).1 = 0 →
      (N.toRot.dual.double.split A.1.1).toHypermap.gcomp (A.1.2.κ0 A.1.2.xa) z →
      (∃ he : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN b)),
        S.vertexEquiv (S.pieceOf ⟨S.copyAt hN b, he⟩) = S.dualSplit.tail z) →
      ∃ i, Net.ParSteps R ((S.levelPad hN).ι (.inl (S.endV (A.1.2.κ1 A.2)))) i ∧
        (Net.parOf R)^[i] ((S.levelPad hN).ι (.inl (S.endV (A.1.2.κ1 A.2)))) = b ∧
        ∀ l < i, ¬ S.cornerFlag hN Q P ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (A.1.2.κ1 A.2))))) := by
    intro b z hb hz hpb
    obtain ⟨q, hq, i, hs, hi, hl⟩ := S.mark_onChain hN Q P hRs h₂ hT hb
    obtain ⟨p, bq, hp, hv⟩ := hvc q hq
    have hvz : q.1.2.Visits q.2 p z := (hv z).2 ⟨b, ⟨i, hi⟩, hpb⟩
    obtain ⟨hqn, h1, -, h3, -⟩ := hQ q hq
    have hgq := connect_trans (q.1.2.gcomp_κ0 h1 h3) (q.1.2.gcomp_of_visits hp hvz)
    have e1 : q.1 = A.1 := r.sep ℓ q.1 hqn A.1 (hQ A hA).1 z hgq hz
    have e : q = A := Prod.ext e1 (hQu q hq A hA e1)
    subst e
    exact ⟨i, hs, hi, hl⟩
  obtain ⟨i, hs, rfl, hl⟩ := own ha hy hpa
  obtain ⟨i', hs', hi', hl'⟩ := own ha' hy' hpa'
  subst hi'
  rcases lt_trichotomy i i' with h | h | h
  · exact absurd hfa (hl' i h)
  · rw [h]
  · exact absurd hfa' (hl i' h)

open Classical in
/-- **A flagged node gives a marked node.** If a node `i` valid steps above the target `t` of an
annulus of `Q` is flagged, the first flagged node above `t` is flagged with count `0`. -/
theorem mark_exists (hRs : (S.levelNet hN).ExactSpec ℓ' φ R)
    (h₂ : (S.levelNet hN).ExactSpec (Net.markLenW R fun a => ((decide (S.cornerFlag hN Q P a)).toNat : ℕ∞))
      (Net.markOffB (S.tgtFlag hN Q)) r₂)
    (hT : ∀ t t' i i', S.tgtFlag hN Q t = true → S.tgtFlag hN Q t' = true → Net.ParSteps R t i →
      Net.ParSteps R t' i' → (Net.parOf R)^[i] t = (Net.parOf R)^[i'] t' → t = t')
    {t : Fin (n * (n * 21))} (ht : S.tgtFlag hN Q t = true) {i : ℕ} (hs : Net.ParSteps R t i)
    (hf : S.cornerFlag hN Q P ((Net.parOf R)^[i] t)) :
    ∃ i' ≤ i, S.cornerFlag hN Q P ((Net.parOf R)^[i'] t) ∧ (r₂ ((Net.parOf R)^[i'] t)).1 = 0 := by
  have e : (Net.markLenW R fun a => ((decide (S.cornerFlag hN Q P a)).toNat : ℕ∞)) =
      Net.markLenW R fun a => if S.cornerFlag hN Q P a then 1 else 0 := by
    congr 1
    funext a
    by_cases h : S.cornerFlag hN Q P a <;> simp [h]
  rw [e] at h₂
  have hex : ∃ l, S.cornerFlag hN Q P ((Net.parOf R)^[l] t) ∧ l ≤ i := ⟨i, hf, le_rfl⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).2, (Nat.find_spec hex).1, ?_⟩
  have hs' : Net.ParSteps R t (Nat.find hex) := fun l hl => hs l (lt_of_lt_of_le hl (Nat.find_spec hex).2)
  rw [← ENat.toENNReal_eq_zero, h₂.dist_eq,
    hRs.dsrcTop_flag_eq_zero (fun a => S.cornerFlag hN Q P a) (S.tgtFlag hN Q) hT ht hs']
  intro l hl hfl
  exact Nat.find_min hex hl ⟨hfl, (le_of_lt hl).trans (Nat.find_spec hex).2⟩

end RData

end RotSystem

end SsspFlow
