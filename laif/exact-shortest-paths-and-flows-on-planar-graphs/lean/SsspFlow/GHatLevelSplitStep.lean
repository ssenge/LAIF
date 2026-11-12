import SsspFlow.GHatLevelDarts
import SsspFlow.ShortestSimple

/-!
# The step from a split of a walk of a level

Let a walk of the network of a level between the pieces at `κ0(t)` and `κ1(t)`, below `M` and at most
`λ_t`, with positive costs, be split at two nodes into three walks. If the copy of the first node is
at a copy `p_x^0`, that of the second at a copy `p_y^1`, no dart after the first node ends at a copy
`p_r^0` and no dart between the two nodes starts at a copy `p_r^1`, then the darts between the two
nodes are the darts of a step of the annulus.

* `RData.levelDarts_append`: the darts of a joined walk are the darts of its parts.
* `RData.level_step_of_split`: the darts between the two nodes of such a split are the darts of a step.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ)

/-- The darts of a joined walk are the darts of its parts. -/
theorem levelDarts_append : ∀ {a b c : Fin (n * (n * 21))} (p : SsspFlow.Walk (S.levelNet hN).G.Adj a b)
    (q : SsspFlow.Walk (S.levelNet hN).G.Adj b c),
    S.levelDarts hN (p.append q) = S.levelDarts hN p ++ S.levelDarts hN q
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons e p, q => by
    show S.levelDarts hN (.cons e (p.append q)) = _
    rw [levelDarts_cons, levelDarts_cons, levelDarts_append p q, List.append_assoc]

/-- **The step from a split of a walk of a level.** For positive costs `c` of the darts, equal on the
two darts of an edge, token lengths that are these costs, and corners of `S` that hold those of a live
annulus, the others out of its reach: let a walk of the network of a level between copies on E_R
edges of the pieces at `κ0(t)` and `κ1(t)`, below `M` and at most `λ_t`, be split at nodes `a` and
`b`. If the copy of `a` is at a copy `p_x^0`, the copy of `b` at a copy `p_y^1`, no dart after `a`
ends at a copy `p_r^0` and no dart between `a` and `b` starts at a copy `p_r^1`, then the darts
between `a` and `b` are the darts of a step. -/
theorem level_step_of_split {C : N.toRot.dual.CutPath} {Γ : Finset (N.G.Dart × Bool)}
    (hR : N.toRot.dual.Planar) (hC : N.toRot.dual.Connected) (c : N.G.Dart → ℕ) (hc1 : ∀ d, 1 ≤ c d)
    (hcr : ∀ d, c (N.toRot.rev d) = c d) (hlam : ∀ x, lam x = c x.1.1)
    (L : C.Live (Nat.cast ∘ c) Γ) (hS : Γ ⊆ S.Γ) {t : ℕ}
    (hz : ∀ w ∈ S.Γ, w ∉ Γ → ∀ p, ¬ (N.toRot.dual.double.split Γ).IsWalk
      ((N.toRot.dual.double.split Γ).tail (L.κ0 t)) p ((N.toRot.dual.double.split Γ).tail w))
    (h1 : L.xa ≤ t) (h2 : L.ya ≤ t) (h3 : t ≤ L.xb) (h4 : t ≤ L.yb)
    {u v : S.hRot.Vertex} {a b : Fin (n * (n * 21))}
    (pa : SsspFlow.Walk (S.levelNet hN).G.Adj ((S.levelPad hN).ι (.inl u)) a)
    (pq : SsspFlow.Walk (S.levelNet hN).G.Adj a b)
    (pc : SsspFlow.Walk (S.levelNet hN).G.Adj b ((S.levelPad hN).ι (.inl v)))
    (hp : (pa.append (pq.append pc)).wt (lenTop (S.levelLen hN lam M)) < M)
    (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)) (hv : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v))
    (hpu : S.pieceOf ⟨S.vcopy u, hu⟩ = S.pieceAt (L.κ0 t))
    (hpv : S.pieceOf ⟨S.vcopy v, hv⟩ = S.pieceAt (L.κ1 t))
    (hle : (pa.append (pq.append pc)).wt (lenTop (S.levelLen hN lam M)) ≤ C.lamD (Nat.cast ∘ c) t)
    (xa xb : S.Tok) (hxa : S.IsEnd xa.1 (S.copyAt hN a)) (hxb : S.IsEnd xb.1 (S.copyAt hN b))
    (hs : C.atCopy Γ 0 ((N.toRot.dual.double.split Γ).tail (N.toRot.tokDart xa.1)))
    (hs' : C.atCopy Γ 1 ((N.toRot.dual.double.split Γ).tail (N.toRot.tokDart xb.1)))
    (hnb : ∀ z ∈ S.levelDarts hN pq ++ S.levelDarts hN pc,
      ¬ C.atCopy Γ 0 ((N.toRot.dual.double.split Γ).head z))
    (hnQ : ∀ z ∈ S.levelDarts hN pq, ¬ C.atCopy Γ 1 ((N.toRot.dual.double.split Γ).tail z)) :
    ∃ St : L.Step, (List.range St.n).map St.q = S.levelDarts hN pq := by
  have hsplit : S.levelDarts hN (pa.append (pq.append pc)) =
      S.levelDarts hN pa ++ (S.levelDarts hN pq ++ S.levelDarts hN pc) := by
    rw [levelDarts_append, levelDarts_append]
  obtain ⟨hsh, -⟩ := S.level_shortest_darts hN lam M c hcr hlam (g := Nat.cast ∘ c) (fun _ => rfl) L hS hz
    h1 h2 h3 h4 _ hp hu hv hpu hpv hle
  obtain ⟨hnd, hne⟩ := L.shortest_simple hc1 hsh
  rw [hsplit] at hsh hnd hne
  rw [SsspFlow.Walk.wt_append, SsspFlow.Walk.wt_append] at hp
  have hwa : pa.wt (lenTop (S.levelLen hN lam M)) < M := lt_of_le_of_lt le_self_add hp
  have hwq : pq.wt (lenTop (S.levelLen hN lam M)) < M :=
    lt_of_le_of_lt (le_self_add.trans le_add_self) hp
  have hwc : pc.wt (lenTop (S.levelLen hN lam M)) < M :=
    lt_of_le_of_lt (le_add_self.trans le_add_self) hp
  have hz₁ : ∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN ((S.levelPad hN).ι (.inl u))) := by
    rw [S.copyAt_ι]; exact hu
  have hz₂ : ∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN ((S.levelPad hN).ι (.inl v))) := by
    rw [S.copyAt_ι]; exact hv
  obtain ⟨wa, -, -⟩ := S.levelDarts_walk hN lam M c hcr hlam pa hz₁ ⟨xa, hxa⟩ hwa
  obtain ⟨wq, -, -⟩ := S.levelDarts_walk hN lam M c hcr hlam pq ⟨xa, hxa⟩ ⟨xb, hxb⟩ hwq
  obtain ⟨wc, -, -⟩ := S.levelDarts_walk hN lam M c hcr hlam pc ⟨xb, hxb⟩ hz₂ hwc
  have e₁ : S.vertexEquiv (S.pieceOf ⟨_, hz₁⟩) = S.dualSplit.tail (L.κ0 t) := by
    have e : S.pieceOf ⟨_, hz₁⟩ = S.pieceOf ⟨S.vcopy u, hu⟩ :=
      congrArg S.pieceOf (Subtype.ext (S.copyAt_ι hN _))
    rw [e, hpu, S.vertexEquiv_pieceAt]
  have e₂ : S.vertexEquiv (S.pieceOf ⟨_, hz₂⟩) = S.dualSplit.tail (L.κ1 t) := by
    have e : S.pieceOf ⟨_, hz₂⟩ = S.pieceOf ⟨S.vcopy v, hv⟩ :=
      congrArg S.pieceOf (Subtype.ext (S.copyAt_ι hN _))
    rw [e, hpv, S.vertexEquiv_pieceAt]
  have ea : S.vertexEquiv (S.pieceOf ⟨_, ⟨xa, hxa⟩⟩) = S.dualSplit.tail (N.toRot.tokDart xa.1) := by
    rw [S.pieceOf_eq ⟨S.copyAt hN a, ⟨xa, hxa⟩⟩ (x := xa) hxa]; rfl
  have eb : S.vertexEquiv (S.pieceOf ⟨_, ⟨xb, hxb⟩⟩) = S.dualSplit.tail (N.toRot.tokDart xb.1) := by
    rw [S.pieceOf_eq ⟨S.copyAt hN b, ⟨xb, hxb⟩⟩ (x := xb) hxb]; rfl
  rw [e₁, ea] at wa
  rw [ea, eb] at wq
  rw [eb, e₂] at wc
  have wa' := (N.toRot.dual.double.isWalk_split_split_iff hS hz _ ⟨[], rfl⟩ _).1 wa
  have wq' := (N.toRot.dual.double.isWalk_split_split_iff hS hz _ ⟨_, wa'⟩ _).1 wq
  have wc' := (N.toRot.dual.double.isWalk_split_split_iff hS hz _ ⟨_, wa'.append wq'⟩ _).1 wc
  exact L.step_of_split hR hC h1 h3 wa' wq' wc' hs hs' hnb hnQ hnd hne hsh.2.1 hsh.2.2

end RData

end RotSystem

end SsspFlow
