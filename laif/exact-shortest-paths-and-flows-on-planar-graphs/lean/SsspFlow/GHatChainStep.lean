import SsspFlow.GHatLevelSplitStep
import SsspFlow.OracleChainSeg

/-!
# The step on the parent chain of a target

Let an output of the oracle on the network of a level meet its specification, and let the parent
chain of a target copy `v` reach, after `k` valid steps, a copy `u` at the piece at `κ0(t)`, with sum
of lengths below `M` and at most `λ_t`. Take two nodes of the chain, `iy ≤ ia` steps above `v`, whose
copies lie at a copy `p_y^1` and a copy `p_x^0`. If no dart of a chain edge below the upper node ends
at a copy `p_r^0` and no dart of a chain edge between them starts at a copy `p_r^1`, then the darts of
the chain edges between the two nodes are the darts of a step of the annulus.

* `RData.levelDarts_sub`: a dart of a walk of a level is the dart of the token of one of its edges.
* `RData.levelDarts_of_hasEdge`: the dart of the token of an edge of a walk is a dart of the walk.
* `RData.levelDarts_eq_edgeFlat`, `RData.chainDarts`, `RData.chainDarts_add`: the darts of a walk
  read off its edges; the darts of the parent steps of a chain, from the top down, and their split.
* `RData.chain_step`: the darts of the chain edges between two such nodes are the darts of a step, in
  order.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ)

/-- A dart of a walk of a level is the dart of the token of one of its edges. -/
theorem levelDarts_sub {P : Fin (n * (n * 21)) → Fin (n * (n * 21)) → Prop} :
    ∀ {a b : Fin (n * (n * 21))} (q : SsspFlow.Walk (S.levelNet hN).G.Adj a b), q.AllEdges P →
      ∀ z ∈ S.levelDarts hN q, ∃ y y' x, P y y' ∧ S.edgeTok hN y y' = some x ∧ z = N.toRot.tokDart x.1
  | _, _, .nil _, _, z, hz => by simp [levelDarts] at hz
  | a, _, .cons (b := b) _ p, hq, z, hz => by
    rw [levelDarts_cons, List.mem_append] at hz
    rcases hz with hz | hz
    · cases h : S.edgeTok hN a b with
      | none => simp [h] at hz
      | some x =>
        simp only [h, Option.map_some, Option.toList_some, List.mem_singleton] at hz
        exact ⟨a, b, x, hq.1, h, hz⟩
    · exact levelDarts_sub p hq.2 z hz

/-- The dart of the token of an edge of a walk of a level is a dart of the walk. -/
theorem levelDarts_of_hasEdge {y y' : Fin (n * (n * 21))} {x : S.Tok} (he : S.edgeTok hN y y' = some x) :
    ∀ {a b : Fin (n * (n * 21))} (q : SsspFlow.Walk (S.levelNet hN).G.Adj a b), q.HasEdge y y' →
      N.toRot.tokDart x.1 ∈ S.levelDarts hN q
  | _, _, .nil _, h => h.elim
  | a, _, .cons (b := b) _ p, h => by
    rw [levelDarts_cons]
    rcases h with ⟨rfl, rfl⟩ | h
    · rw [he]
      simp
    · exact List.mem_append_right _ (levelDarts_of_hasEdge he p h)

/-- The darts of a walk of a level are read off its edges. -/
theorem levelDarts_eq_edgeFlat : ∀ {a b : Fin (n * (n * 21))} (q : SsspFlow.Walk (S.levelNet hN).G.Adj a b),
    S.levelDarts hN q = q.edgeFlat fun y y' => ((S.edgeTok hN y y').map fun x => N.toRot.tokDart x.1).toList
  | _, _, .nil _ => rfl
  | _, _, .cons _ p => by rw [levelDarts_cons, levelDarts_eq_edgeFlat p]; rfl

/-- The darts of the tokens of the parent steps `j + d - 1, …, j` above `v`, from the top down. -/
noncomputable def chainDarts (r : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (v : Fin (n * (n * 21))) (j d : ℕ) : List (N.G.Dart × Bool) :=
  ((List.range d).reverse.map fun l => ((S.edgeTok hN ((Net.parOf r)^[j + l + 1] v)
    ((Net.parOf r)^[j + l] v)).map fun x => N.toRot.tokDart x.1).toList).flatten

/-- The darts of `a + b` parent steps from `j` are those of the upper `a` steps, then those of the
lower `b` steps. -/
theorem chainDarts_add (r : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (v : Fin (n * (n * 21))) (j a b : ℕ) :
    S.chainDarts hN r v j (b + a) = S.chainDarts hN r v (j + b) a ++ S.chainDarts hN r v j b := by
  unfold chainDarts
  rw [List.range_add, List.reverse_append, List.map_append, List.flatten_append, List.map_reverse,
    List.map_map, List.map_reverse]
  congr 2
  rw [← List.map_reverse]
  congr 1
  funext l
  simp only [Function.comp_apply, Nat.add_assoc]

/-- **The step on the parent chain of a target.** For positive costs `c` of the darts, equal on the two
darts of an edge, token lengths that are these costs, and corners of `S` that hold those of a live
annulus, the others out of its reach: let an output `r` of the oracle on the network of a level meet
its specification, and let the chain of the copy node of `v` take `k` valid parent steps to the copy
node of `u`, at the piece at `κ0(t)`, with sum of lengths below `M` and at most `λ_t`, where `v` lies at
the piece at `κ1(t)`. Let the copies of the nodes `ia` and `iy ≤ ia` steps above `v` hold tokens at a
copy `p_x^0` and a copy `p_y^1`. If no dart of a chain edge below the node `ia` ends at a copy `p_r^0`
and no dart of a chain edge between the two nodes starts at a copy `p_r^1`, then there is a step whose
darts are exactly the darts of the tokens of the chain edges between the two nodes. -/
theorem chain_step {C : N.toRot.dual.CutPath} {Γ : Finset (N.G.Dart × Bool)}
    (hR : N.toRot.dual.Planar) (hC : N.toRot.dual.Connected) (c : N.G.Dart → ℕ) (hc1 : ∀ d, 1 ≤ c d)
    (hcr : ∀ d, c (N.toRot.rev d) = c d) (hlam : ∀ x, lam x = c x.1.1)
    (L : C.Live (Nat.cast ∘ c) Γ) (hS : Γ ⊆ S.Γ) {t : ℕ}
    (hz : ∀ w ∈ S.Γ, w ∉ Γ → ∀ p, ¬ (N.toRot.dual.double.split Γ).IsWalk
      ((N.toRot.dual.double.split Γ).tail (L.κ0 t)) p ((N.toRot.dual.double.split Γ).tail w))
    (h1 : L.xa ≤ t) (h2 : L.ya ≤ t) (h3 : t ≤ L.xb) (h4 : t ≤ L.yb)
    (ψ : Fin (n * (n * 21)) → ℕ∞) (r : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) ψ r)
    {u v : S.hRot.Vertex} {k iy ia : ℕ} (hya : iy ≤ ia) (hak : ia ≤ k)
    (hs : Net.ParSteps r ((S.levelPad hN).ι (.inl v)) k)
    (hroot : (Net.parOf r)^[k] ((S.levelPad hN).ι (.inl v)) = (S.levelPad hN).ι (.inl u))
    (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)) (hv : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v))
    (hpu : S.pieceOf ⟨S.vcopy u, hu⟩ = S.pieceAt (L.κ0 t))
    (hpv : S.pieceOf ⟨S.vcopy v, hv⟩ = S.pieceAt (L.κ1 t))
    (hlt : ((∑ l ∈ Finset.range k, S.levelLen hN lam M ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
      ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) : ℕ∞) : ℝ≥0∞) < M)
    (hle : ((∑ l ∈ Finset.range k, S.levelLen hN lam M ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
      ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) : ℕ∞) : ℝ≥0∞) ≤ C.lamD (Nat.cast ∘ c) t)
    (xa xb : S.Tok)
    (hxa : S.IsEnd xa.1 (S.copyAt hN ((Net.parOf r)^[ia] ((S.levelPad hN).ι (.inl v)))))
    (hxb : S.IsEnd xb.1 (S.copyAt hN ((Net.parOf r)^[iy] ((S.levelPad hN).ι (.inl v)))))
    (hs0 : C.atCopy Γ 0 ((N.toRot.dual.double.split Γ).tail (N.toRot.tokDart xa.1)))
    (hs1 : C.atCopy Γ 1 ((N.toRot.dual.double.split Γ).tail (N.toRot.tokDart xb.1)))
    (hF0 : ∀ l < ia, ∀ x, S.edgeTok hN ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
      ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) = some x →
      ¬ C.atCopy Γ 0 ((N.toRot.dual.double.split Γ).head (N.toRot.tokDart x.1)))
    (hF1 : ∀ l, iy ≤ l → l < ia → ∀ x, S.edgeTok hN ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
      ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) = some x →
      ¬ C.atCopy Γ 1 ((N.toRot.dual.double.split Γ).tail (N.toRot.tokDart x.1))) :
    ∃ St : L.Step, (∀ z, z ∈ (List.range St.n).map St.q ↔ ∃ l, iy ≤ l ∧ l < ia ∧ ∃ x,
      S.edgeTok hN ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
        ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) = some x ∧ z = N.toRot.tokDart x.1) ∧
      (List.range St.n).map St.q = S.chainDarts hN r ((S.levelPad hN).ι (.inl v)) iy (ia - iy) := by
  have H3 := hr.chain_seg ((S.levelPad hN).ι (.inl v)) hs iy 0 (by omega)
  rw [Nat.zero_add] at H3
  have H2 := hr.chain_seg ((S.levelPad hN).ι (.inl v)) hs (ia - iy) iy (by omega)
  rw [Nat.add_sub_of_le hya] at H2
  have H1 := hr.chain_seg ((S.levelPad hN).ι (.inl v)) hs (k - ia) ia (by omega)
  rw [Nat.add_sub_of_le hak, hroot] at H1
  obtain ⟨q₃, a₃, -, w₃, -⟩ := H3
  obtain ⟨q₂, a₂, e₂, w₂, f₂⟩ := H2
  obtain ⟨q₁, -, -, w₁, -⟩ := H1
  have hW : (q₁.append (q₂.append q₃)).wt (lenTop (S.levelLen hN lam M)) =
      ((∑ l ∈ Finset.range k, S.levelLen hN lam M ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
        ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) : ℕ∞) : ℝ≥0∞) := by
    rw [SsspFlow.Walk.wt_append, SsspFlow.Walk.wt_append, w₁, w₂, w₃, ← ENat.toENNReal_add,
      ← ENat.toENNReal_add, add_comm (∑ l ∈ Finset.Ico iy ia, _), Finset.sum_Ico_consecutive _ (Nat.zero_le _) hya,
      add_comm, Finset.sum_Ico_consecutive _ (Nat.zero_le _) hak, Finset.range_eq_Ico]
  obtain ⟨St, hSt⟩ := S.level_step_of_split hN lam M hR hC c hc1 hcr hlam L hS hz h1 h2 h3 h4 q₁ q₂ q₃
    (hW ▸ hlt) hu hv hpu hpv (hW ▸ hle) xa xb hxa hxb hs0 hs1
    (fun z hz => by
      rcases List.mem_append.1 hz with hz | hz
      · obtain ⟨y, y', x, ⟨l, hl1, hl2, rfl, rfl⟩, he, rfl⟩ := S.levelDarts_sub hN q₂ a₂ z hz
        exact hF0 l hl2 x he
      · obtain ⟨y, y', x, ⟨l, -, hl2, rfl, rfl⟩, he, rfl⟩ := S.levelDarts_sub hN q₃ a₃ z hz
        exact hF0 l (by omega) x he)
    (fun z hz => by
      obtain ⟨y, y', x, ⟨l, hl1, hl2, rfl, rfl⟩, he, rfl⟩ := S.levelDarts_sub hN q₂ a₂ z hz
      exact hF1 l hl1 hl2 x he)
  refine ⟨St, fun z => ?_, by rw [hSt, S.levelDarts_eq_edgeFlat, f₂]; rfl⟩
  rw [hSt]
  constructor
  · intro hz
    obtain ⟨y, y', x, ⟨l, hl1, hl2, rfl, rfl⟩, he, rfl⟩ := S.levelDarts_sub hN q₂ a₂ z hz
    exact ⟨l, hl1, hl2, x, he, rfl⟩
  · rintro ⟨l, hl1, hl2, x, he, rfl⟩
    exact S.levelDarts_of_hasEdge hN he q₂ (e₂ l hl1 hl2)

end RData

end RotSystem

end SsspFlow
