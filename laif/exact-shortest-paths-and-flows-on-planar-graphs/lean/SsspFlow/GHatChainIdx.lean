import SsspFlow.GHatChainStep
import SsspFlow.GHatLevelIdx
import SsspFlow.GHatLevelMinIdx

/-!
# The indices of the cut path on the darts of a chain

The darts of the parent steps of the chain of a target, from its root down (`RData.chainDarts`), are
the darts of the walk down the chain. When the root lies at the piece at `κ0(t)` and the target at the
piece at `κ1(t)`, with sum of lengths below `M` and at most `λ_t`, they form a shortest walk of the
annulus, and its indices on the cut path are read at the copies of the nodes of the chain, exactly as
for the walk of `RData.level_chain_idx`.

* `Walk.support_eq_edgeFlat`: the nodes of a walk are the tails of its edges, then its end.
* `RData.chain_darts_idx`: the darts of the chain of a target form a shortest walk of the annulus
  whose indices on the cut path are the indices at the pieces of the copies of the nodes of the chain.
* `RData.chain_data`: the chain of a target reaches a root at the piece at `κ0(t)`, and its darts form
  such a walk.
* `RData.chain_least_greatest`: the least and the greatest index of `RData.level_least_greatest` are
  the least and the greatest index of the darts of the chain of the target.
-/

set_option autoImplicit false

namespace SsspFlow

/-- The nodes of a walk are the tails of its edges, in order, then its end. -/
theorem Walk.support_eq_edgeFlat {V : Type} {adj : V → V → Prop} :
    ∀ {a b : V} (p : SsspFlow.Walk adj a b), p.support = p.edgeFlat (fun y _ => [y]) ++ [b]
  | _, _, .nil _ => rfl
  | a, _, .cons _ p => by
    show a :: p.support = _
    rw [Walk.support_eq_edgeFlat p]
    rfl

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ)

/-- **The darts of a chain are a shortest walk of the annulus.** For token lengths that are the costs
`c` of their darts, with `c` equal on the two darts of an edge and giving `g`, and corners of `S` that
hold those of a live annulus, the others out of its reach: let an output `r` of the oracle on the
network of a level meet its specification, and let the chain of the copy node of `v`, at the piece at
`κ1(t)`, take `k` valid parent steps to a root at the copy node of `u`, at the piece at `κ0(t)`, with
sum of lengths below `M` and at most `λ_t`. Then the darts of the chain form a shortest walk of the
annulus, and an index `r' ≤ m` is an index of it on the cut path exactly when some corner `p_{r'}^σ`
lies, in the cut along the path, at the vertex of the piece of the copy of a node of the chain. -/
theorem chain_darts_idx {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞}
    {Γ : Finset (N.G.Dart × Bool)} (c : N.G.Dart → ℕ) (hcr : ∀ d, c (N.toRot.rev d) = c d)
    (hlam : ∀ x, lam x = c x.1.1) (hgc : ∀ d, g d = c d) (L : C.Live g Γ) (hS : Γ ⊆ S.Γ) {t : ℕ}
    (hz : ∀ w ∈ S.Γ, w ∉ Γ → ∀ p, ¬ (N.toRot.dual.double.split Γ).IsWalk
      ((N.toRot.dual.double.split Γ).tail (L.κ0 t)) p ((N.toRot.dual.double.split Γ).tail w))
    (h1 : L.xa ≤ t) (h2 : L.ya ≤ t) (h3 : t ≤ L.xb) (h4 : t ≤ L.yb)
    (ψ : Fin (n * (n * 21)) → ℕ∞) (r : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) ψ r)
    {u v : S.hRot.Vertex} {k : ℕ} (hs : Net.ParSteps r ((S.levelPad hN).ι (.inl v)) k)
    (hroot : (Net.parOf r)^[k] ((S.levelPad hN).ι (.inl v)) = (S.levelPad hN).ι (.inl u))
    (hnone : (r ((S.levelPad hN).ι (.inl u))).2 = none)
    (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)) (hv : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v))
    (hpu : S.pieceOf ⟨S.vcopy u, hu⟩ = S.pieceAt (L.κ0 t))
    (hpv : S.pieceOf ⟨S.vcopy v, hv⟩ = S.pieceAt (L.κ1 t))
    (hlt : ((∑ l ∈ Finset.range k, S.levelLen hN lam M ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
      ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) : ℕ∞) : ℝ≥0∞) < M)
    (hle : ((∑ l ∈ Finset.range k, S.levelLen hN lam M ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
      ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) : ℕ∞) : ℝ≥0∞) ≤ C.lamD g t) :
    L.Shortest t (S.chainDarts hN r ((S.levelPad hN).ι (.inl v)) 0 k) ∧
      (∀ r', r' ∈ C.idx (L.κ0 t) (S.chainDarts hN r ((S.levelPad hN).ι (.inl v)) 0 k) ↔
        r' ≤ C.m ∧ ∃ σ, ∃ y, (∃ i, (Net.parOf r)^[i] ((S.levelPad hN).ι (.inl v)) = y) ∧
          ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)), ∃ z,
            S.dualSplit.tail z = S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) ∧
            C.cut.tail z = C.cut.tail (C.k σ r')) ∧
      ∀ w, (w = S.dualSplit.tail (L.κ0 t) ∨ ∃ y ∈ S.chainDarts hN r ((S.levelPad hN).ι (.inl v)) 0 k,
          S.dualSplit.head y = w) ↔
        ∃ y, (∃ i, (Net.parOf r)^[i] ((S.levelPad hN).ι (.inl v)) = y) ∧
          ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)), S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) = w := by
  obtain ⟨Q, -, -, hQw, hQf⟩ := hr.chain_seg ((S.levelPad hN).ι (.inl v)) hs k 0 (by omega)
  have hD : S.levelDarts hN Q = S.chainDarts hN r ((S.levelPad hN).ι (.inl v)) 0 k := by
    rw [levelDarts_eq_edgeFlat, hQf]
    rfl
  -- past the root the chain stays there
  have hfix : ∀ i, k ≤ i → (Net.parOf r)^[i] ((S.levelPad hN).ι (.inl v)) =
      (Net.parOf r)^[k] ((S.levelPad hN).ι (.inl v)) := fun i hi => by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    have hfx : Net.parOf r ((S.levelPad hN).ι (.inl u)) = (S.levelPad hN).ι (.inl u) := by
      simp [Net.parOf, hnone]
    rw [Nat.add_comm, Function.iterate_add_apply, hroot, Function.iterate_fixed hfx]
  have hsupp : ∀ y, y ∈ Q.support ↔ ∃ i, (Net.parOf r)^[i] ((S.levelPad hN).ι (.inl v)) = y := by
    intro y
    rw [Walk.support_eq_edgeFlat, hQf]
    simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_reverse, List.mem_range,
      List.mem_singleton, Nat.zero_add]
    constructor
    · rintro (⟨_, ⟨l, -, rfl⟩, h⟩ | rfl)
      · exact ⟨_, (List.mem_singleton.1 h).symm⟩
      · exact ⟨0, rfl⟩
    · rintro ⟨i, rfl⟩
      have e : (Net.parOf r)^[i] ((S.levelPad hN).ι (.inl v)) =
          (Net.parOf r)^[min i k] ((S.levelPad hN).ι (.inl v)) := by
        rcases le_total i k with h | h
        · rw [min_eq_left h]
        · rw [min_eq_right h, hfix i h]
      rw [e]
      rcases Nat.eq_zero_or_pos (min i k) with h0 | h0
      · exact .inr (by rw [h0])
      · exact .inl ⟨_, ⟨min i k - 1, by omega, rfl⟩, by rw [Nat.sub_add_cancel h0]; exact List.mem_singleton.2 rfl⟩
  have key : ∀ {a : Fin (n * (n * 21))} (Q : SsspFlow.Walk (S.levelNet hN).G.Adj a ((S.levelPad hN).ι (.inl v))),
      a = (S.levelPad hN).ι (.inl u) →
      S.levelDarts hN Q = S.chainDarts hN r ((S.levelPad hN).ι (.inl v)) 0 k →
      (∀ y, y ∈ Q.support ↔ ∃ i, (Net.parOf r)^[i] ((S.levelPad hN).ι (.inl v)) = y) →
      Q.wt (lenTop (S.levelLen hN lam M)) =
        ((∑ l ∈ Finset.range k, S.levelLen hN lam M ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
          ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) : ℕ∞) : ℝ≥0∞) →
      L.Shortest t (S.chainDarts hN r ((S.levelPad hN).ι (.inl v)) 0 k) ∧
      (∀ r', r' ∈ C.idx (L.κ0 t) (S.chainDarts hN r ((S.levelPad hN).ι (.inl v)) 0 k) ↔
        r' ≤ C.m ∧ ∃ σ, ∃ y, (∃ i, (Net.parOf r)^[i] ((S.levelPad hN).ι (.inl v)) = y) ∧
          ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)), ∃ z,
            S.dualSplit.tail z = S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) ∧
            C.cut.tail z = C.cut.tail (C.k σ r')) ∧
      ∀ w, (w = S.dualSplit.tail (L.κ0 t) ∨ ∃ y ∈ S.chainDarts hN r ((S.levelPad hN).ι (.inl v)) 0 k,
          S.dualSplit.head y = w) ↔
        ∃ y, (∃ i, (Net.parOf r)^[i] ((S.levelPad hN).ι (.inl v)) = y) ∧
          ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)), S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) = w := by
    intro a Q ha hD hsupp hw
    subst ha
    have hp : Q.wt (lenTop (S.levelLen hN lam M)) < M := hw ▸ hlt
    have hz₁ : ∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN ((S.levelPad hN).ι (.inl u))) := by
      rw [S.copyAt_ι]; exact hu
    have hz₂ : ∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN ((S.levelPad hN).ι (.inl v))) := by
      rw [S.copyAt_ι]; exact hv
    have e₁ : S.pieceOf ⟨_, hz₁⟩ = S.pieceOf ⟨S.vcopy u, hu⟩ :=
      congrArg S.pieceOf (Subtype.ext (S.copyAt_ι hN _))
    obtain ⟨-, -, hvis⟩ := S.levelDarts_walk hN lam M c hcr hlam Q hz₁ hz₂ hp
    rw [e₁, hpu, S.vertexEquiv_pieceAt] at hvis
    have hsub : C.Γ ⊆ S.Γ := L.sub.trans hS
    rw [← hD]
    refine ⟨(S.level_shortest_darts hN lam M c hcr hlam hgc L hS hz h1 h2 h3 h4 Q hp hu hv hpu hpv
      (hw ▸ hle)).1, fun r' => ?_, fun w => (hvis w).trans
        ⟨fun ⟨y, hy, hcy, h⟩ => ⟨y, (hsupp y).1 hy, hcy, h⟩, fun ⟨y, hy, hcy, h⟩ => ⟨y, (hsupp y).2 hy, hcy, h⟩⟩⟩
    show (r' ≤ C.m ∧ ∃ σ, _) ↔ _
    refine and_congr_right fun _ => exists_congr fun σ => ?_
    constructor
    · rintro (h | ⟨y', hy', h⟩)
      · obtain ⟨y, hy, hcy, hw'⟩ := (hvis _).1 (.inl rfl)
        exact ⟨y, (hsupp y).1 hy, hcy, L.κ0 t, hw'.symm, h.symm⟩
      · obtain ⟨y, hy, hcy, hw'⟩ := (hvis _).1 (.inr ⟨y', hy', rfl⟩)
        exact ⟨y, (hsupp y).1 hy, hcy, N.toRot.dual.double.rev y', hw'.symm, h⟩
    · rintro ⟨y, hy, hcy, z, hz1, hz2⟩
      rcases (hvis _).2 ⟨y, (hsupp y).2 hy, hcy, hz1.symm⟩ with h | ⟨y', hy', h⟩
      · exact .inl (hz2.symm.trans (S.cut_tail_of_split hsub h))
      · exact .inr ⟨y', hy', (S.cut_tail_of_split hsub h).trans hz2⟩
  exact key Q (by rw [Nat.zero_add]; exact hroot) hD hsupp
    (hQw.trans (by rw [Nat.zero_add, Finset.range_eq_Ico]))

/-- **The chain of a target.** Under the conditions of `RData.level_chain_idx`, the chain of the
target takes `k` valid parent steps to a root at the copy node of a vertex `u` at the piece at
`κ0(t)`, with sum of lengths the distance of the target, and the darts of the chain form a shortest
walk of the annulus whose indices on the cut path are read at the copies of the nodes of the chain. -/
theorem chain_data {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞}
    {Γ : Finset (N.G.Dart × Bool)} (c : N.G.Dart → ℕ) (hcr : ∀ d, c (N.toRot.rev d) = c d)
    (hlam : ∀ x, lam x = c x.1.1) (hgc : ∀ d, g d = c d) (L : C.Live g Γ) (hS : Γ ⊆ S.Γ) {t : ℕ}
    (hz : ∀ w ∈ S.Γ, w ∉ Γ → ∀ p, ¬ (N.toRot.dual.double.split Γ).IsWalk
      ((N.toRot.dual.double.split Γ).tail (L.κ0 t)) p ((N.toRot.dual.double.split Γ).tail w))
    (h1 : L.xa ≤ t) (h2 : L.ya ≤ t) (h3 : t ≤ L.xb) (h4 : t ≤ L.yb)
    (ψ : Fin (n * (n * 21)) → ℕ∞) (r : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) ψ r) {v : S.hRot.Vertex}
    (hv : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v)) (hpv : S.pieceOf ⟨S.vcopy v, hv⟩ = S.pieceAt (L.κ1 t))
    (hroot : ∀ z, ψ z ≠ ⊤ → ψ z = 0 ∧ ∃ u, z = (S.levelPad hN).ι (.inl u) ∧
      ∃ hu : (∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
        S.pieceOf ⟨S.vcopy u, hu⟩ = S.pieceAt (L.κ0 t) ∨
          (M : ℝ≥0∞) ≤ S.arcDist lam M (S.vcopy u) (S.vcopy v))
    (hlt : ((r ((S.levelPad hN).ι (.inl v))).1 : ℝ≥0∞) < M)
    (hle : ((r ((S.levelPad hN).ι (.inl v))).1 : ℝ≥0∞) ≤ C.lamD g t) :
    ∃ (k : ℕ) (u : S.hRot.Vertex) (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
      Net.ParSteps r ((S.levelPad hN).ι (.inl v)) k ∧
      (Net.parOf r)^[k] ((S.levelPad hN).ι (.inl v)) = (S.levelPad hN).ι (.inl u) ∧
      (r ((S.levelPad hN).ι (.inl u))).2 = none ∧ S.pieceOf ⟨S.vcopy u, hu⟩ = S.pieceAt (L.κ0 t) ∧
      ((∑ l ∈ Finset.range k, S.levelLen hN lam M ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
        ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) : ℕ∞) : ℝ≥0∞) =
        ((r ((S.levelPad hN).ι (.inl v))).1 : ℝ≥0∞) ∧
      L.Shortest t (S.chainDarts hN r ((S.levelPad hN).ι (.inl v)) 0 k) ∧
      (∀ r', r' ∈ C.idx (L.κ0 t) (S.chainDarts hN r ((S.levelPad hN).ι (.inl v)) 0 k) ↔
        r' ≤ C.m ∧ ∃ σ, ∃ y, (∃ i, (Net.parOf r)^[i] ((S.levelPad hN).ι (.inl v)) = y) ∧
          ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)), ∃ z,
            S.dualSplit.tail z = S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) ∧
            C.cut.tail z = C.cut.tail (C.k σ r')) ∧
      ∀ w, (w = S.dualSplit.tail (L.κ0 t) ∨ ∃ y ∈ S.chainDarts hN r ((S.levelPad hN).ι (.inl v)) 0 k,
          S.dualSplit.head y = w) ↔
        ∃ y, (∃ i, (Net.parOf r)^[i] ((S.levelPad hN).ι (.inl v)) = y) ∧
          ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)), S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) = w := by
  have hfin : (r ((S.levelPad hN).ι (.inl v))).1 ≠ ⊤ := fun e => by simp [e] at hlt
  obtain ⟨k, hk0, -, hstep, hsumk⟩ := hr.chain _ hfin
  have hs : Net.ParSteps r ((S.levelPad hN).ι (.inl v)) k := fun i hi => (hstep i hi).1
  have hρ : ψ ((Net.parOf r)^[k] ((S.levelPad hN).ι (.inl v))) ≠ ⊤ := fun e => by
    rw [e, top_add] at hsumk
    exact hfin hsumk.symm
  obtain ⟨h0, u, hρu, hu, hcase⟩ := hroot _ hρ
  rw [h0, zero_add] at hsumk
  have hsumR : ((∑ l ∈ Finset.range k, S.levelLen hN lam M ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
      ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) : ℕ∞) : ℝ≥0∞) =
      ((r ((S.levelPad hN).ι (.inl v))).1 : ℝ≥0∞) := by rw [hsumk]
  have hlt' : ((∑ l ∈ Finset.range k, S.levelLen hN lam M ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
      ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) : ℕ∞) : ℝ≥0∞) < M := by rw [hsumR]; exact hlt
  -- a walk of length below `M` joins the copies of `u` and `v`, so the root lies at the piece at `κ0(t)`
  have hpu : S.pieceOf ⟨S.vcopy u, hu⟩ = S.pieceAt (L.κ0 t) := by
    refine hcase.resolve_right fun harc => ?_
    have aux : ∀ {a : Fin (n * (n * 21))} (p : SsspFlow.Walk (S.levelNet hN).G.Adj a ((S.levelPad hN).ι (.inl v))),
        a = (S.levelPad hN).ι (.inl u) → p.wt (lenTop (S.levelLen hN lam M)) < M → False := by
      intro a p ha hp
      subst ha
      obtain ⟨q, hq, -⟩ := S.walk_project hN lam M p (ne_top_of_lt hp)
      have harc' : (M : ℝ≥0∞) ≤ S.arcDist lam M (S.copyAt hN ((S.levelPad hN).ι (.inl u)))
          (S.copyAt hN ((S.levelPad hN).ι (.inl v))) := by
        rw [S.copyAt_ι, S.copyAt_ι]
        exact harc
      have : S.arcDist lam M (S.copyAt hN ((S.levelPad hN).ι (.inl u)))
          (S.copyAt hN ((S.levelPad hN).ι (.inl v))) ≤ p.wt (lenTop (S.levelLen hN lam M)) := by
        rw [← hq]
        exact iInf_le _ q
      exact absurd (harc'.trans this) (not_le.2 hp)
    obtain ⟨Q, -, -, hQw, -⟩ := hr.chain_seg ((S.levelPad hN).ι (.inl v)) hs k 0 (by omega)
    exact aux Q (by rw [Nat.zero_add]; exact hρu)
      ((hQw.trans (by rw [Nat.zero_add, Finset.range_eq_Ico])).trans_lt hlt')
  have hnone : (r ((S.levelPad hN).ι (.inl u))).2 = none := by rw [← hρu]; exact hk0
  obtain ⟨hsh, hidx', hvis⟩ := S.chain_darts_idx hN lam M c hcr hlam hgc L hS hz h1 h2 h3 h4 ψ r hr hs hρu hnone
    hu hv hpu hpv hlt' (by rw [hsumR]; exact hle)
  exact ⟨k, u, hu, hs, hρu, hnone, hpu, hsumR, hsh, hidx', hvis⟩

/-- **The least and the greatest index on the darts of a chain.** Under the conditions of
`RData.level_least_greatest`, the chain of the target takes `k` valid parent steps to a root at the
copy node of a vertex `u` at the piece at `κ0(t)`, with sum of lengths the distance of the target. The
darts of the chain form a shortest walk of the annulus, its least index on the cut path is the least
`ix`, and its greatest index is `m` minus the least `jx`, over the flagged copies of the component of
the target. -/
theorem chain_least_greatest {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞}
    {Γ : Finset (N.G.Dart × Bool)} (c : N.G.Dart → ℕ) (hcr : ∀ d, c (N.toRot.rev d) = c d)
    (hlam : ∀ x, lam x = c x.1.1) (hgc : ∀ d, g d = c d) (L : C.Live g Γ) (hS : Γ ⊆ S.Γ) {t : ℕ}
    (hz : ∀ w ∈ S.Γ, w ∉ Γ → ∀ p, ¬ (N.toRot.dual.double.split Γ).IsWalk
      ((N.toRot.dual.double.split Γ).tail (L.κ0 t)) p ((N.toRot.dual.double.split Γ).tail w))
    (h1 : L.xa ≤ t) (h2 : L.ya ≤ t) (h3 : t ≤ L.xb) (h4 : t ≤ L.yb)
    (ψ : Fin (n * (n * 21)) → ℕ∞) (r : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) ψ r) {v : S.hRot.Vertex}
    (hv : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v)) (hpv : S.pieceOf ⟨S.vcopy v, hv⟩ = S.pieceAt (L.κ1 t))
    (hroot : ∀ z, ψ z ≠ ⊤ → ψ z = 0 ∧ ∃ u, z = (S.levelPad hN).ι (.inl u) ∧
      ∃ hu : (∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
        S.pieceOf ⟨S.vcopy u, hu⟩ = S.pieceAt (L.κ0 t) ∨
          (M : ℝ≥0∞) ≤ S.arcDist lam M (S.vcopy u) (S.vcopy v))
    (hle : ((r ((S.levelPad hN).ι (.inl v))).1 : ℝ≥0∞) ≤ C.lamD g t)
    (isT : Fin (n * (n * 21)) → Bool)
    (hT : ∀ t', isT t' = true → ((r t').1 : ℝ≥0∞) < M ∧ ∃ v', t' = (S.levelPad hN).ι (.inl v') ∧
      ∃ _ : (∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v')),
        (Relation.ReflTransGen S.ERC (S.vcopy v') (S.vcopy v) → v' = v))
    (hTv : isT ((S.levelPad hN).ι (.inl v)) = true)
    (fl : S.hRot.Vertex → Prop)
    (hfl : ∀ u, fl u ↔ ∃ y, (∃ t' i, isT t' = true ∧ (Net.parOf r)^[i] t' = y) ∧ S.copyAt hN y = S.vcopy u)
    (ix jx : S.hRot.Vertex → ℕ∞)
    (hix : ∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
      ix u = ⨅ r' ∈ S.cutIdx C ⟨S.vcopy u, hu⟩, (r' : ℕ∞))
    (hjx : ∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
      jx u = ⨅ r' ∈ S.cutIdx C ⟨S.vcopy u, hu⟩, ((C.m - r' : ℕ) : ℕ∞)) :
    ∃ (k : ℕ) (u : S.hRot.Vertex) (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)) (i1 i2 : ℕ),
      Net.ParSteps r ((S.levelPad hN).ι (.inl v)) k ∧
      (Net.parOf r)^[k] ((S.levelPad hN).ι (.inl v)) = (S.levelPad hN).ι (.inl u) ∧
      (r ((S.levelPad hN).ι (.inl u))).2 = none ∧ S.pieceOf ⟨S.vcopy u, hu⟩ = S.pieceAt (L.κ0 t) ∧
      ((∑ l ∈ Finset.range k, S.levelLen hN lam M ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
        ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) : ℕ∞) : ℝ≥0∞) =
        ((r ((S.levelPad hN).ι (.inl v))).1 : ℝ≥0∞) ∧
      L.Shortest t (S.chainDarts hN r ((S.levelPad hN).ι (.inl v)) 0 k) ∧
      IsLeast (C.idx (L.κ0 t) (S.chainDarts hN r ((S.levelPad hN).ι (.inl v)) 0 k)) i1 ∧
      IsGreatest (C.idx (L.κ0 t) (S.chainDarts hN r ((S.levelPad hN).ι (.inl v)) 0 k)) i2 ∧
      (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy v)), ⨅ (_ : fl u), ix u) = i1 ∧
      (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy v)), ⨅ (_ : fl u), jx u) =
        (C.m - i2 : ℕ) := by
  obtain ⟨ps, i1, i2, -, -, hl, hg, e1, e2, hidx⟩ := S.level_least_greatest hN lam M c hcr hlam hgc L hS
    hz h1 h2 h3 h4 ψ r hr hv hpv hroot hle isT hT hTv fl hfl ix jx hix hjx
  obtain ⟨k, u, hu, hs, hρu, hnone, hpu, hsumR, hsh, hidx', -⟩ := S.chain_data hN lam M c hcr hlam hgc L hS
    hz h1 h2 h3 h4 ψ r hr hv hpv hroot (hT _ hTv).1 hle
  have hE : C.idx (L.κ0 t) (S.chainDarts hN r ((S.levelPad hN).ι (.inl v)) 0 k) = C.idx (L.κ0 t) ps :=
    Set.ext fun r' => (hidx' r').trans (hidx r').symm
  exact ⟨k, u, hu, i1, i2, hs, hρu, hnone, hpu, hsumR, hsh, hE ▸ hl, hE ▸ hg, e1, e2⟩

end RData

end RotSystem

end SsspFlow
