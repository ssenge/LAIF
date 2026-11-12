import SsspFlow.GHatLevelChain

/-!
# The least index of the cut path on the walk of an annulus

The marking run marks the parent chains of the targets. A copy is flagged when a marked node has it
as its copy, and carries the least value `f r` over the indices `r` of the cut path at the vertex of
its piece (`RData.cutIdx`). When every target of distance below `M` is the only target of its
component of `Ĝ_ℓ[E_R ∪ E_C]`, the least such value over the flagged copies of the component of a
target is the least value of `f` over the indices of the shortest walk of the annulus that the chain
of the target gives. With `f r = r` this is the least index of the walk, with `f r = m - r` it gives
the greatest index.

* `RData.erc_of_walk`: a walk of `Ĝ_ℓ` of length below `M` runs in one component of
  `Ĝ_ℓ[E_R ∪ E_C]`, through copies on E_R edges when it ends at one.
* `RData.erc_symm`: the components of `Ĝ_ℓ[E_R ∪ E_C]` are symmetric.
* `RData.exists_vcopy`: every node of the network of a level has the copy of a vertex as its copy.
* `RData.chain_erc`: the copies of the nodes of the parent chain of a target of distance below `M`
  lie in the component of the target.
* `RData.level_min_idx`: the least value over the flagged copies of the component of a target is
  the least value of `f` over the indices of the shortest walk of the annulus.
* `Nat.iInf_isLeast`, `Nat.iInf_sub_isGreatest`: the least value of `r` and of `m - r` over a nonempty
  set of indices `r ≤ m` give its least and its greatest element.
* `RData.level_least_greatest`: the least and the greatest index on the cut path of the shortest walk
  of the annulus, from the least values of `r` and of `m - r` over the flagged copies.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

section Gen

variable {E : Type} [Fintype E] [DecidableEq E] {G : RotSystem E} (S : G.RData)

/-- The indices `r ≤ m` of the corners `p_r^σ` that lie, in the cut along `C`, at the vertex of
the piece of a copy on E_R edges. -/
def cutIdx (C : G.dual.CutPath) (a : S.EndCopy) : Set ℕ :=
  {r | r ≤ C.m ∧ ∃ σ, ∃ z, S.dualSplit.tail z = S.vertexEquiv (S.pieceOf a) ∧
    C.cut.tail z = C.cut.tail (C.k σ r)}

variable (lam : S.Tok → ℕ) (M : ℕ)

theorem arc_erc {a b : Copy G.Vertex E} (e : S.Arc a b) (h : S.arcW lam M a b e < M) :
    S.ERC a b ∧ ∃ x : S.Tok, S.IsEnd x.1 a := by
  cases e with
  | er x => exact ⟨.inl ⟨x, .inl ⟨rfl, rfl⟩⟩, x, .inl rfl⟩
  | er' x => exact ⟨.inl ⟨x, .inr ⟨rfl, rfl⟩⟩, x, .inr rfl⟩
  | ec x => exact ⟨.inr ⟨x, rfl, rfl⟩, x, S.isEnd_att x.1⟩
  | es _ => exact absurd h (lt_irrefl _)
  | es' _ => exact absurd h (lt_irrefl _)

/-- **Short walks stay in a component.** A walk of `Ĝ_ℓ` of length below `M` runs in one component
of `Ĝ_ℓ[E_R ∪ E_C]`, through copies on E_R edges when it ends at one. -/
theorem erc_of_walk : ∀ {a b : Copy G.Vertex E} (q : FaceDisjoint.Walk S.Arc a b), S.awt lam M q < M →
    ∀ c ∈ q.support, Relation.ReflTransGen S.ERC c b ∧
      ((∃ x : S.Tok, S.IsEnd x.1 b) → ∃ x : S.Tok, S.IsEnd x.1 c)
  | _, _, .nil _, _ => fun c hc => by
    rw [FaceDisjoint.Walk.support_nil, List.mem_singleton] at hc
    subst hc
    exact ⟨.refl, id⟩
  | _, _, .cons e q, h => fun c hc => by
    have h' : S.arcW lam M _ _ e + S.awt lam M q < M := h
    have hq : S.awt lam M q < M := by omega
    obtain ⟨hs, hend⟩ := S.arc_erc lam M e (by omega)
    rw [FaceDisjoint.Walk.support_cons, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨.head hs (erc_of_walk q hq _ q.start_mem).1, fun _ => hend⟩
    · exact erc_of_walk q hq c hc

theorem erc_symm {a b : Copy G.Vertex E} (h : Relation.ReflTransGen S.ERC a b) :
    Relation.ReflTransGen S.ERC b a := by
  have h0 : Relation.ReflTransGen (S.ZR (fun _ => 0)) a b := by rw [zr_zero]; exact h
  have := S.rtg_symm (fun _ => 0) (fun _ => rfl) h0
  rwa [zr_zero] at this

end Gen

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ) {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞}
  {Γ : Finset (N.G.Dart × Bool)}

theorem exists_vcopy (z : Fin (n * (n * 21))) : ∃ u, S.copyAt hN z = S.vcopy u := by
  unfold copyAt
  generalize (S.levelPad hN).back z = x
  rcases x with u | d
  · exact ⟨u, rfl⟩
  · exact ⟨S.hRot.tail d, (S.vcopy_tail d).symm⟩

/-- **Chains stay in the component of their target.** For an output of the oracle on the network of
a level, the copies of the nodes of the parent chain of a target of distance below `M` lie in the
component of `Ĝ_ℓ[E_R ∪ E_C]` of the target, on E_R edges when the target is. -/
theorem chain_erc (ψ : Fin (n * (n * 21)) → ℕ∞) (r : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) ψ r) {w : S.hRot.Vertex}
    (hlt : ((r ((S.levelPad hN).ι (.inl w))).1 : ℝ≥0∞) < M) {y : Fin (n * (n * 21))}
    (hy : ∃ i, (Net.parOf r)^[i] ((S.levelPad hN).ι (.inl w)) = y) :
    Relation.ReflTransGen S.ERC (S.copyAt hN y) (S.vcopy w) ∧
      ((∃ x : S.Tok, S.IsEnd x.1 (S.vcopy w)) → ∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)) := by
  have hfin : (r ((S.levelPad hN).ι (.inl w))).1 ≠ ⊤ := fun e => by simp [e] at hlt
  obtain ⟨k, p, -, -, hwt, hsupp⟩ := hr.chain_walk _ hfin
  have hpM : p.wt (lenTop (S.levelLen hN lam M)) < M :=
    lt_of_le_of_lt (hwt ▸ le_add_self) hlt
  obtain ⟨q, hq, -, hs'⟩ := S.walk_project_supp hN lam M p (ne_top_of_lt hpM)
  have hqM : S.awt lam M q < M := by
    have : ((S.awt lam M q : ℕ) : ℝ≥0∞) < M := hq ▸ hpM
    exact_mod_cast this
  have h := S.erc_of_walk lam M q hqM (S.copyAt hN y) (hs' y ((hsupp y).2 hy))
  rw [S.copyAt_ι] at h
  exact h

/-- **The least value on the walk of an annulus.** Under the conditions of `RData.level_chain_idx`,
let the targets `isT` have distance below `M`, each the only target of its component of
`Ĝ_ℓ[E_R ∪ E_C]`, with the copy at `v` a target. Let a copy be flagged when a node of the parent
chain of a target has it as its copy, and let `ix` give the least value of `f` over the indices of
the cut path at the piece of a copy. Then there is a shortest walk of the annulus of the length of
the distance of the target whose least value of `f` over its indices on the cut path is the least
`ix` over the flagged copies of the component of the target. -/
theorem level_min_idx (c : N.G.Dart → ℕ) (hcr : ∀ d, c (N.toRot.rev d) = c d)
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
    (f : ℕ → ℕ∞) (ix : S.hRot.Vertex → ℕ∞)
    (hix : ∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)), ix u = ⨅ r' ∈ S.cutIdx C ⟨S.vcopy u, hu⟩, f r') :
    ∃ ps : List (N.G.Dart × Bool), L.Shortest t ps ∧
      (ps.map (g ∘ Prod.fst)).sum = ((r ((S.levelPad hN).ι (.inl v))).1 : ℝ≥0∞) ∧
      (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy v)), ⨅ (_ : fl u), ix u) =
        ⨅ r' ∈ C.idx (L.κ0 t) ps, f r' := by
  have hlt := (hT _ hTv).1
  obtain ⟨ps, hps, hsum, hidx⟩ := S.level_chain_idx hN lam M c hcr hlam hgc L hS hz h1 h2 h3 h4 ψ r hr hv
    hpv hroot hlt hle
  refine ⟨ps, hps, hsum, le_antisymm ?_ ?_⟩
  · refine le_iInf₂ fun r' hr' => ?_
    obtain ⟨hm, σ, y, hyc, hy, z, hz1, hz2⟩ := (hidx r').1 hr'
    obtain ⟨u, hu⟩ := S.exists_vcopy hN y
    have hE := S.chain_erc hN lam M ψ r hr hlt hyc
    have hu' : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u) := hu ▸ hy
    have hfu : fl u := by
      obtain ⟨i, hi⟩ := hyc
      exact (hfl u).2 ⟨y, ⟨_, i, hTv, hi⟩, hu⟩
    refine iInf_le_of_le u (iInf_le_of_le (hu ▸ hE.1) (iInf_le_of_le hfu ?_))
    rw [hix u hu']
    have hpc : S.pieceOf ⟨S.copyAt hN y, hy⟩ = S.pieceOf ⟨S.vcopy u, hu'⟩ :=
      congrArg S.pieceOf (Subtype.ext hu)
    exact iInf₂_le r' ⟨hm, σ, z, hz1.trans (congrArg S.vertexEquiv hpc), hz2⟩
  · refine le_iInf fun u => le_iInf fun hERC => le_iInf fun hflu => ?_
    obtain ⟨y, ⟨t', i, hT', hi⟩, hyu⟩ := (hfl u).1 hflu
    obtain ⟨hlt', v', rfl, hv', huniq⟩ := hT t' hT'
    have hE := S.chain_erc hN lam M ψ r hr hlt' ⟨i, hi⟩
    have hvv : v' = v := huniq ((S.erc_symm (hyu ▸ hE.1)).trans hERC)
    subst hvv
    have hy : ∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y) := hE.2 hv'
    have hu' : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u) := hyu ▸ hy
    rw [hix u hu']
    refine le_iInf₂ fun r' hr' => ?_
    obtain ⟨hm, σ, z, hz1, hz2⟩ := hr'
    have hpc : S.pieceOf ⟨S.copyAt hN y, hy⟩ = S.pieceOf ⟨S.vcopy u, hu'⟩ :=
      congrArg S.pieceOf (Subtype.ext hyu)
    exact iInf₂_le_of_le r' ((hidx r').2 ⟨hm, σ, y, ⟨i, hi⟩, hy, z,
      hz1.trans (congrArg S.vertexEquiv hpc.symm), hz2⟩) le_rfl

end RData

end RotSystem

/-- The least value of `r` over a set of indices that holds `i` is its least element. -/
theorem Nat.iInf_isLeast {I : Set ℕ} {i : ℕ} (hi : i ∈ I) :
    IsLeast I (sInf I) ∧ (⨅ r ∈ I, (r : ℕ∞)) = (sInf I : ℕ) := by
  have hm : sInf I ∈ I := Nat.sInf_mem ⟨i, hi⟩
  refine ⟨⟨hm, fun r hr => Nat.sInf_le hr⟩, le_antisymm (iInf₂_le _ hm) (le_iInf₂ fun r hr => ?_)⟩
  exact_mod_cast Nat.sInf_le hr

/-- The least value of `m - r` over a set of indices `r ≤ m` that holds `i` gives its greatest
element. -/
theorem Nat.iInf_sub_isGreatest {I : Set ℕ} {i m : ℕ} (hi : i ∈ I) (hI : ∀ r ∈ I, r ≤ m) :
    IsGreatest I (sSup I) ∧ (⨅ r ∈ I, ((m - r : ℕ) : ℕ∞)) = (m - sSup I : ℕ) := by
  have hb : BddAbove I := ⟨m, hI⟩
  have hm : sSup I ∈ I := Nat.sSup_mem ⟨i, hi⟩ hb
  refine ⟨⟨hm, fun r hr => le_csSup hb hr⟩, le_antisymm (iInf₂_le _ hm) (le_iInf₂ fun r hr => ?_)⟩
  exact_mod_cast Nat.sub_le_sub_left (le_csSup hb hr) m

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ) {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞}
  {Γ : Finset (N.G.Dart × Bool)}

/-- **The least and the greatest index on the walk of an annulus.** Under the conditions of
`RData.level_min_idx`, with `ix` the least index and `jx` the least value of `m - r` over the indices
`r` at the piece of a copy: there is a shortest walk of the annulus of the length of the distance of
the target whose least index on the cut path is the least `ix`, and whose greatest index is `m` minus
the least `jx`, over the flagged copies of the component of the target. Its indices are those of
`RData.level_chain_idx`, read at the copies of the nodes of the chain of the target. -/
theorem level_least_greatest (c : N.G.Dart → ℕ) (hcr : ∀ d, c (N.toRot.rev d) = c d)
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
    ∃ (ps : List (N.G.Dart × Bool)) (i1 i2 : ℕ), L.Shortest t ps ∧
      (ps.map (g ∘ Prod.fst)).sum = ((r ((S.levelPad hN).ι (.inl v))).1 : ℝ≥0∞) ∧
      IsLeast (C.idx (L.κ0 t) ps) i1 ∧ IsGreatest (C.idx (L.κ0 t) ps) i2 ∧
      (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy v)), ⨅ (_ : fl u), ix u) = i1 ∧
      (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy v)), ⨅ (_ : fl u), jx u) =
        (C.m - i2 : ℕ) ∧
      ∀ r', r' ∈ C.idx (L.κ0 t) ps ↔ r' ≤ C.m ∧ ∃ σ, ∃ y,
        (∃ i, (Net.parOf r)^[i] ((S.levelPad hN).ι (.inl v)) = y) ∧
        ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)), ∃ z,
          S.dualSplit.tail z = S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) ∧
          C.cut.tail z = C.cut.tail (C.k σ r') := by
  have hlt := (hT _ hTv).1
  obtain ⟨ps, hps, hsum, hidx⟩ := S.level_chain_idx hN lam M c hcr hlam hgc L hS hz h1 h2 h3 h4 ψ r hr hv
    hpv hroot hlt hle
  have key : ∀ (f : ℕ → ℕ∞) (ix : S.hRot.Vertex → ℕ∞),
      (∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)), ix u = ⨅ r' ∈ S.cutIdx C ⟨S.vcopy u, hu⟩, f r') →
      (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy v)), ⨅ (_ : fl u), ix u) =
        ⨅ r' ∈ C.idx (L.κ0 t) ps, f r' := by
    intro f ix hix
    refine le_antisymm ?_ ?_
    · refine le_iInf₂ fun r' hr' => ?_
      obtain ⟨hm, σ, y, hyc, hy, z, hz1, hz2⟩ := (hidx r').1 hr'
      obtain ⟨u, hu⟩ := S.exists_vcopy hN y
      have hE := S.chain_erc hN lam M ψ r hr hlt hyc
      have hu' : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u) := hu ▸ hy
      have hfu : fl u := by
        obtain ⟨i, hi⟩ := hyc
        exact (hfl u).2 ⟨y, ⟨_, i, hTv, hi⟩, hu⟩
      refine iInf_le_of_le u (iInf_le_of_le (hu ▸ hE.1) (iInf_le_of_le hfu ?_))
      rw [hix u hu']
      have hpc : S.pieceOf ⟨S.copyAt hN y, hy⟩ = S.pieceOf ⟨S.vcopy u, hu'⟩ :=
        congrArg S.pieceOf (Subtype.ext hu)
      exact iInf₂_le r' ⟨hm, σ, z, hz1.trans (congrArg S.vertexEquiv hpc), hz2⟩
    · refine le_iInf fun u => le_iInf fun hERC => le_iInf fun hflu => ?_
      obtain ⟨y, ⟨t', i, hT', hi⟩, hyu⟩ := (hfl u).1 hflu
      obtain ⟨hlt', v', rfl, hv', huniq⟩ := hT t' hT'
      have hE := S.chain_erc hN lam M ψ r hr hlt' ⟨i, hi⟩
      have hvv : v' = v := huniq ((S.erc_symm (hyu ▸ hE.1)).trans hERC)
      subst hvv
      have hy : ∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y) := hE.2 hv'
      have hu' : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u) := hyu ▸ hy
      rw [hix u hu']
      refine le_iInf₂ fun r' hr' => ?_
      obtain ⟨hm, σ, z, hz1, hz2⟩ := hr'
      have hpc : S.pieceOf ⟨S.copyAt hN y, hy⟩ = S.pieceOf ⟨S.vcopy u, hu'⟩ :=
        congrArg S.pieceOf (Subtype.ext hyu)
      exact iInf₂_le_of_le r' ((hidx r').2 ⟨hm, σ, y, ⟨i, hi⟩, hy, z,
        hz1.trans (congrArg S.vertexEquiv hpc.symm), hz2⟩) le_rfl
  have hmem : t ∈ C.idx (L.κ0 t) ps := L.mem_idx h1 h3 ps
  have hI : ∀ r' ∈ C.idx (L.κ0 t) ps, r' ≤ C.m := fun r' hr' => hr'.1
  obtain ⟨hl, hl'⟩ := Nat.iInf_isLeast hmem
  obtain ⟨hg, hg'⟩ := Nat.iInf_sub_isGreatest hmem hI
  exact ⟨ps, _, _, hps, hsum, hl, hg, (key _ ix hix).trans hl', (key _ jx hjx).trans hg', hidx⟩

end RData

end RotSystem

end SsspFlow
