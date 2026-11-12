import SsspFlow.GHatLevelI12
import SsspFlow.GHatChainCopy

/-!
# The least and the greatest index of a level, computed

The algorithm of `RData.levelI12_local` holds at the copy of the target of an annulus, capped at
`M`, the least index and `m` minus the greatest index on the cut path of one shortest walk of the
annulus, when the values `ix` and `jx` at each copy are the least index and the least `m - r` over
the indices `r` at its piece.

* `ENat.toENNReal_iInf`: the cast of an infimum in `ℕ∞` is the infimum of the casts.
* `RData.level_i12_of_marked`: the least values over the copies whose identifiers lie on the chain
  of a target are the least and `m` minus the greatest index of one shortest walk of the annulus.
* `RData.levelI12_run`: assuming the Exact SSSP bound, one algorithm of the message model, fixed
  before the network, after at most `2 C log^c n' · (12 D + 16) + 4` rounds holds these two
  values, capped at `M`, at the copy of the target.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

/-- The cast of an infimum in `ℕ∞` is the infimum of the casts. -/
theorem ENat.toENNReal_iInf {ι : Sort*} (f : ι → ℕ∞) : ((⨅ i, f i : ℕ∞) : ℝ≥0∞) = ⨅ i, (f i : ℝ≥0∞) := by
  refine le_antisymm (le_iInf fun i => ENat.toENNReal_mono (iInf_le f i)) ?_
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · obtain ⟨i, hi⟩ := csInf_mem (Set.range_nonempty f)
    rw [show (⨅ j, f j) = f i from hi.symm]
    exact iInf_le _ i

namespace RotSystem

namespace RData

section Spec

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ) {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞}
  {Γ : Finset (N.G.Dart × Bool)}

/-- **The least and the greatest index from the marked copies.** Under the conditions of
`RData.level_least_greatest`, values `x1`, `x2` that agree, capped at `M`, with the least `ix` and the
least `jx` over the copies of the component of the target whose identifiers lie on the chain of a
target are, capped at `M`, the least index and `m` minus the greatest index on the cut path of one
shortest walk of the annulus, whose indices are read at the copies of the nodes of the chain of the
target. -/
theorem level_i12_of_marked (c : N.G.Dart → ℕ) (hcr : ∀ d, c (N.toRot.rev d) = c d)
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
    (ixI jxI : Fin (n * (n * 21)) → ℕ∞)
    (hix : ∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
      ixI ((S.levelPad hN).ι (.inl u)) = ⨅ r' ∈ S.cutIdx C ⟨S.vcopy u, hu⟩, (r' : ℕ∞))
    (hjx : ∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
      jxI ((S.levelPad hN).ι (.inl u)) = ⨅ r' ∈ S.cutIdx C ⟨S.vcopy u, hu⟩, ((C.m - r' : ℕ) : ℕ∞))
    (x1 x2 : ℝ≥0∞)
    (hx1 : min x1 M = min (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy v)),
      ⨅ (_ : ∃ t i, isT t = true ∧ (Net.parOf r)^[i] t = (S.levelPad hN).ι (.inl u)),
        (ixI ((S.levelPad hN).ι (.inl u)) : ℝ≥0∞)) M)
    (hx2 : min x2 M = min (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy v)),
      ⨅ (_ : ∃ t i, isT t = true ∧ (Net.parOf r)^[i] t = (S.levelPad hN).ι (.inl u)),
        (jxI ((S.levelPad hN).ι (.inl u)) : ℝ≥0∞)) M) :
    ∃ (ps : List (N.G.Dart × Bool)) (i1 i2 : ℕ), L.Shortest t ps ∧
      (ps.map (g ∘ Prod.fst)).sum = ((r ((S.levelPad hN).ι (.inl v))).1 : ℝ≥0∞) ∧
      IsLeast (C.idx (L.κ0 t) ps) i1 ∧ IsGreatest (C.idx (L.κ0 t) ps) i2 ∧
      min x1 M = min (i1 : ℝ≥0∞) M ∧ min x2 M = min ((C.m - i2 : ℕ) : ℝ≥0∞) M ∧
      ∀ r', r' ∈ C.idx (L.κ0 t) ps ↔ r' ≤ C.m ∧ ∃ σ, ∃ y,
        (∃ i, (Net.parOf r)^[i] ((S.levelPad hN).ι (.inl v)) = y) ∧
        ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)), ∃ z,
          S.dualSplit.tail z = S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) ∧
          C.cut.tail z = C.cut.tail (C.k σ r') := by
  have hroot' : ∀ z, ψ z ≠ ⊤ → ∃ u, z = (S.levelPad hN).ι (.inl u) := fun z hz' => by
    obtain ⟨-, u, hu, -⟩ := hroot z hz'
    exact ⟨u, hu⟩
  have hT' : ∀ t', isT t' = true → (r t').1 ≠ ⊤ ∧ ∃ w, t' = (S.levelPad hN).ι (.inl w) := fun t' ht => by
    obtain ⟨hlt, w, hw, -⟩ := hT t' ht
    refine ⟨fun h0 => ?_, w, hw⟩
    rw [h0, ENat.toENNReal_top] at hlt
    exact not_top_lt hlt
  obtain ⟨ps, i1, i2, hps, hsum, hi1, hi2, he1, he2, hidx⟩ := S.level_least_greatest hN lam M c hcr hlam hgc L hS
    hz h1 h2 h3 h4 ψ r hr hv hpv hroot hle isT hT hTv
    (fun u => ∃ t i, isT t = true ∧ (Net.parOf r)^[i] t = (S.levelPad hN).ι (.inl u))
    (fun u => (S.marked_copy_iff hN lam M ψ r hr hroot' isT hT' u).symm)
    (fun u => ixI ((S.levelPad hN).ι (.inl u))) (fun u => jxI ((S.levelPad hN).ι (.inl u))) hix hjx
  refine ⟨ps, i1, i2, hps, hsum, hi1, hi2, ?_, ?_, hidx⟩
  · have e := congrArg ENat.toENNReal he1
    simp only [ENat.toENNReal_iInf, ENat.toENNReal_coe] at e
    rw [hx1, e]
  · have e := congrArg ENat.toENNReal he2
    simp only [ENat.toENNReal_iInf, ENat.toENNReal_coe] at e
    rw [hx2, e]

end Spec

open Classical in
/-- **The least and the greatest index of a level, computed.** Assuming the Exact SSSP bound, one
algorithm of the message model on `N`, fixed before the network, starts from the inputs of a level and,
at each node, offsets, targets and values `ix`, `jx` that agree with `ψ`, `isT`, `ixI`, `jxI` at the
identifiers it hosts. After `T` rounds its outputs `rr` meet the specification of the oracle. Under the
conditions of `RData.level_i12_of_marked` for an annulus with target copy `v`, the outputs `o1` and
`o2` at `v`, capped at `M`, are the least index and `m` minus the greatest index on the cut path of
one shortest walk of the annulus, whose length is the distance at `v`. -/
theorem levelI12_run (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n)
        (LevelIn n × (((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → Bool)) ×
          ((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → ℕ∞)))) σ
        (4 * (C * logN (n * (n * 21)) ^ c + 1) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (rr : Fin (n * (n * 21)) → σ → ℕ∞ × Option (Fin (n * (n * 21))))
      (o1 o2 : Fin (n * (n * 21)) → σ → ℕ∞),
    T ≤ 4 + 2 * (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) ∧
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (lam : S.Tok → ℕ) (M : ℕ)
      (u₀ : S.hRot.Vertex) (ψ : Fin (n * (n * 21)) → ℕ∞) (isT : Fin (n * (n * 21)) → Bool)
      (ixI jxI : Fin (n * (n * 21)) → ℕ∞)
      (off : Fin n → Fin (n * (n * 21)) → ℕ∞) (flg : Fin n → Fin (n * (n * 21)) → Bool)
      (ixL jxL : Fin n → Fin (n * (n * 21)) → ℕ∞),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ z, ψ z = ⊤ ∨ ψ z ≤ (n * (n * 21) + 2) ^ K) →
      (∀ z, (∀ u, z ≠ (S.levelPad hN).ι (.inl u)) → ixI z = ⊤ ∧ jxI z = ⊤) →
      (∀ z, (ixI z = ⊤ ∨ ixI z ≤ (n * (n * 21) + 2) ^ K) ∧ (jxI z = ⊤ ∨ jxI z ≤ (n * (n * 21) + 2) ^ K)) →
      (∀ a, off (hostOf a) a = ψ a) → (∀ a, flg (hostOf a) a = isT a) →
      (∀ a, ixL (hostOf a) a = ixI a) → (∀ a, jxL (hostOf a) a = jxI a) →
      let st := A.run N.G (fun w => (S.levelIn hN lam M u₀ w, ((off w, flg w), (ixL w, jxL w)))) T
      let R := fun a => rr a (st (hostOf a))
      (S.levelNet hN).ExactSpec (S.levelLen hN lam M) ψ R ∧
      ∀ (c : N.G.Dart → ℕ) (_ : ∀ d, c (N.toRot.rev d) = c d) (_ : ∀ x, lam x = c x.1.1)
        (Cp : N.toRot.dual.CutPath) (g : N.G.Dart → ℝ≥0∞) (Γ : Finset (N.G.Dart × Bool))
        (_ : ∀ d, g d = c d) (L : Cp.Live g Γ) (_ : Γ ⊆ S.Γ) (t : ℕ)
        (_ : ∀ w ∈ S.Γ, w ∉ Γ → ∀ p, ¬ (N.toRot.dual.double.split Γ).IsWalk
          ((N.toRot.dual.double.split Γ).tail (L.κ0 t)) p ((N.toRot.dual.double.split Γ).tail w))
        (_ : L.xa ≤ t) (_ : L.ya ≤ t) (_ : t ≤ L.xb) (_ : t ≤ L.yb) (v : S.hRot.Vertex)
        (hv : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v)) (_ : S.pieceOf ⟨S.vcopy v, hv⟩ = S.pieceAt (L.κ1 t))
        (_ : ∀ z, ψ z ≠ ⊤ → ψ z = 0 ∧ ∃ u, z = (S.levelPad hN).ι (.inl u) ∧
          ∃ hu : (∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
            S.pieceOf ⟨S.vcopy u, hu⟩ = S.pieceAt (L.κ0 t) ∨
              (M : ℝ≥0∞) ≤ S.arcDist lam M (S.vcopy u) (S.vcopy v))
        (_ : ((R ((S.levelPad hN).ι (.inl v))).1 : ℝ≥0∞) ≤ Cp.lamD g t)
        (_ : ∀ t', isT t' = true → ((R t').1 : ℝ≥0∞) < M ∧ ∃ v', t' = (S.levelPad hN).ι (.inl v') ∧
          ∃ _ : (∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v')),
            (Relation.ReflTransGen S.ERC (S.vcopy v') (S.vcopy v) → v' = v))
        (_ : isT ((S.levelPad hN).ι (.inl v)) = true)
        (_ : ∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
          ixI ((S.levelPad hN).ι (.inl u)) = ⨅ r' ∈ S.cutIdx Cp ⟨S.vcopy u, hu⟩, (r' : ℕ∞))
        (_ : ∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
          jxI ((S.levelPad hN).ι (.inl u)) = ⨅ r' ∈ S.cutIdx Cp ⟨S.vcopy u, hu⟩, ((Cp.m - r' : ℕ) : ℕ∞)),
        ∃ (ps : List (N.G.Dart × Bool)) (i1 i2 : ℕ), L.Shortest t ps ∧
          (ps.map (g ∘ Prod.fst)).sum = ((R ((S.levelPad hN).ι (.inl v))).1 : ℝ≥0∞) ∧
          IsLeast (Cp.idx (L.κ0 t) ps) i1 ∧ IsGreatest (Cp.idx (L.κ0 t) ps) i2 ∧
          min (o1 ((S.levelPad hN).ι (.inl v)) (st (hostOf ((S.levelPad hN).ι (.inl v)))) : ℝ≥0∞) M =
            min (i1 : ℝ≥0∞) M ∧
          min (o2 ((S.levelPad hN).ι (.inl v)) (st (hostOf ((S.levelPad hN).ι (.inl v)))) : ℝ≥0∞) M =
            min ((Cp.m - i2 : ℕ) : ℝ≥0∞) M := by
  obtain ⟨C, c, hC⟩ := levelI12_local hE K
  refine ⟨C, c, fun n D => ?_⟩
  obtain ⟨σ, A, T, rr, o1, o2, hT, hA⟩ := hC n D
  refine ⟨σ, A, T, rr, o1, o2, hT, ?_⟩
  intro N S hN lam M u₀ ψ isT ixI jxI off flg ixL jxL hP hc hS hcut hD hlam hM hψW hix0 hixW hoff hflg
    hixL hjxL
  obtain ⟨hR, hO⟩ := hA N S hN lam M u₀ ψ isT ixI jxI off flg ixL jxL hP hc hS hcut hD hlam hM hψW hix0
    hixW hoff hflg hixL hjxL
  refine ⟨hR, fun cc hcr hcl Cp g Γ hgc L hΓ t hz h1 h2 h3 h4 v hv hpv hroot hle hTt hTv hix hjx => ?_⟩
  obtain ⟨ps, i1, i2, a1, a2, a3, a4, a5, a6, -⟩ := S.level_i12_of_marked hN lam M cc hcr hcl hgc L hΓ hz
    h1 h2 h3 h4 ψ _ hR hv hpv hroot hle isT hTt hTv ixI jxI hix hjx _ _ (hO v).1 (hO v).2
  exact ⟨ps, i1, i2, a1, a2, a3, a4, a5, a6⟩

end RData

end RotSystem

end SsspFlow
