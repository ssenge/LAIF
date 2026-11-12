import SsspFlow.GHatChainIdx

/-!
# The least and the greatest index of all annuli of a level, on the chains

For the sources and targets of a list of annuli of a level of a run, each with one index and
`λ_t < M`, the algorithm of `RData.levelI12_local` holds at the target of every annulus the least
index and `m` minus the greatest index on the cut path of the walk of the annulus that the darts of
the chain of the target form.

* `RData.levelI12_roots_run`: assuming the Exact SSSP bound, after at most
  `2 C log^c n' · (12 D + 16) + 4` rounds the outputs at the target of every annulus of the list are,
  capped at `M`, the least index and `m` minus the greatest index of the darts of its chain, which
  form a shortest walk of the annulus.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

open Classical in
/-- **The least and the greatest index of all annuli of a level, as one algorithm.** Assuming the
Exact SSSP bound, one algorithm of the message model on `N`, fixed before the network, starts from
the inputs of a level and, at each node, the offsets of the sources and the targets of a list `Q` of
annuli of a level of a run with one index each and `λ_t < M`, and values `ix`, `jx` at the identifiers
it hosts. After `T` rounds its outputs `rr` meet the specification of the oracle, and for every
annulus of `Q` the chain of its target reaches a root at the piece at `κ0(t)` in `k` valid parent
steps, with sum of lengths the distance at the target, the darts of the chain form a shortest walk of
the annulus, and the outputs `o1` and `o2` at the target, capped at `M`, are its least index and `m`
minus its greatest index on the cut path. -/
theorem levelI12_roots_run (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n)
        (LevelIn n × (((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → Bool)) ×
          ((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → ℕ∞)))) σ
        (4 * (C * logN (n * (n * 21)) ^ c + 1) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (rr : Fin (n * (n * 21)) → σ → ℕ∞ × Option (Fin (n * (n * 21))))
      (o1 o2 : Fin (n * (n * 21)) → σ → ℕ∞),
    T ≤ 4 + 2 * (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) ∧
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
      {Cp : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞} {hR : N.toRot.dual.Planar}
      {hC : N.toRot.dual.Connected} {hg : ∀ x, g (N.toRot.dual.rev x) = g x}
      {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live g Γ₀} {j k : ℕ}
      (r : CutPath.Run hR hC hg Γ₀ L₀ j k) (ℓ : ℕ) (lam : S.Tok → ℕ) (M : ℕ) (cc : N.G.Dart → ℕ)
      (u₀ : S.hRot.Vertex) (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live g Γ') × ℕ))
      (ixI jxI : Fin (n * (n * 21)) → ℕ∞)
      (off : Fin n → Fin (n * (n * 21)) → ℕ∞) (flg : Fin n → Fin (n * (n * 21)) → Bool)
      (ixL jxL : Fin n → Fin (n * (n * 21)) → ℕ∞),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ d, cc (N.toRot.rev d) = cc d) → (∀ x, lam x = cc x.1.1) → (∀ d, g d = cc d) →
      S.Γ = Γ₀ ∪ r.steps ℓ →
      (∀ q ∈ Q, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧ q.2 ≤ q.1.2.xb ∧
        q.2 ≤ q.1.2.yb ∧ Cp.lamD g q.2 < M) →
      (∀ q ∈ Q, ∀ q' ∈ Q, q.1 = q'.1 → q.2 = q'.2) →
      (∀ z, (∀ u, z ≠ (S.levelPad hN).ι (.inl u)) → ixI z = ⊤ ∧ jxI z = ⊤) →
      (∀ z, (ixI z = ⊤ ∨ ixI z ≤ (n * (n * 21) + 2) ^ K) ∧ (jxI z = ⊤ ∨ jxI z ≤ (n * (n * 21) + 2) ^ K)) →
      (∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
        ixI ((S.levelPad hN).ι (.inl u)) = ⨅ r' ∈ S.cutIdx Cp ⟨S.vcopy u, hu⟩, (r' : ℕ∞)) →
      (∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
        jxI ((S.levelPad hN).ι (.inl u)) = ⨅ r' ∈ S.cutIdx Cp ⟨S.vcopy u, hu⟩, ((Cp.m - r' : ℕ) : ℕ∞)) →
      (∀ a, off (hostOf a) a = S.srcOff hN Q a) → (∀ a, flg (hostOf a) a = S.tgtFlag hN Q a) →
      (∀ a, ixL (hostOf a) a = ixI a) → (∀ a, jxL (hostOf a) a = jxI a) →
      let st := A.run N.G (fun w => (S.levelIn hN lam M u₀ w, ((off w, flg w), (ixL w, jxL w)))) T
      let R := fun a => rr a (st (hostOf a))
      (S.levelNet hN).ExactSpec (S.levelLen hN lam M) (S.srcOff hN Q) R ∧
      ∀ At ∈ Q, ∃ (kk : ℕ) (u : S.hRot.Vertex) (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)) (i1 i2 : ℕ),
        Net.ParSteps R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) kk ∧
        (Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) = (S.levelPad hN).ι (.inl u) ∧
        (R ((S.levelPad hN).ι (.inl u))).2 = none ∧ S.pieceOf ⟨S.vcopy u, hu⟩ = S.pieceAt (At.1.2.κ0 At.2) ∧
        ((∑ l ∈ Finset.range kk, S.levelLen hN lam M
          ((Net.parOf R)^[l + 1] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))
          ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))) : ℕ∞) : ℝ≥0∞) =
          ((R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))).1 : ℝ≥0∞) ∧
        At.1.2.Shortest At.2 (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk) ∧
        IsLeast (Cp.idx (At.1.2.κ0 At.2)
          (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk)) i1 ∧
        IsGreatest (Cp.idx (At.1.2.κ0 At.2)
          (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk)) i2 ∧
        min (o1 ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))
          (st (hostOf ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))))  : ℝ≥0∞) M =
            min (i1 : ℝ≥0∞) M ∧
        min (o2 ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))
          (st (hostOf ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))) : ℝ≥0∞) M =
            min ((Cp.m - i2 : ℕ) : ℝ≥0∞) M := by
  obtain ⟨C, c, hC⟩ := levelI12_local hE K
  refine ⟨C, c, fun n D => ?_⟩
  obtain ⟨σ, A, T, rr, o1, o2, hT, hA⟩ := hC n D
  refine ⟨σ, A, T, rr, o1, o2, hT, ?_⟩
  intro N S hN Cp g hR hC hg Γ₀ L₀ j k r ℓ lam M cc u₀ Q ixI jxI off flg ixL jxL hP hc hS hcut hD hlam hM
    hcr hlc hgc hΓ hQ hQu hix0 hixW hix hjx hoff hflg hixL hjxL
  have hψW : ∀ z, S.srcOff hN Q z = ⊤ ∨ S.srcOff hN Q z ≤ (n * (n * 21) + 2) ^ K := fun z => by
    unfold srcOff
    split_ifs
    · exact .inr zero_le
    · exact .inl rfl
  obtain ⟨hR', hO⟩ := hA N S hN lam M u₀ (S.srcOff hN Q) (S.tgtFlag hN Q) ixI jxI off flg ixL jxL hP hc hS
    hcut hD hlam hM hψW hix0 hixW hoff hflg hixL hjxL
  refine ⟨hR', fun At hAt => ?_⟩
  have hAt' : (At.1, At.2) ∈ Q := by simpa using hAt
  obtain ⟨ps, i1, i2, -, -, hl, hg, e1, e2, hidx⟩ := S.level_i12_roots hN r ℓ lam M cc hcr hlc hgc hΓ Q hQ
    hQu _ hR' ixI jxI hix hjx (A := At.1) (t := At.2) hAt' _ _ (hO (S.endV (At.1.2.κ1 At.2))).1
    (hO (S.endV (At.1.2.κ1 At.2))).2
  obtain ⟨hA, hun, h1, h2, h3, h4, hroot, hup, hT, hTv⟩ :=
    S.level_roots_cond hN r ℓ lam M cc hcr hlc hgc hΓ Q hQ hQu _ hR' hAt'
  obtain ⟨kk, u, hu, hs, hρu, hnone, hpu, hsum, hsh, hidx'⟩ := S.chain_data hN lam M cc hcr hlc hgc At.1.2 hA
    hun h1 h2 h3 h4 _ _ hR' (S.endV_end _) (S.pieceOf_endV _) hroot (hT _ hTv).1 hup
  have hE : Cp.idx (At.1.2.κ0 At.2)
      (S.chainDarts hN _ ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk) =
      Cp.idx (At.1.2.κ0 At.2) ps := Set.ext fun r' => (hidx' r').trans (hidx r').symm
  exact ⟨kk, u, hu, i1, i2, hs, hρu, hnone, hpu, hsum, hsh, hE ▸ hl, hE ▸ hg, e1, e2⟩

end RData

end RotSystem

end SsspFlow
