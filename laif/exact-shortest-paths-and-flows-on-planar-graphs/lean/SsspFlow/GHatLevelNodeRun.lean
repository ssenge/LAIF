import SsspFlow.GHatLevelNode
import SsspFlow.GHatLevelChainRuns

/-!
# The data of the nodes of a run at a level, as one algorithm

One algorithm of the message model runs, on local inputs, the algorithm of `RData.levelI12_roots_run`
and then the runs along the chains of `RData.levelChain_local`. Both use the chosen oracle on the same
sources, so they follow the same parents, and the step found on the chain of a target is a segment of
the shortest walk whose least and greatest index on the cut path the first part computes.

* `RData.levelNode_run`: for all annuli of a level, the walk, the two indices and the step, from one
  algorithm with a bound on its rounds.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

open Classical in
/-- **The data of the nodes of a run at a level, as one algorithm.** There are constants `C` and `c`
such that for all `n` and `D` one algorithm of the message model, with `O(log^c n)` bits per message,
runs in at most `6 + 3 C log^c n (12 D + 16)` rounds on the network of the level of a run, with local
inputs: the input of the level, the sources and the flags of the targets and of the nodes for `0` and
`1`, and the cut-path indices. For every annulus `At` of `Q` there are a number `kk` of parent steps
from its target, its least and greatest index `i1`, `i2` and a step, such that the darts of the chain
of `kk` parent steps form a shortest walk of the annulus, `i1` and `i2` are the least and the greatest
index on the cut path of that walk, the outputs `o1` and `o2` at the target, capped at `M`, are `i1`
and `m - i2`, the darts of the step are those of the parent arcs of the nodes of the chain that meet
the local test on the outputs `r₂`, `r₃` and the flags, and they form a segment of the walk. The walk
visits a corner exactly when the piece of the copy of a node of the chain is its vertex. -/
theorem levelNode_run (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n)
        (LevelIn n × (((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → Bool × Bool × Bool)) ×
          ((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → ℕ∞)))) σ
        (4 * (C * logN (n * (n * 21)) ^ c + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (rr r₂ r₃ : Fin (n * (n * 21)) → σ → ℕ∞ × Option (Fin (n * (n * 21))))
      (o1 o2 : Fin (n * (n * 21)) → σ → ℕ∞),
    T ≤ 6 + 3 * (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) ∧
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
      {Cp : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞} {hR : N.toRot.dual.Planar}
      {hC : N.toRot.dual.Connected} {hg : ∀ x, g (N.toRot.dual.rev x) = g x}
      {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live g Γ₀} {j k : ℕ}
      (r : CutPath.Run hR hC hg Γ₀ L₀ j k) (ℓ : ℕ) (lam : S.Tok → ℕ) (M : ℕ) (cc : N.G.Dart → ℕ)
      (u₀ : S.hRot.Vertex) (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live g Γ') × ℕ))
      (ixI jxI : Fin (n * (n * 21)) → ℕ∞)
      (off : Fin n → Fin (n * (n * 21)) → ℕ∞) (flg : Fin n → Fin (n * (n * 21)) → Bool × Bool × Bool)
      (ixL jxL : Fin n → Fin (n * (n * 21)) → ℕ∞),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ d, 1 ≤ cc d) → (∀ d, cc (N.toRot.rev d) = cc d) → (∀ x, lam x = cc x.1.1) →
      (∀ d, g d = cc d) → S.Γ = Γ₀ ∪ r.steps ℓ →
      (∀ q ∈ Q, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧ q.2 ≤ q.1.2.xb ∧
        q.2 ≤ q.1.2.yb ∧ Cp.lamD g q.2 < M) →
      (∀ q ∈ Q, ∀ q' ∈ Q, q.1 = q'.1 → q.2 = q'.2) →
      (∀ z, (∀ u, z ≠ (S.levelPad hN).ι (.inl u)) → ixI z = ⊤ ∧ jxI z = ⊤) →
      (∀ z, (ixI z = ⊤ ∨ ixI z ≤ (n * (n * 21) + 2) ^ K) ∧ (jxI z = ⊤ ∨ jxI z ≤ (n * (n * 21) + 2) ^ K)) →
      (∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
        ixI ((S.levelPad hN).ι (.inl u)) = ⨅ r' ∈ S.cutIdx Cp ⟨S.vcopy u, hu⟩, (r' : ℕ∞)) →
      (∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
        jxI ((S.levelPad hN).ι (.inl u)) = ⨅ r' ∈ S.cutIdx Cp ⟨S.vcopy u, hu⟩, ((Cp.m - r' : ℕ) : ℕ∞)) →
      (∀ a, off (hostOf a) a = S.srcOff hN Q a) →
      (∀ a, flg (hostOf a) a =
        (S.tgtFlag hN Q a, decide (S.nodeFlag hN Cp 0 a), decide (S.nodeFlag hN Cp 1 a))) →
      (∀ a, ixL (hostOf a) a = ixI a) → (∀ a, jxL (hostOf a) a = jxI a) →
      let st := A.run N.G (fun w => (S.levelIn hN lam M u₀ w, ((off w, flg w), (ixL w, jxL w)))) T
      let R := fun a => rr a (st (hostOf a))
      (S.levelNet hN).ExactSpec (S.levelLen hN lam M) (S.srcOff hN Q) R ∧
      R = hE.oracleRun K (12 * D + 16) (by omega) (S.levelNet hN) (S.levelLen hN lam M) (S.srcOff hN Q) ∧
      ∀ At ∈ Q, ∃ (kk i1 i2 : ℕ) (St : At.1.2.Step),
        At.1.2.Shortest At.2 (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk) ∧
        IsLeast (Cp.idx (At.1.2.κ0 At.2)
          (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk)) i1 ∧
        IsGreatest (Cp.idx (At.1.2.κ0 At.2)
          (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk)) i2 ∧
        min (o1 ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))
          (st (hostOf ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))) : ℝ≥0∞) M =
            min (i1 : ℝ≥0∞) M ∧
        min (o2 ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))
          (st (hostOf ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))) : ℝ≥0∞) M =
            min ((Cp.m - i2 : ℕ) : ℝ≥0∞) M ∧
        (∀ z, z ∈ (List.range St.n).map St.q ↔ ∃ l,
          Net.ParSteps R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) (l + 1) ∧
          (r₂ ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))
            (st (hostOf ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))))).1 = 0 ∧
          (flg (hostOf ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))))
            ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))).2.1 = false ∧
          (r₃ ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))
            (st (hostOf ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))))).1 = 0 ∧
          ∃ x, S.edgeTok hN ((Net.parOf R)^[l + 1] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))
              ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))) = some x ∧
            z = N.toRot.tokDart x.1) ∧
        (∃ p₁ p₃, S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk =
          p₁ ++ (List.range St.n).map St.q ++ p₃) ∧
        ∀ c, At.1.2.Visits At.2 (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk) c ↔
          ∃ y, (∃ i, (Net.parOf R)^[i] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) = y) ∧
            ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)),
              S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) = S.dualSplit.tail c := by
  obtain ⟨C₁, c₁, hI⟩ := levelI12_roots_run hE K
  obtain ⟨C₂, c₂, hH⟩ := levelChain_local hE K
  refine ⟨C₁ + C₂, c₁ + c₂, fun n D => ?_⟩
  obtain ⟨σ₁, A₁, T₁, rr₁, o1₁, o2₁, hT₁, hA₁⟩ := hI n D
  obtain ⟨σ₂, A₂, T₂, out₂, hT₂, hA₂⟩ := hH n D
  have hL : 1 ≤ logN (n * (n * 21)) := by unfold logN; omega
  have hp₁ : logN (n * (n * 21)) ^ c₁ ≤ logN (n * (n * 21)) ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hp₂ : logN (n * (n * 21)) ^ c₂ ≤ logN (n * (n * 21)) ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hm₁ := Nat.mul_le_mul (show C₁ ≤ C₁ + C₂ by omega) hp₁
  have hm₂ := Nat.mul_le_mul (show C₂ ≤ C₁ + C₂ by omega) hp₂
  have hw₁ : 4 * (C₁ * logN (n * (n * 21)) ^ c₁ + 1) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤
      4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) := by
    omega
  have hw₂ : 4 * (C₂ * logN (n * (n * 21)) ^ c₂ + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤
      4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) := by
    omega
  let J := LevelIn n × (((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → Bool × Bool × Bool)) ×
    ((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → ℕ∞)))
  let g₁ : Fin n → J → LevelIn n × (((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → Bool)) ×
      ((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → ℕ∞))) :=
    fun _ q => (q.1, ((q.2.1.1, fun a => (q.2.1.2 a).1), q.2.2))
  let B₁ := (A₁.widen hw₁).keep g₁
  let B₂ := (A₂.widen hw₂).keep (fun _ (p : J × σ₁) => (p.1.1, p.1.2.1))
  let A := B₁.seq T₁ (fun _ s => s) B₂
  refine ⟨_, A, T₁ + T₂,
    fun a => Sum.elim (fun _ => (⊤, none)) (fun p => rr₁ a p.1.2),
    fun a => Sum.elim (fun _ => (⊤, none)) (fun p => (out₂ a p.2).2.1),
    fun a => Sum.elim (fun _ => (⊤, none)) (fun p => (out₂ a p.2).2.2),
    fun a => Sum.elim (fun _ => 0) (fun p => o1₁ a p.1.2),
    fun a => Sum.elim (fun _ => 0) (fun p => o2₁ a p.1.2), ?_, ?_⟩
  · have h : C₁ * logN (n * (n * 21)) ^ c₁ * (12 * D + 16) + C₂ * logN (n * (n * 21)) ^ c₂ * (12 * D + 16) ≤
        (C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) * (12 * D + 16) := by
      rw [← Nat.add_mul]
      refine Nat.mul_le_mul_right _ ?_
      rw [Nat.add_mul]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ hp₁) (Nat.mul_le_mul_left _ hp₂)
    omega
  intro N S hN Cp g hR hC hg Γ₀ L₀ j k r ℓ lam M cc u₀ Q ixI jxI off flg ixL jxL hP hc hS hcut hD hlam hM
    hc1 hcr hlc hgc hΓ hQ hQu hix0 hixW hix hjx hoff hflg hixL hjxL
  have hψW : ∀ z, S.srcOff hN Q z = ⊤ ∨ S.srcOff hN Q z ≤ (n * (n * 21) + 2) ^ K := fun z => by
    unfold srcOff
    split_ifs
    · exact .inr zero_le
    · exact .inl rfl
  have hrun : A.run N.G (fun w => (S.levelIn hN lam M u₀ w, ((off w, flg w), (ixL w, jxL w)))) (T₁ + T₂) =
      fun w => .inr (((S.levelIn hN lam M u₀ w, ((off w, flg w), (ixL w, jxL w))),
        A₁.run N.G (fun w => (S.levelIn hN lam M u₀ w, ((off w, fun a => (flg w a).1), (ixL w, jxL w)))) T₁ w),
        A₂.run N.G (fun w => (S.levelIn hN lam M u₀ w, (off w, flg w))) T₂ w) := by
    funext w
    simp only [A, B₁, B₂, Cslib.Congest.Algorithm.run_seq, Cslib.Congest.Algorithm.run_keep,
      Cslib.Congest.Algorithm.run_widen]
    rfl
  obtain ⟨hR', hRe, hO⟩ := hA₁ N S hN r ℓ lam M cc u₀ Q ixI jxI off (fun w a => (flg w a).1) ixL jxL hP hc hS
    hcut hD hlam hM hcr hlc hgc hΓ hQ hQu hix0 hixW hix hjx hoff (fun a => by rw [hflg]) hixL hjxL
  obtain ⟨-, hr₂, hr₃, hRe₂⟩ := hA₂ N S hN lam M u₀ (S.srcOff hN Q) (fun a => flg (hostOf a) a) off flg hP hc hS
    hcut hD hlam hM hψW hoff (fun _ => rfl)
  rw [hRe₂, ← hRe] at hr₂ hr₃
  simp only [hrun, Sum.elim_inr]
  refine ⟨hR', hRe, fun At hAt => ?_⟩
  have hAt' : (At.1, At.2) ∈ Q := by simpa using hAt
  obtain ⟨kk, u, hu, i1, i2, hs, hρu, -, hpu, hsum, hsh, hl, hg', e1, e2, hvc⟩ := hO At hAt
  obtain ⟨St, hSt, hsub⟩ := S.level_node_step hN r ℓ lam M cc hc1 hcr hlc hgc hΓ Q hQ hQu _ _ _ hR'
    (fun a => flg (hostOf a) a) hflg hr₂ hr₃ hAt' kk u hu hs hρu hpu hsum
  exact ⟨kk, i1, i2, St, hsh, hl, hg', e1, e2, hSt, hsub, hvc⟩

end RData

end RotSystem

end SsspFlow
