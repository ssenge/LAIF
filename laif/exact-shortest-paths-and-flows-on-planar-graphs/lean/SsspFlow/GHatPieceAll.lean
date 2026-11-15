import SsspFlow.GHatPieceRun

/-!
# The least value at each piece, at every copy

The run of `RData.levelPieceVal_local` holds at every copy, also at a copy at which no token ends, the
least value of `copyVal` over the copies joined to it by E_R edges, capped at `M`. A copy at which no
token ends is joined to no other copy, so there the capped value is `M`.

* `RData.levelPieceVal_all`: the least value of `copyVal` over the copies joined by E_R edges, at
  every copy.
* `RData.erMin_noEnd`: at a copy at which no token ends this least value is `⊤`.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

open Cslib.Congest.Algorithm in
/-- **The least value at each piece, at every copy.** The algorithm of `RData.levelPieceVal_local`
holds at every copy the least value of `copyVal g` over the copies joined to it by E_R edges, capped
at `M`. -/
theorem levelPieceVal_all (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n)
        (LevelIn n × ((Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))) σ
      (4 * (C * logN (n * (n * 21)) ^ c) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (out : Fin (n * (n * 21)) → σ → ℕ∞),
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (lam : S.Tok → ℕ) (M : ℕ)
      (u₀ : S.hRot.Vertex) (g : N.G.Dart × Bool → ℕ∞) (vo vi : Fin n → Fin n → Bool → ℕ∞),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → 1 ≤ M → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ z, g z = ⊤ ∨ g z ≤ (n * (n * 21) + 2) ^ K) →
      (∀ (d : N.G.Dart) b, vo d.fst d.snd b = g (d, b)) →
      (∀ (d : N.G.Dart) b, vi d.snd d.fst b = g (d, b)) →
      ∀ v : S.hRot.Vertex,
        min (out ((S.levelPad hN).ι (.inl v))
          (A.run N.G (fun w => (S.levelIn hN lam M u₀ w, (vo w, vi w)))
            (1 + (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16))) (hostOf ((S.levelPad hN).ι (.inl v)))) :
            ℝ≥0∞) M =
          min (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ER (S.vcopy u) (S.vcopy v)),
            ((S.copyVal g (S.vcopy u) : ℕ∞) : ℝ≥0∞)) M := by
  obtain ⟨C, c, hC⟩ := levelPieceMin_local hE K
  refine ⟨C, c, fun n D => ?_⟩
  set b := K * logN (n * (n * 21)) + 1
  set Bw := 4 * (C * logN (n * (n * 21)) ^ c) + (3 * b + 5)
  obtain ⟨σ, A, out, hA⟩ := hC n D
  let Aex := (exchTo (Fin n) Bw).keep
    (fun _ (j : LevelIn n × ((Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))) => j.1.msg b)
  let f : Fin n → (LevelIn n × ((Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))) ×
      ((Fin n → ℕ) × (Fin n → Option ℕ)) → LevelIn n × (Fin (n * (n * 21)) → ℕ∞) :=
    fun w s => (s.1.1.withConst s.1.1.bnd, pieceOff b w s.1 s.2.2)
  refine ⟨_, Aex.seq 1 f A, fun a s => match s with
    | .inr s' => out a s'
    | .inl _ => ⊤, ?_⟩
  intro N S hN lam M u₀ g vo vi hP hc hS hcut hD hlam hM1 hM hg hvo hvi v
  have hb : ∀ x, lam x < 2 ^ b := fun x => lam_lt_pow (hlam x)
  have hmsg : ∀ u w, (S.levelIn hN lam M u₀ u).msg b w < 2 ^ Bw := fun u w =>
    (DInfo.pack_lt _ (S.lamAt_lt lam hb _ _ _) (S.lamAt_lt lam hb _ _ _) (S.lamAt_lt lam hb _ _ _)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  set ψ := S.onCopies hN (fun u => S.copyVal g (S.vcopy u))
  have hex : (fun w => f w (Aex.run N.G (fun w => (S.levelIn hN lam M u₀ w, (vo w, vi w))) 1 w)) =
      fun w => ((S.levelIn hN lam M u₀ w).withConst M,
        pieceOff b w (S.levelIn hN lam M u₀ w, (vo w, vi w)) (S.levelRecv hN lam M b u₀ w)) := by
    funext w
    show f w ((exchTo (Fin n) Bw).keep
      (fun _ (j : LevelIn n × ((Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))) => j.1.msg b) |>.run N.G _ 1 w) = _
    rw [run_keep]
    show (_, pieceOff b w (S.levelIn hN lam M u₀ w, (vo w, vi w))
      ((exchTo (Fin n) Bw).run N.G _ 1 w).2) = _
    rw [run_exchTo N.G _ hmsg]
    rfl
  have hoff : ∀ a, pieceOff b (hostOf a) (S.levelIn hN lam M u₀ (hostOf a), (vo (hostOf a), vi (hostOf a)))
      (S.levelRecv hN lam M b u₀ (hostOf a)) a = ψ a := fun a => by
    unfold pieceOff
    rw [S.inn_recv hN lam M hb u₀ (hostOf a)]
    show locCopy (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a)) (vo (hostOf a)) (vi (hostOf a))
      (idEquiv.symm a).2.2 (rawAt (N.rotList (hostOf a)) (S.dinfoAt (hostOf a))
        (fun u => S.dinfoAt u (hostOf a)) (hostOf a) ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2)) = _
    rw [← S.levelNet_rotList_raw hN a]
    exact S.locCopy_eq hN _ vo vi hvo hvi a
  have hψ : ∀ z, (∀ u, z ≠ (S.levelPad hN).ι (.inl u)) → ψ z = ⊤ := fun z hz => S.onCopies_other hN _ z hz
  have hψW : ∀ z, ψ z = ⊤ ∨ ψ z ≤ (n * (n * 21) + 2) ^ K := fun z =>
    ENat.iInf_top_or_le fun u => ENat.iInf_top_or_le fun _ => ENat.iInf_top_or_le fun y =>
      ENat.iInf_top_or_le fun _ => ENat.iInf_top_or_le fun z' => ENat.iInf_top_or_le fun _ =>
        by exact_mod_cast hg z'
  rw [run_seq, hex]
  dsimp only
  rw [hA N S hN lam M u₀ ψ _ hP hc hS hcut hD hM1 hM hψ hψW hoff v]
  congr 1
  exact iInf_congr fun u => iInf_congr fun _ => congrArg _ (S.onCopies_copy hN _ u)

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData)

/-- **No least value at a copy without token ends.** At a copy at which no token ends, the least value
of `copyVal g` over the copies joined to it by E_R edges is `⊤`. -/
theorem erMin_noEnd (g : N.G.Dart × Bool → ℕ∞) (v : S.hRot.Vertex)
    (hv : ¬ ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v)) :
    (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ER (S.vcopy u) (S.vcopy v)),
      ((S.copyVal g (S.vcopy u) : ℕ∞) : ℝ≥0∞)) = ⊤ := by
  refine iInf_eq_top.2 fun u => iInf_eq_top.2 fun h => ?_
  rcases h.cases_tail with e | ⟨c, -, x, hx⟩
  · rw [← e]
    have : S.copyVal g (S.vcopy v) = ⊤ :=
      iInf_eq_top.2 fun y => iInf_eq_top.2 fun hy => absurd ⟨y, hy⟩ hv
    rw [this]
    rfl
  · rcases hx with ⟨-, hb⟩ | ⟨-, ha⟩
    · exact absurd ⟨x, .inr hb⟩ hv
    · exact absurd ⟨x, .inl ha⟩ hv

end RData

end RotSystem

end SsspFlow
