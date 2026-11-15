import SsspFlow.GHatPieceLocal
import SsspFlow.GHatLevelOff

/-!
# The least value at each piece, from local data

From the inputs of a level and, at each node, the values of a function `g` of the corners at the
corners of both darts of its edges (for example the least value `φ r` over the indices `r` of the cut
path at a corner), one round of exchange gives every node the records of the darts
into it. Then every node knows the rotation lists of the network of the level at its identifiers, so it
computes `copyVal` at each copy it hosts, and one run of the oracle with all token lengths `M` gives at
every copy on E_R edges the least value of `g` over the corners at its piece, capped at `M`.

* `ENat.iInf_top_or_le`: least values of values that are `⊤` or at most `B` are `⊤` or at most `B`.
* `RData.levelPieceVal_local`: one algorithm of the message model that holds at every copy on E_R edges
  the least value of a function of the corners over the corners at its piece, capped at `M`.
* `RData.copyPiece_iff`: a piece lies at a copy `p_t^σ` exactly when the least flag over its corners
  is `0`.
* `RData.cutIdx_top_or_lt`: the least index at a piece is `⊤` or below `M > m`, so it is recovered from
  its cap (`ENat.uncap_eq`).
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

theorem ENat.iInf_top_or_le {ι : Sort*} {g : ι → ℕ∞} {B : ℕ∞} (h : ∀ i, g i = ⊤ ∨ g i ≤ B) :
    (⨅ i, g i) = ⊤ ∨ (⨅ i, g i) ≤ B := by
  by_cases hx : ∃ i, g i ≠ ⊤
  · obtain ⟨i, hi⟩ := hx
    exact .inr (iInf_le_of_le i ((h i).resolve_left hi))
  · simp only [ne_eq, not_exists, not_not] at hx
    exact .inl (iInf_eq_top.2 hx)

namespace RotSystem

namespace RData

/-- The offsets of a node `w` for the run on the pieces: `copyVal` at its copies, from its inputs and
the numbers it received. -/
noncomputable def pieceOff {n : ℕ} (b : ℕ) (w : Fin n)
    (j : LevelIn n × ((Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))) (r : Fin n → Option ℕ)
    (a : Fin (n * (n * 21))) : ℕ∞ :=
  locCopy j.1.own (LevelIn.inn b r) j.2.1 j.2.2 (idEquiv.symm a).2.2
    (rawAt j.1.rot j.1.own (LevelIn.inn b r) w ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2))

open Cslib.Congest.Algorithm in
/-- **The least value at each piece, from local data.** Assuming the Exact SSSP bound, one algorithm of
the message model on `N`, fixed before the network, starts from the inputs of a level and, at each node
`w`, the values `vo w u b` and `vi w u b` of `g` at the corners `((w, u), b)` and `((u, w), b)`. After
`C log^c n' · (12 D + 16) + 2` rounds it holds at every copy on E_R edges the least value of `g` over
the corners at the vertex of its piece, capped at `M`. With `g z` the least value of `φ` over the
indices of the cut path at `z` (`RData.cutIdx_iInf`), this is the least value of `φ` over the indices
at the piece. -/
theorem levelPieceVal_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
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
      ∀ (v : S.hRot.Vertex) (hv : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v)),
        min (out ((S.levelPad hN).ι (.inl v))
          (A.run N.G (fun w => (S.levelIn hN lam M u₀ w, (vo w, vi w)))
            (1 + (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16))) (hostOf ((S.levelPad hN).ι (.inl v)))) :
            ℝ≥0∞) M =
          min (((⨅ z, ⨅ (_ : S.pieceAt z = S.pieceOf ⟨S.vcopy v, hv⟩), g z : ℕ∞)) : ℝ≥0∞) M := by
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
  intro N S hN lam M u₀ g vo vi hP hc hS hcut hD hlam hM1 hM hg hvo hvi v hv
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
  rw [hA N S hN lam M u₀ ψ _ hP hc hS hcut hD hM1 hM hψ hψW hoff v, S.pieceMin_eq g ⟨S.vcopy v, hv⟩,
    ENat.toENNReal_iInf]
  congr 1
  refine iInf_congr fun u => ?_
  rw [ENat.toENNReal_iInf]
  exact iInf_congr fun _ => congrArg _ (S.onCopies_copy hN _ u)


open Classical in
/-- The flag of a corner for `σ`: `0` if it lies at a corner `p_t^σ` in the cut along `C`, `⊤`
otherwise. -/
noncomputable def flagVal {n : ℕ} {N : Net (Fin n)} (C : N.toRot.dual.CutPath) (σ : Fin 2)
    (z : N.G.Dart × Bool) : ℕ∞ :=
  if ∃ t, t ≤ C.m ∧ C.cut.tail z = C.cut.tail (C.k σ t) then 0 else ⊤

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData)

/-- **The flags of a piece from its corners.** A piece lies at a copy `p_t^σ` exactly when the least
flag for `σ` over the corners at its vertex is `0`. -/
theorem copyPiece_iff (C : N.toRot.dual.CutPath) (σ : Fin 2) (a : S.EndCopy) :
    S.CopyPiece C σ (S.pieceOf a) ↔ (⨅ z, ⨅ (_ : S.pieceAt z = S.pieceOf a), flagVal C σ z) = 0 := by
  classical
  constructor
  · rintro ⟨t, ht, z, hz, hc⟩
    refine le_antisymm (iInf_le_of_le z (iInf_le_of_le ((S.tail_eq_vertexEquiv_iff z _).1 hz) ?_)) zero_le
    unfold flagVal
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨t, ht, hc⟩)]
  · intro h
    by_contra hn
    have htop : (⨅ z, ⨅ (_ : S.pieceAt z = S.pieceOf a), flagVal C σ z) = ⊤ := by
      refine iInf_eq_top.2 fun z => iInf_eq_top.2 fun hz => ?_
      unfold flagVal
      split_ifs with hc'
      · obtain ⟨t, ht, hc⟩ := hc'
        exact absurd ⟨t, ht, z, (S.tail_eq_vertexEquiv_iff z _).2 hz, hc⟩ hn
      · rfl
    rw [htop] at h
    exact ENat.top_ne_zero h

/-- The least value of `r` or of `m - r` over the indices of the cut path at a piece is `⊤` or at most
`m`. -/
theorem cutIdx_top_or_lt (C : N.toRot.dual.CutPath) (a : S.EndCopy) (φ : ℕ → ℕ∞)
    (hφ : ∀ r, r ≤ C.m → φ r ≤ C.m) {M : ℕ} (hM : C.m < M) :
    (⨅ r ∈ S.cutIdx C a, φ r) = ⊤ ∨ (⨅ r ∈ S.cutIdx C a, φ r) < M := by
  rcases ENat.iInf_top_or_le (B := (C.m : ℕ∞)) (g := fun r => ⨅ (_ : r ∈ S.cutIdx C a), φ r)
    (fun r => ENat.iInf_top_or_le fun hr => .inr (hφ r hr.1)) with h | h
  · exact .inl h
  · exact .inr (h.trans_lt (by exact_mod_cast hM))

end RData

end RotSystem

end SsspFlow
