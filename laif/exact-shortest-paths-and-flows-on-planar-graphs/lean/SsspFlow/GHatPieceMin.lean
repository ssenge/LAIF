import SsspFlow.GHatLevelMin
import SsspFlow.GHatLevelStep
import SsspFlow.GHatChainFlags

/-!
# Least values over the pieces of a level

The indices of the cut path at the piece of a copy (`RData.cutIdx`) are those of the corners at the
vertex of the piece. Every such corner is the corner of a token with an end at a copy of the piece, and
the copies of a piece are joined by E_R edges. So the least value over the indices at the piece of a
copy is the least value over the copies joined to it by E_R edges of a value of the copy, read from
the tokens that end there and the indices of their corners. With token lengths `M`, only the E_R arcs
have length `0`, so one run of the oracle computes these least values, capped at `M`.

* `RData.er_pieceOf`: copies joined by E_R edges lie in one piece.
* `RData.copyVal`: the least value over the corners of the tokens that end at a copy.
* `RData.pieceMin_eq`: the least value over the corners at the vertex of the piece of a copy is the
  least value of `copyVal` over the copies joined to it by E_R edges.
* `RData.cornerIdx`, `RData.cutIdx_iInf`: the indices at the piece of a copy are those of its corners.
* `RData.cutIdx_pieceMin`: the least value over the indices at the piece of a copy, as a least value
  over the copies joined to it by E_R edges.
* `RData.levelPieceMin_local`: one algorithm of the message model that holds at every copy the least
  offset over the copies joined to it by E_R edges, capped at `M`.
* `ENat.uncap_eq`: a value `t` that is `⊤` or below `M` is recovered from its cap at `M`.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

/-- The value of `x` capped at `M` turned back: `⊤` from `M` on. -/
def ENat.uncap (M : ℕ) (x : ℕ∞) : ℕ∞ := if (M : ℕ∞) ≤ x then ⊤ else x

/-- **Uncapping.** A value `t` that is `⊤` or below `M` is recovered from a value with the same cap
at `M`. -/
theorem ENat.uncap_eq {x t : ℕ∞} {M : ℕ} (h : min (x : ℝ≥0∞) M = min (t : ℝ≥0∞) M)
    (ht : t = ⊤ ∨ t < M) : ENat.uncap M x = t := by
  have h' : min x (M : ℕ∞) = min t M := ENat.toENNReal_strictMono.injective (by
    rw [ENat.toENNReal_min, ENat.toENNReal_min, ENat.toENNReal_coe]
    exact h)
  unfold ENat.uncap
  split_ifs with hM
  · rcases ht with rfl | ht
    · rfl
    · rw [min_eq_right hM, min_eq_left ht.le] at h'
      exact absurd (h' ▸ ht) (lt_irrefl _)
  · have hxM : x ≤ M := le_of_lt (not_le.1 hM)
    rcases ht with rfl | ht
    · rw [min_eq_right le_top] at h'
      exact absurd (min_eq_right_iff.1 h') hM
    · rw [min_eq_left hxM, min_eq_left ht.le] at h'
      exact h'

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

/-- **Copies joined by E_R edges lie in one piece.** -/
theorem er_pieceOf {a b : Copy N.toRot.Vertex N.G.Dart} (h : Relation.ReflTransGen S.ER a b)
    (ha : ∃ x : S.Tok, S.IsEnd x.1 a) :
    ∃ hb : (∃ x : S.Tok, S.IsEnd x.1 b), S.pieceOf ⟨b, hb⟩ = S.pieceOf ⟨a, ha⟩ := by
  induction h with
  | refl => exact ⟨ha, rfl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨hb, e⟩ := ih
    obtain ⟨x, hx⟩ := hbc
    have hxb : S.IsEnd x.1 b := by
      rcases hx with hx | hx
      · exact .inl hx.1
      · exact .inr hx.1
    have hxc : S.IsEnd x.1 c := by
      rcases hx with hx | hx
      · exact .inr hx.2
      · exact .inl hx.2
    exact ⟨⟨x, hxc⟩, (S.pieceOf_eq ⟨_, ⟨x, hxc⟩⟩ hxc).trans ((S.pieceOf_eq ⟨_, hb⟩ hxb).symm.trans e)⟩

/-- The least value of `f` over the corners of the tokens that end at a copy. -/
def copyVal {α : Type} [CompleteLattice α] (f : N.G.Dart × Bool → α)
    (b : Copy N.toRot.Vertex N.G.Dart) : α :=
  ⨅ y : S.Tok, ⨅ (_ : S.IsEnd y.1 b), ⨅ z, ⨅ (_ : S.tokOf z = y.1), f z

/-- **The least value over a piece.** The least value of `f` over the corners at the vertex of the
piece of a copy is the least value of `copyVal f` over the copies joined to it by E_R edges. -/
theorem pieceMin_eq {α : Type} [CompleteLattice α] (f : N.G.Dart × Bool → α) (a : S.EndCopy) :
    ⨅ z, ⨅ (_ : S.pieceAt z = S.pieceOf a), f z =
      ⨅ u, ⨅ (_ : Relation.ReflTransGen S.ER (S.vcopy u) a.1), S.copyVal f (S.vcopy u) := by
  apply le_antisymm
  · refine le_iInf fun u => le_iInf fun hu => le_iInf fun y => le_iInf fun hy => le_iInf fun z =>
      le_iInf fun hz => iInf_le_of_le z (iInf_le_of_le ?_ le_rfl)
    obtain ⟨_, e⟩ := S.er_pieceOf hu ⟨y, hy⟩
    show S.piece ⟨S.tokOf z, S.isTok_tokOf z⟩ = S.pieceOf a
    rw [show (⟨S.tokOf z, S.isTok_tokOf z⟩ : S.Tok) = y from Subtype.ext hz,
      ← S.pieceOf_eq ⟨_, ⟨y, hy⟩⟩ hy]
    exact e.symm
  · refine le_iInf fun z => le_iInf fun hz => ?_
    have hring : Relation.ReflTransGen S.ER (S.vcopy (S.endV z)) a.1 := by
      refine S.ring_conn ⟨_, S.endV_end z⟩ a ?_
      rw [S.pieceOf_eq ⟨_, S.endV_end z⟩ (x := ⟨S.tokOf z, S.isTok_tokOf z⟩) (.inl rfl)]
      exact hz
    exact iInf_le_of_le (S.endV z) (iInf_le_of_le hring (iInf_le_of_le ⟨S.tokOf z, S.isTok_tokOf z⟩
      (iInf_le_of_le (.inl rfl) (iInf_le_of_le z (iInf_le_of_le rfl le_rfl)))))

/-- The indices `r ≤ m` of the corners `p_r^σ` at the vertex of a corner in the cut along `C`. -/
def cornerIdx (C : N.toRot.dual.CutPath) (z : N.G.Dart × Bool) : Set ℕ :=
  {r | r ≤ C.m ∧ ∃ σ, C.cut.tail z = C.cut.tail (C.k σ r)}

theorem tail_eq_vertexEquiv_iff (z : N.G.Dart × Bool) (P : S.Piece) :
    S.dualSplit.tail z = S.vertexEquiv P ↔ S.pieceAt z = P := by
  rw [← S.vertexEquiv_pieceAt z]
  exact S.vertexEquiv.injective.eq_iff

theorem mem_cutIdx (C : N.toRot.dual.CutPath) (a : S.EndCopy) (r : ℕ) :
    r ∈ S.cutIdx C a ↔ ∃ z, S.pieceAt z = S.pieceOf a ∧ r ∈ cornerIdx C z := by
  constructor
  · rintro ⟨hr, σ, z, hz, hc⟩
    exact ⟨z, (S.tail_eq_vertexEquiv_iff z _).1 hz, hr, σ, hc⟩
  · rintro ⟨z, hz, hr, σ, hc⟩
    exact ⟨hr, σ, z, (S.tail_eq_vertexEquiv_iff z _).2 hz, hc⟩

/-- **The indices at a piece are those of its corners.** -/
theorem cutIdx_iInf (C : N.toRot.dual.CutPath) (a : S.EndCopy) (φ : ℕ → ℕ∞) :
    ⨅ r ∈ S.cutIdx C a, φ r = ⨅ z, ⨅ (_ : S.pieceAt z = S.pieceOf a), ⨅ r ∈ cornerIdx C z, φ r := by
  apply le_antisymm
  · exact le_iInf fun z => le_iInf fun hz => le_iInf fun r => le_iInf fun hr =>
      iInf_le_of_le r (iInf_le_of_le ((S.mem_cutIdx C a r).2 ⟨z, hz, hr⟩) le_rfl)
  · refine le_iInf fun r => le_iInf fun hr => ?_
    obtain ⟨z, hz, hr'⟩ := (S.mem_cutIdx C a r).1 hr
    exact iInf_le_of_le z (iInf_le_of_le hz (iInf_le_of_le r (iInf_le_of_le hr' le_rfl)))

/-- **The least value over the indices at a piece, by E_R edges.** For a copy `u` on E_R edges, the
least value of `φ` over the indices of the cut path at its piece is the least value, over the copies
joined to it by E_R edges, of the least value of `φ` over the indices of the corners of the tokens
that end there. -/
theorem cutIdx_pieceMin (C : N.toRot.dual.CutPath) (φ : ℕ → ℕ∞) (u : S.hRot.Vertex)
    (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)) :
    ⨅ r ∈ S.cutIdx C ⟨S.vcopy u, hu⟩, φ r = ⨅ u', ⨅ (_ : Relation.ReflTransGen S.ER (S.vcopy u') (S.vcopy u)),
      S.copyVal (fun z => ⨅ r ∈ cornerIdx C z, φ r) (S.vcopy u') := by
  exact (S.cutIdx_iInf C ⟨S.vcopy u, hu⟩ φ).trans (S.pieceMin_eq _ ⟨S.vcopy u, hu⟩)

/-- The values at the copies of the vertices, `⊤` elsewhere. -/
noncomputable def onCopies (f : S.hRot.Vertex → ℕ∞) (z : Fin (n * (n * 21))) : ℕ∞ :=
  ⨅ u, ⨅ (_ : (S.levelPad hN).ι (.inl u) = z), f u

theorem onCopies_copy (f : S.hRot.Vertex → ℕ∞) (u : S.hRot.Vertex) :
    S.onCopies hN f ((S.levelPad hN).ι (.inl u)) = f u :=
  le_antisymm (iInf_le_of_le u (iInf_le_of_le rfl le_rfl))
    (le_iInf fun u' => le_iInf fun h => by
      obtain rfl := Sum.inl_injective ((S.levelPad hN).ι_injective h)
      exact le_rfl)

theorem onCopies_other (f : S.hRot.Vertex → ℕ∞) (z : Fin (n * (n * 21)))
    (hz : ∀ u, z ≠ (S.levelPad hN).ι (.inl u)) : S.onCopies hN f z = ⊤ :=
  le_antisymm le_top (le_iInf fun u => le_iInf fun h => absurd h.symm (hz u))

/-- **Least offsets of the pieces, from local inputs.** Assuming the Exact SSSP bound, one algorithm of
the message model on `N`, fixed before the network, starts from the inputs of a level with all token
lengths set to `M ≥ 1` and, at each node, offsets that agree with `ψ` at the identifiers it hosts.
After `C log^c n' · (12 D + 16) + 1` rounds it holds at every copy the least offset of the copies
joined to it by E_R edges, capped at `M`. -/
theorem levelPieceMin_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (LevelIn n × (Fin (n * (n * 21)) → ℕ∞)) σ
      (4 * (C * logN (n * (n * 21)) ^ c) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (out : Fin (n * (n * 21)) → σ → ℕ∞),
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (lam : S.Tok → ℕ) (M : ℕ)
      (u₀ : S.hRot.Vertex) (ψ : Fin (n * (n * 21)) → ℕ∞) (off : Fin n → Fin (n * (n * 21)) → ℕ∞),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      1 ≤ M → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ z, (∀ u, z ≠ (S.levelPad hN).ι (.inl u)) → ψ z = ⊤) →
      (∀ z, ψ z = ⊤ ∨ ψ z ≤ (n * (n * 21) + 2) ^ K) →
      (∀ a, off (hostOf a) a = ψ a) →
      ∀ v : S.hRot.Vertex,
        min (out ((S.levelPad hN).ι (.inl v))
          (A.run N.G (fun w => ((S.levelIn hN lam M u₀ w).withConst M, off w))
            (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16)) (hostOf ((S.levelPad hN).ι (.inl v)))) : ℝ≥0∞) M =
          min (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ER (S.vcopy u) (S.vcopy v)),
            (ψ ((S.levelPad hN).ι (.inl u)) : ℝ≥0∞)) M := by
  obtain ⟨C, c, hC⟩ := levelSsspOff_local hE K
  refine ⟨C, c, fun n D => ?_⟩
  obtain ⟨σ, A, out, hA⟩ := hC n D
  refine ⟨σ, A, out, fun N S hN lam M u₀ ψ off hP hc hS hcut hD hM1 hM hψ hψW hoff v => ?_⟩
  have e : (fun w => ((S.levelIn hN lam M u₀ w).withConst M, off w)) =
      fun w => (S.levelIn hN (fun _ => M) M u₀ w, off w) :=
    funext fun w => by rw [S.levelIn_const hN lam M M u₀ w]
  rw [e, hA N S hN (fun _ => M) M u₀ ψ off hP hc hS hcut hD (fun _ => hM) hM hψ hψW hoff v,
    S.zmin_cap (fun _ => M) M (fun _ => Or.inr le_rfl) (fun u => ψ ((S.levelPad hN).ι (.inl u))) v,
    S.zr_const hM1]

end RData

end RotSystem

end SsspFlow
