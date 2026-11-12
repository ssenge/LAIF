import SsspFlow.GHatChainStep

/-!
# The step on a parent chain from flags at the nodes

A piece lies at a copy `p_t^σ` of the cut path if a dart at its vertex lies, in the cut, at the
vertex of a corner `p_t^σ` (`RData.CopyPiece`); this is the `σ` part of the indices `RData.cutIdx`.
The tail of the dart of a token lies at a copy `p_t^σ` exactly when its piece does, and its head
exactly when the piece of the partner does. A token edge of the network of a level joins the copy of
its token to the copy of the partner.

On the parent chain of a target, flag a node when the piece of its copy lies at a copy `p_t^σ`. The
first node flagged for `σ = 0` going up from the target, and the last node flagged for `σ = 1` below
it, bound the darts of a step.

* `RData.atCopy_tokDart_iff`, `RData.atCopy_head_tokDart_iff`: the tail and the head of the dart of a
  token at the copies of the cut path.
* `RData.hdTok_ends`, `RData.edgeTok_ends`: the ends of a token edge of finite length.
* `RData.chain_step_flags`: the darts of the chain edges between the first node flagged for `0` and
  the last node below it flagged for `1` are exactly the darts of a step.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

section Flags

variable {E : Type} [Fintype E] [DecidableEq E] {G : RotSystem E} (S : G.RData)

/-- A piece lies at a copy `p_t^σ` of the cut path: a dart at its vertex lies, in the cut, at the
vertex of a corner `p_t^σ` with `t ≤ m`. -/
def CopyPiece (C : G.dual.CutPath) (σ : Fin 2) (P : S.Piece) : Prop :=
  ∃ t, t ≤ C.m ∧ ∃ z, S.dualSplit.tail z = S.vertexEquiv P ∧ C.cut.tail z = C.cut.tail (C.k σ t)

/-- The tail of the dart of a token lies at a copy `p_t^σ` exactly when its piece does. -/
theorem atCopy_tokDart_iff {C : G.dual.CutPath} {Γ : Finset (E × Bool)} (hCΓ : C.Γ ⊆ Γ)
    (hCS : C.Γ ⊆ S.Γ) (σ : Fin 2) (x : S.Tok) :
    C.atCopy Γ σ ((G.dual.double.split Γ).tail (G.tokDart x.1)) ↔ S.CopyPiece C σ (S.piece x) := by
  rw [C.atCopy_tail hCΓ]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, G.tokDart x.1, (S.vertexEquiv_piece x).symm, (C.cut.tail_eq_iff _ _).2 h⟩
  · rintro ⟨t, ht, z, hz, hc⟩
    have h1 : fconnect S.dualSplit.rot z (G.tokDart x.1) :=
      (S.dualSplit.tail_eq_iff _ _).1 (hz.trans (S.vertexEquiv_piece x))
    have h2 : fconnect C.cut.rot z (G.tokDart x.1) := fconnect_of_split_subset (R := G.dual) hCS h1
    exact ⟨t, ht, connect_trans (fconnect_symm h2) ((C.cut.tail_eq_iff _ _).1 hc)⟩

/-- The head of the dart of a token lies at a copy `p_t^σ` exactly when the piece of the partner
does. -/
theorem atCopy_head_tokDart_iff {C : G.dual.CutPath} {Γ : Finset (E × Bool)} (hCΓ : C.Γ ⊆ Γ)
    (hCS : C.Γ ⊆ S.Γ) (σ : Fin 2) (x : S.Tok) :
    C.atCopy Γ σ ((G.dual.double.split Γ).head (G.tokDart x.1)) ↔
      S.CopyPiece C σ (S.piece (S.partnerTok x)) := by
  have e : (G.dual.double.split Γ).head (G.tokDart x.1) =
      (G.dual.double.split Γ).tail (S.dualSplit.rev (G.tokDart x.1)) := rfl
  have hv : S.dualSplit.tail (S.dualSplit.rev (G.tokDart x.1)) = S.vertexEquiv (S.piece (S.partnerTok x)) :=
    S.head_tokDart x
  rw [e, C.atCopy_tail hCΓ]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, _, hv, (C.cut.tail_eq_iff _ _).2 h⟩
  · rintro ⟨t, ht, z, hz, hc⟩
    have h1 : fconnect S.dualSplit.rot z (S.dualSplit.rev (G.tokDart x.1)) :=
      (S.dualSplit.tail_eq_iff _ _).1 (hz.trans hv.symm)
    have h2 : fconnect C.cut.rot z (S.dualSplit.rev (G.tokDart x.1)) :=
      fconnect_of_split_subset (R := G.dual) hCS h1
    exact ⟨t, ht, connect_trans (fconnect_symm h2) ((C.cut.tail_eq_iff _ _).1 hc)⟩

end Flags

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ)

/-- The ends of a kept dart of the repaired graph with a token: its node lies at the copy of the
token, the node of its reverse at the copy of the partner. -/
theorem hdTok_ends {d : S.HD} {x : S.Tok} (he : S.hdTok d = some x) (hk : d ∈ S.keep) :
    S.IsEnd x.1 (S.copyAt hN ((S.levelPad hN).ι (.inr d))) ∧
      S.IsEnd (S.partnerTok x).1 (S.copyAt hN ((S.levelPad hN).ι (.inr (S.hrev d)))) := by
  obtain ⟨he', b⟩ := d
  have hkK : S.Keep he' := by simpa [keep] using hk
  cases he' with
  | rim d₀ =>
    obtain ⟨k1, k2⟩ := S.att_rimTok hkK
    rw [S.copyAt_ι, S.copyAt_ι]
    cases b
    · obtain rfl : S.rimTok d₀ = x := Option.some.inj he
      refine ⟨?_, ?_⟩
      · show S.IsEnd (S.rimTok d₀).1 (S.alphaD (N.toRot.tailCorner d₀))
        rw [← k1]; exact S.isEnd_att _
      · show S.IsEnd (N.toRot.partner (S.rimTok d₀).1) (S.betaD d₀)
        rw [← k2]; exact S.isEnd_att _
    · obtain rfl : S.partnerTok (S.rimTok d₀) = x := Option.some.inj he
      refine ⟨?_, ?_⟩
      · show S.IsEnd (N.toRot.partner (S.rimTok d₀).1) (S.betaD d₀)
        rw [← k2]; exact S.isEnd_att _
      · show S.IsEnd (N.toRot.partner (N.toRot.partner (S.rimTok d₀).1)) (S.alphaD (N.toRot.tailCorner d₀))
        rw [N.toRot.partner_partner, ← k1]; exact S.isEnd_att _
  | sp _ | lsp _ | rsp _ | xsp _ | tok _ => simp [hdTok] at he

/-- The ends of a token edge of finite length of the network of a level: its first node lies at the
copy of the token, its second at the copy of the partner. -/
theorem edgeTok_ends {y y' : Fin (n * (n * 21))} {x : S.Tok} (he : S.edgeTok hN y y' = some x)
    (hf : S.levelLen hN lam M y y' ≠ ⊤) :
    S.IsEnd x.1 (S.copyAt hN y) ∧ S.IsEnd (S.partnerTok x).1 (S.copyAt hN y') := by
  classical
  unfold edgeTok at he
  split_ifs at he with h
  obtain ⟨e1, e2⟩ := h.choose_spec
  generalize h.choose = d at he e1 e2
  subst e1 e2
  have hk : d ∈ S.keep := by
    by_contra hk
    exact hf (by rw [S.levelLen_ι]; simp [hk])
  exact S.hdTok_ends hN he hk

/-- A node of the parent chain of the copy node of `v`, `i` steps above it, is flagged for `σ` when
the piece of its copy lies at a copy `p_t^σ`. -/
def chainFlag (C : N.toRot.dual.CutPath) (r : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (v : S.hRot.Vertex) (σ : Fin 2) (i : ℕ) : Prop :=
  ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN ((Net.parOf r)^[i] ((S.levelPad hN).ι (.inl v))))),
    S.CopyPiece C σ (S.pieceOf ⟨_, hy⟩)

/-- **The step on a parent chain from flags at the nodes.** Under the conditions of
`RData.chain_step` on the chain of a target, without the two nodes: let `ia` be the first node going
up from the target that is flagged for `0`, and `iy ≤ ia` the last node below it flagged for `1`.
Then the darts of the tokens of the chain edges between them are exactly the darts of a step. -/
theorem chain_step_flags {C : N.toRot.dual.CutPath} {Γ : Finset (N.G.Dart × Bool)}
    (hR : N.toRot.dual.Planar) (hC : N.toRot.dual.Connected) (c : N.G.Dart → ℕ) (hc1 : ∀ d, 1 ≤ c d)
    (hcr : ∀ d, c (N.toRot.rev d) = c d) (hlam : ∀ x, lam x = c x.1.1)
    (L : C.Live (Nat.cast ∘ c) Γ) (hS : Γ ⊆ S.Γ) {t : ℕ}
    (hz : ∀ w ∈ S.Γ, w ∉ Γ → ∀ p, ¬ (N.toRot.dual.double.split Γ).IsWalk
      ((N.toRot.dual.double.split Γ).tail (L.κ0 t)) p ((N.toRot.dual.double.split Γ).tail w))
    (h1 : L.xa ≤ t) (h2 : L.ya ≤ t) (h3 : t ≤ L.xb) (h4 : t ≤ L.yb)
    (ψ : Fin (n * (n * 21)) → ℕ∞) (r : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) ψ r)
    {u v : S.hRot.Vertex} {k : ℕ}
    (hs : Net.ParSteps r ((S.levelPad hN).ι (.inl v)) k)
    (hroot : (Net.parOf r)^[k] ((S.levelPad hN).ι (.inl v)) = (S.levelPad hN).ι (.inl u))
    (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)) (hv : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v))
    (hpu : S.pieceOf ⟨S.vcopy u, hu⟩ = S.pieceAt (L.κ0 t))
    (hpv : S.pieceOf ⟨S.vcopy v, hv⟩ = S.pieceAt (L.κ1 t))
    (hlt : ((∑ l ∈ Finset.range k, S.levelLen hN lam M ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
      ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) : ℕ∞) : ℝ≥0∞) < M)
    (hle : ((∑ l ∈ Finset.range k, S.levelLen hN lam M ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
      ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) : ℕ∞) : ℝ≥0∞) ≤ C.lamD (Nat.cast ∘ c) t) :
    ∃ ia iy : ℕ, iy ≤ ia ∧ ia ≤ k ∧ S.chainFlag hN C r v 0 ia ∧ (∀ l < ia, ¬ S.chainFlag hN C r v 0 l) ∧
      S.chainFlag hN C r v 1 iy ∧ (∀ l, iy < l → l ≤ ia → ¬ S.chainFlag hN C r v 1 l) ∧
      ∃ St : L.Step, ∀ z, z ∈ (List.range St.n).map St.q ↔ ∃ l, iy ≤ l ∧ l < ia ∧ ∃ x,
        S.edgeTok hN ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
          ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) = some x ∧ z = N.toRot.tokDart x.1 := by
  classical
  have hCS : C.Γ ⊆ S.Γ := L.sub.trans hS
  have hfin : ∀ l < k, S.levelLen hN lam M ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v)))
      ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))) ≠ ⊤ := fun l hl e => by
    have htop := top_le_iff.1 (e ▸ Finset.single_le_sum (f := fun l => S.levelLen hN lam M
      ((Net.parOf r)^[l + 1] ((S.levelPad hN).ι (.inl v))) ((Net.parOf r)^[l] ((S.levelPad hN).ι (.inl v))))
      (fun i _ => zero_le) (Finset.mem_range.2 hl))
    rw [htop] at hlt
    simp at hlt
  have hroot0 : S.chainFlag hN C r v 0 k := by
    have hz₁ : ∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN ((S.levelPad hN).ι (.inl u))) := by
      rw [S.copyAt_ι]; exact hu
    have e : S.pieceOf ⟨_, hz₁⟩ = S.pieceOf ⟨S.vcopy u, hu⟩ :=
      congrArg S.pieceOf (Subtype.ext (S.copyAt_ι hN _))
    unfold chainFlag
    rw [hroot]
    refine ⟨hz₁, ?_⟩
    rw [e, hpu]
    exact ⟨t, h3.trans L.xb_le, L.κ0 t, (S.vertexEquiv_pieceAt _).symm,
      (C.cut.tail_eq_iff _ _).2 (L.piece0 t h1 h3)⟩
  have hv1 : S.chainFlag hN C r v 1 0 := by
    have hz₂ : ∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN ((S.levelPad hN).ι (.inl v))) := by
      rw [S.copyAt_ι]; exact hv
    have e : S.pieceOf ⟨_, hz₂⟩ = S.pieceOf ⟨S.vcopy v, hv⟩ :=
      congrArg S.pieceOf (Subtype.ext (S.copyAt_ι hN _))
    refine ⟨hz₂, ?_⟩
    show S.CopyPiece C 1 (S.pieceOf ⟨S.copyAt hN ((S.levelPad hN).ι (.inl v)), hz₂⟩)
    rw [e, hpv]
    exact ⟨t, h4.trans L.yb_le, L.κ1 t, (S.vertexEquiv_pieceAt _).symm,
      (C.cut.tail_eq_iff _ _).2 (L.piece1 t h2 h4)⟩
  have hex : ∃ i, i ≤ k ∧ S.chainFlag hN C r v 0 i := ⟨k, le_rfl, hroot0⟩
  obtain ⟨ia, ⟨hak, hA0⟩, hmin⟩ : ∃ ia, (ia ≤ k ∧ S.chainFlag hN C r v 0 ia) ∧
      ∀ l < ia, ¬ S.chainFlag hN C r v 0 l :=
    ⟨Nat.find hex, Nat.find_spec hex, fun l hl hF =>
      Nat.find_min hex hl ⟨by have := (Nat.find_spec hex).1; omega, hF⟩⟩
  obtain ⟨iy, hA1, hya, hmax⟩ : ∃ iy, S.chainFlag hN C r v 1 iy ∧ iy ≤ ia ∧
      ∀ l, iy < l → l ≤ ia → ¬ S.chainFlag hN C r v 1 l :=
    ⟨Nat.findGreatest (S.chainFlag hN C r v 1) ia, Nat.findGreatest_spec (Nat.zero_le ia) hv1,
      Nat.findGreatest_le ia, fun l h1 h2 => Nat.findGreatest_is_greatest h1 h2⟩
  obtain ⟨hya0, hc0⟩ := hA0
  obtain ⟨hyb1, hc1'⟩ := hA1
  have hs0 : C.atCopy Γ 0 ((N.toRot.dual.double.split Γ).tail (N.toRot.tokDart hya0.choose.1)) := by
    rw [S.atCopy_tokDart_iff L.sub hCS, ← S.pieceOf_eq ⟨_, hya0⟩ hya0.choose_spec]
    exact hc0
  have hs1 : C.atCopy Γ 1 ((N.toRot.dual.double.split Γ).tail (N.toRot.tokDart hyb1.choose.1)) := by
    rw [S.atCopy_tokDart_iff L.sub hCS, ← S.pieceOf_eq ⟨_, hyb1⟩ hyb1.choose_spec]
    exact hc1'
  obtain ⟨St, hSt⟩ := S.chain_step hN lam M hR hC c hc1 hcr hlam L hS hz h1 h2 h3 h4 ψ r hr hya hak hs hroot
    hu hv hpu hpv hlt hle hya0.choose hyb1.choose hya0.choose_spec hyb1.choose_spec hs0 hs1
    (fun l hl x he hcp => by
      rw [S.atCopy_head_tokDart_iff L.sub hCS] at hcp
      have hend := (S.edgeTok_ends hN lam M he (hfin l (by omega))).2
      exact hmin l hl ⟨⟨_, hend⟩, by rw [S.pieceOf_eq ⟨_, ⟨_, hend⟩⟩ hend]; exact hcp⟩)
    (fun l hl1 hl2 x he hcp => by
      rw [S.atCopy_tokDart_iff L.sub hCS] at hcp
      have hend := (S.edgeTok_ends hN lam M he (hfin l (by omega))).1
      exact hmax (l + 1) (by omega) (by omega) ⟨⟨_, hend⟩, by rw [S.pieceOf_eq ⟨_, ⟨_, hend⟩⟩ hend]; exact hcp⟩)
  exact ⟨ia, iy, hya, hak, ⟨hya0, hc0⟩, hmin, ⟨hyb1, hc1'⟩, hmax, St, hSt⟩

end RData

end RotSystem

end SsspFlow
