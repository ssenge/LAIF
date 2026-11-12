import SsspFlow.GHatLevelRoots

/-!
# The darts of a walk of a level, in order

A rim dart of the repaired graph is an E_C arc of `Ĝ_ℓ` with the token `rimTok d` forwards and its
partner backwards; a token dart stays at one piece, and a spoke costs `M`. So a walk of the network
of a level of length below `M` gives, edge by edge, the darts of the split of the doubled dual at
the tokens of its E_C arcs (`RData.levelDarts`), and these form a walk of the split between the
pieces of its ends, of the same length.

* `RData.att_rimTok`: the ends of a kept rim dart are the copies of its token and of the partner.
* `RData.edgeTok_dart`, `RData.edgeTok_inl_left`, `RData.edgeTok_inl_right`: the token of an edge of
  the network of a level.
* `RData.levelDarts_walk`: the darts of a walk of the network of a level below `M` between copies
  on E_R edges form a walk of the split between their pieces, with the sum of the costs as length.
* `RData.level_shortest_darts`: for such a walk between the pieces at `κ0(t)` and `κ1(t)` of length at
  most `λ_t`, these darts form a shortest walk of the annulus.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

section Rim

variable {E : Type} [Fintype E] [DecidableEq E] {G : RotSystem E} (S : G.RData)

/-- The ends of a kept rim dart are the copies of its token and of the partner. -/
theorem att_rimTok {d : E} (hx : S.Keep (.rim d)) :
    S.att (S.rimTok d).1 = S.alphaD (G.tailCorner d) ∧ S.att (G.partner (S.rimTok d).1) = S.betaD d := by
  simp only [Keep] at hx
  by_cases hd : d ∈ S.inc
  · simp only [rimTok, hd, dite_true]
    exact S.att_of_atTail (x := (d, .one)) (S.isTok_one hd) rfl
  · have hh : S.hostT d = true := by simpa [hd] using hx
    simp only [rimTok, hd, dite_false]
    exact S.att_of_atTail (x := (d, .zero)) (S.isTok_zero hd) hh

/-- The token of the E_C arc of a dart of the repaired graph. -/
def hdTok : S.HD → Option S.Tok
  | (.rim d, false) => some (S.rimTok d)
  | (.rim d, true) => some (S.partnerTok (S.rimTok d))
  | _ => none

end Rim

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ)

open Classical in
/-- The token of an edge of the network of a level: the token of the E_C arc of a middle edge of a
dart, and none otherwise. -/
noncomputable def edgeTok (y y' : Fin (n * (n * 21))) : Option S.Tok :=
  if h : ∃ d : S.HD, y = (S.levelPad hN).ι (.inr d) ∧ y' = (S.levelPad hN).ι (.inr (S.hrev d)) then
    S.hdTok h.choose else none

theorem edgeTok_dart (d : S.HD) :
    S.edgeTok hN ((S.levelPad hN).ι (.inr d)) ((S.levelPad hN).ι (.inr (S.hrev d))) = S.hdTok d := by
  have h : ∃ d' : S.HD, (S.levelPad hN).ι (.inr d) = (S.levelPad hN).ι (.inr d') ∧
      (S.levelPad hN).ι (.inr (S.hrev d)) = (S.levelPad hN).ι (.inr (S.hrev d')) := ⟨d, rfl, rfl⟩
  unfold edgeTok
  rw [dif_pos h]
  have e := Sum.inr_injective ((S.levelPad hN).ι_injective h.choose_spec.1)
  rw [← e]

theorem edgeTok_inl_left (v : S.hRot.Vertex) (y : Fin (n * (n * 21))) :
    S.edgeTok hN ((S.levelPad hN).ι (.inl v)) y = none := by
  unfold edgeTok
  rw [dif_neg]
  rintro ⟨d, h, -⟩
  exact Sum.inl_ne_inr ((S.levelPad hN).ι_injective h)

theorem edgeTok_inl_right (v : S.hRot.Vertex) (y : Fin (n * (n * 21))) :
    S.edgeTok hN y ((S.levelPad hN).ι (.inl v)) = none := by
  unfold edgeTok
  rw [dif_neg]
  rintro ⟨d, -, h⟩
  exact Sum.inl_ne_inr ((S.levelPad hN).ι_injective h)

/-- The darts of the split at the tokens of the E_C arcs of a walk of the network of a level. -/
noncomputable def levelDarts : ∀ {z z' : Fin (n * (n * 21))},
    SsspFlow.Walk (S.levelNet hN).G.Adj z z' → List (N.G.Dart × Bool)
  | _, _, .nil _ => []
  | a, _, .cons (b := b) _ p =>
    ((S.edgeTok hN a b).map fun x => N.toRot.tokDart x.1).toList ++ levelDarts p

theorem levelDarts_cons {a b z' : Fin (n * (n * 21))} (e : (S.levelNet hN).G.Adj a b)
    (p : SsspFlow.Walk (S.levelNet hN).G.Adj b z') :
    S.levelDarts hN (.cons e p) = ((S.edgeTok hN a b).map fun x => N.toRot.tokDart x.1).toList ++
      S.levelDarts hN p := rfl

/-- **The darts of a walk of a level, in order.** For token lengths that are the costs `c` of their
darts, the darts of a walk of the network of a level of length below `M` between copies on E_R
edges form a walk of the split between their pieces, and the sum of their costs is its length. -/
theorem levelDarts_walk (c : N.G.Dart → ℕ) (hcr : ∀ d, c (N.toRot.rev d) = c d)
    (hlam : ∀ x, lam x = c x.1.1) : ∀ {z z' : Fin (n * (n * 21))}
    (p : SsspFlow.Walk (S.levelNet hN).G.Adj z z') (hz : ∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN z))
    (hz' : ∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN z')),
    p.wt (lenTop (S.levelLen hN lam M)) < M →
    S.dualSplit.IsWalk (S.vertexEquiv (S.pieceOf ⟨S.copyAt hN z, hz⟩)) (S.levelDarts hN p)
        (S.vertexEquiv (S.pieceOf ⟨S.copyAt hN z', hz'⟩)) ∧
      ((S.levelDarts hN p).map fun d => (c d.1 : ℝ≥0∞)).sum = p.wt (lenTop (S.levelLen hN lam M))
  | _, _, .nil z, hz, hz', _ => by
    refine ⟨?_, by simp [levelDarts, SsspFlow.Walk.wt]⟩
    simp only [levelDarts]
    exact congrArg S.vertexEquiv (S.pieceOf_eq _ hz'.choose_spec)
  | z, z', .cons (b := y) e p, hz, hz', hlt => by
    classical
    rw [SsspFlow.Walk.wt_cons] at hlt
    have hle1 : lenTop (S.levelLen hN lam M) z y < M := lt_of_le_of_lt le_self_add hlt
    have hle2 : p.wt (lenTop (S.levelLen hN lam M)) < M := lt_of_le_of_lt le_add_self hlt
    have ih := fun hy => levelDarts_walk c hcr hlam p hy hz' hle2
    have hf : S.levelLen hN lam M z y ≠ ⊤ := fun h0 => by
      simp [lenTop, h0] at hle1
    -- the same piece: no dart, the rest of the walk
    have same : ∀ (hy : ∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)),
        S.pieceOf ⟨S.copyAt hN y, hy⟩ = S.pieceOf ⟨S.copyAt hN z, hz⟩ →
        S.edgeTok hN z y = none → S.levelLen hN lam M z y = 0 →
        S.dualSplit.IsWalk (S.vertexEquiv (S.pieceOf ⟨S.copyAt hN z, hz⟩))
          (S.levelDarts hN (.cons e p)) (S.vertexEquiv (S.pieceOf ⟨S.copyAt hN z', hz'⟩)) ∧
        ((S.levelDarts hN (.cons e p)).map fun d => (c d.1 : ℝ≥0∞)).sum =
          (lenTop (S.levelLen hN lam M) z y + p.wt (lenTop (S.levelLen hN lam M))) := by
      intro hy hp ht h0
      obtain ⟨h1, h2⟩ := ih hy
      rw [levelDarts_cons, ht, hp] at *
      refine ⟨by simpa using h1, ?_⟩
      simp [h2, lenTop, h0]
    rcases padNet_adj_cases e with ⟨x, x', rfl, rfl, hxy⟩ | ⟨hb, -⟩ | ⟨ha, -⟩
    · rw [S.levelLen_ι] at hf
      rcases x with v | d <;> rcases x' with w | d'
      · exact absurd hf (by simp)
      · obtain rfl : S.hRot.tail d' = v := hxy
        have hc : S.copyAt hN ((S.levelPad hN).ι (.inr d')) = S.copyAt hN ((S.levelPad hN).ι (.inl (S.hRot.tail d'))) := by
          rw [S.copyAt_ι, S.copyAt_ι]; rfl
        have hy : ∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN ((S.levelPad hN).ι (.inr d'))) := by
          rw [hc]; exact hz
        refine same hy ?_ (S.edgeTok_inl_left hN _ _) (by rw [S.levelLen_ι])
        refine (S.pieceOf_eq _ ?_).trans (S.pieceOf_eq _ hz.choose_spec).symm
        change S.IsEnd _ (S.copyAt hN _); rw [hc]; exact hz.choose_spec
      · obtain rfl : S.hRot.tail d = w := hxy
        have hc : S.copyAt hN ((S.levelPad hN).ι (.inl (S.hRot.tail d))) = S.copyAt hN ((S.levelPad hN).ι (.inr d)) := by
          rw [S.copyAt_ι, S.copyAt_ι]; rfl
        have hy : ∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN ((S.levelPad hN).ι (.inl (S.hRot.tail d)))) := by
          rw [hc]; exact hz
        refine same hy ?_ (S.edgeTok_inl_right hN _ _) (by rw [S.levelLen_ι])
        refine (S.pieceOf_eq _ ?_).trans (S.pieceOf_eq _ hz.choose_spec).symm
        change S.IsEnd _ (S.copyAt hN _); rw [hc]; exact hz.choose_spec
      · obtain rfl : d' = S.hRot.rev d := hxy
        have hrv : S.hRot.rev d = S.hrev d := rfl
        by_cases hk : d ∈ S.keep
        swap
        · exact absurd hf (by simp [hk, hrv])
        have hlen : S.levelLen hN lam M ((S.levelPad hN).ι (.inr d)) ((S.levelPad hN).ι (.inr (S.hRot.rev d))) =
            S.dartW lam M d := by
          rw [S.levelLen_ι]; simp [hk, hrv]
        have hkK : S.Keep d.1 := by simpa [keep] using hk
        obtain ⟨he, b⟩ := d
        cases he with
        | tok x =>
          have hy : ∃ y : S.Tok, S.IsEnd y.1 (S.copyAt hN ((S.levelPad hN).ι (.inr (S.hRot.rev (HE.tok x, b))))) := by
            rw [S.copyAt_ι]
            cases b
            · exact ⟨x, .inr rfl⟩
            · exact ⟨x, .inl rfl⟩
          have hzx : S.IsEnd x.1 (S.copyAt hN ((S.levelPad hN).ι (.inr (HE.tok x, b)))) := by
            rw [S.copyAt_ι]
            cases b
            · exact .inl rfl
            · exact .inr rfl
          have hyx : S.IsEnd x.1 (S.copyAt hN ((S.levelPad hN).ι (.inr (S.hRot.rev (HE.tok x, b))))) := by
            rw [S.copyAt_ι]
            cases b
            · exact .inr rfl
            · exact .inl rfl
          refine same hy ((S.pieceOf_eq _ hyx).trans (S.pieceOf_eq _ hzx).symm)
            ((S.edgeTok_dart hN _).trans rfl) (by rw [hlen]; rfl)
        | rim d₀ =>
          obtain ⟨k1, k2⟩ := S.att_rimTok hkK
          -- the token of the E_C arc and its ends
          set x : S.Tok := if b then S.partnerTok (S.rimTok d₀) else S.rimTok d₀ with hx
          have htok : S.hdTok (HE.rim d₀, b) = some x := by cases b <;> rfl
          have hzx : S.IsEnd x.1 (S.copyAt hN ((S.levelPad hN).ι (.inr (HE.rim d₀, b)))) := by
            rw [S.copyAt_ι]
            cases b
            · show S.IsEnd (S.rimTok d₀).1 (S.alphaD (N.toRot.tailCorner d₀))
              rw [← k1]; exact S.isEnd_att _
            · show S.IsEnd (N.toRot.partner (S.rimTok d₀).1) (S.betaD d₀)
              rw [← k2]; exact S.isEnd_att _
          have hyx : S.IsEnd (S.partnerTok x).1
              (S.copyAt hN ((S.levelPad hN).ι (.inr (S.hRot.rev (HE.rim d₀, b))))) := by
            rw [S.copyAt_ι]
            cases b
            · show S.IsEnd (N.toRot.partner (S.rimTok d₀).1) (S.betaD d₀)
              rw [← k2]; exact S.isEnd_att _
            · show S.IsEnd (N.toRot.partner (N.toRot.partner (S.rimTok d₀).1)) (S.alphaD (N.toRot.tailCorner d₀))
              rw [N.toRot.partner_partner, ← k1]; exact S.isEnd_att _
          obtain ⟨h1, h2⟩ := ih ⟨_, hyx⟩
          have hE : S.edgeTok hN ((S.levelPad hN).ι (.inr (HE.rim d₀, b)))
              ((S.levelPad hN).ι (.inr (S.hRot.rev (HE.rim d₀, b)))) = some x :=
            (S.edgeTok_dart hN _).trans htok
          rw [levelDarts_cons, hE]
          have hpz : S.pieceOf ⟨_, hz⟩ = S.piece x := S.pieceOf_eq _ hzx
          have hpy : S.pieceOf ⟨_, ⟨_, hyx⟩⟩ = S.piece (S.partnerTok x) := S.pieceOf_eq _ hyx
          refine ⟨(S.dualSplit.isWalk_cons _ _ _ _).2 ⟨?_, ?_⟩, ?_⟩
          · rw [hpz]; exact (S.vertexEquiv_piece x).symm
          · rw [S.head_tokDart, ← hpy]; exact h1
          · simp only [Option.map_some, Option.toList_some, List.singleton_append, List.map_cons,
              List.sum_cons, h2, N.toRot.tokDart_fst, hcr]
            congr 1
            rw [lenTop, hlen]
            cases b
            · simp [hx, dartW, hlam]
            · simp [hx, dartW, hlam, partnerTok]
        | sp _ | lsp _ | rsp _ | xsp _ =>
          exfalso
          rw [lenTop, hlen] at hle1
          cases b <;> simp [dartW] at hle1
    · exact absurd (by unfold levelLen; exact ite_eq_right_iff.2 (fun h' => absurd h'.1 hb)) hf
    · exact absurd (by unfold levelLen; exact ite_eq_right_iff.2 (fun h' => absurd h'.2 ha)) hf

/-- **The darts of a short walk of a level are a shortest walk.** For token lengths that are the costs
`c` of their darts, with `c` equal on the two darts of an edge and giving `g`, and corners of `S` that
hold those of a live annulus, the others out of its reach: the darts of a walk of the network of a
level between copies on E_R edges of the pieces at `κ0(t)` and `κ1(t)`, of length below `M` and at
most `λ_t`, form a shortest walk of the annulus of the same length. -/
theorem level_shortest_darts (c : N.G.Dart → ℕ) (hcr : ∀ d, c (N.toRot.rev d) = c d)
    (hlam : ∀ x, lam x = c x.1.1) {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞}
    {Γ : Finset (N.G.Dart × Bool)} (hgc : ∀ d, g d = c d) (L : C.Live g Γ) (hS : Γ ⊆ S.Γ) {t : ℕ}
    (hz : ∀ w ∈ S.Γ, w ∉ Γ → ∀ p, ¬ (N.toRot.dual.double.split Γ).IsWalk
      ((N.toRot.dual.double.split Γ).tail (L.κ0 t)) p ((N.toRot.dual.double.split Γ).tail w))
    (h1 : L.xa ≤ t) (h2 : L.ya ≤ t) (h3 : t ≤ L.xb) (h4 : t ≤ L.yb)
    {u v : S.hRot.Vertex} (p : SsspFlow.Walk (S.levelNet hN).G.Adj ((S.levelPad hN).ι (.inl u))
      ((S.levelPad hN).ι (.inl v)))
    (hp : p.wt (lenTop (S.levelLen hN lam M)) < M)
    (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)) (hv : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v))
    (hpu : S.pieceOf ⟨S.vcopy u, hu⟩ = S.pieceAt (L.κ0 t))
    (hpv : S.pieceOf ⟨S.vcopy v, hv⟩ = S.pieceAt (L.κ1 t))
    (hle : p.wt (lenTop (S.levelLen hN lam M)) ≤ C.lamD g t) :
    L.Shortest t (S.levelDarts hN p) ∧
      ((S.levelDarts hN p).map (g ∘ Prod.fst)).sum = p.wt (lenTop (S.levelLen hN lam M)) := by
  have hz₁ : ∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN ((S.levelPad hN).ι (.inl u))) := by
    rw [S.copyAt_ι]; exact hu
  have hz₂ : ∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN ((S.levelPad hN).ι (.inl v))) := by
    rw [S.copyAt_ι]; exact hv
  have e₁ : S.pieceOf ⟨_, hz₁⟩ = S.pieceOf ⟨S.vcopy u, hu⟩ := congrArg S.pieceOf (Subtype.ext (S.copyAt_ι hN _))
  have e₂ : S.pieceOf ⟨_, hz₂⟩ = S.pieceOf ⟨S.vcopy v, hv⟩ := congrArg S.pieceOf (Subtype.ext (S.copyAt_ι hN _))
  obtain ⟨hw, hsum⟩ := S.levelDarts_walk hN lam M c hcr hlam p hz₁ hz₂ hp
  rw [e₁, hpu, e₂, hpv] at hw
  have hg' : ∀ d, g d = ENNReal.ofReal (c d : ℝ) := fun d => by rw [hgc, ENNReal.ofReal_natCast]
  have hk : ENNReal.ofReal ((S.levelDarts hN p).map fun z => (c z.1 : ℝ)).sum =
      p.wt (lenTop (S.levelLen hN lam M)) := by
    rw [ofReal_sum_map _ (fun _ => Nat.cast_nonneg _), ← hsum]
    simp only [ENNReal.ofReal_natCast]
  refine ⟨S.shortest_live (fun d => (c d : ℝ)) (fun _ => Nat.cast_nonneg _) hg' L hS hz h1 h2 h3 h4 _ hw
    (hk ▸ hle), ?_⟩
  rw [← hsum]
  exact congrArg List.sum (List.map_congr_left fun z _ => hgc z.1)

end RData

end RotSystem

end SsspFlow
