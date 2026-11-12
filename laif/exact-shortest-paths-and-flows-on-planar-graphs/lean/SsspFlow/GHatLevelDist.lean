import SsspFlow.GHatLevelSim
import SsspFlow.LemmaV
import SsspFlow.LabelHypothesis

/-!
# Distances in the network of a level

The arcs of `Ĝ_ℓ` get natural lengths: `0` on E_R arcs, `lam x` on the E_C arc of the token `x` and
`M` on E_S arcs (`RData.arcW`). Each kept dart of the full repaired graph carries the length of its
arc (`RData.dartW`): every kept dart is an arc of the same length between the same copies
(`RData.arc_of_keep_w`), and every arc is such a dart (`RData.keep_of_arc_w`).

In the network of a level, the middle edge of a kept dart has the length of the dart, an edge
between a copy and a dart has length `0`, and all other edges have length `∞` (`RData.levelLen`).
Then the distance between two copies in the network of the level is their distance in `Ĝ_ℓ`
(`RData.levelNet_dist`).
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

section Weights

variable {E : Type} [Fintype E] [DecidableEq E] {G : RotSystem E} (S : G.RData) (lam : S.Tok → ℕ)
  (M : ℕ)

/-- The natural length of an arc of `Ĝ_ℓ`. -/
def arcW : ∀ a b, S.Arc a b → ℕ
  | _, _, .er _ => 0
  | _, _, .er' _ => 0
  | _, _, .ec x => lam x
  | _, _, .es _ => M
  | _, _, .es' _ => M

/-- The token whose E_C edge is the rim across `d`, read from its tail. -/
def rimTok (d : E) : S.Tok :=
  if h : d ∈ S.inc then ⟨(d, .one), S.isTok_one h⟩ else ⟨(d, .zero), S.isTok_zero h⟩

/-- The length of a dart of the full repaired graph. -/
def dartW : S.HD → ℕ
  | (.tok _, _) => 0
  | (.rim d, false) => lam (S.rimTok d)
  | (.rim d, true) => lam (S.partnerTok (S.rimTok d))
  | _ => M

theorem arcW_transport {a b a' b' : Copy G.Vertex E} (e : S.Arc a b) (ha : a = a') (hb : b = b') :
    ∃ e' : S.Arc a' b', S.arcW lam M a' b' e' = S.arcW lam M a b e := by
  subst ha hb
  exact ⟨e, rfl⟩

/-- Every kept dart is an arc of the same length between the same copies. -/
theorem arc_of_keep_w (x : S.HD) (hx : x ∈ S.keep) :
    ∃ e : S.Arc (S.tl x) (S.tl (S.hrev x)), S.arcW lam M _ _ e = S.dartW lam M x := by
  obtain ⟨e, b⟩ := x
  simp only [keep, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  cases e with
  | sp c =>
    cases b
    · exact ⟨.es (a := .star (G.tail c)) (b := .dc c) rfl, rfl⟩
    · exact ⟨.es' (a := .star (G.tail c)) (b := .dc c) rfl, rfl⟩
  | rim d =>
    simp only [Keep] at hx
    have key : S.att (S.rimTok d).1 = S.alphaD (G.tailCorner d) ∧
        S.att (G.partner (S.rimTok d).1) = S.betaD d := by
      by_cases hd : d ∈ S.inc
      · simp only [rimTok, hd, dite_true]
        exact S.att_of_atTail (x := (d, .one)) (S.isTok_one hd) rfl
      · have hh : S.hostT d = true := by simpa [hd] using hx
        simp only [rimTok, hd, dite_false]
        exact S.att_of_atTail (x := (d, .zero)) (S.isTok_zero hd) hh
    obtain ⟨h1, h2⟩ := key
    cases b
    · exact S.arcW_transport lam M (.ec (S.rimTok d)) h1 h2
    · have hpp : S.att (G.partner (S.partnerTok (S.rimTok d)).1) = S.att (S.rimTok d).1 := by
        simp [partnerTok]
      exact S.arcW_transport lam M (.ec (S.partnerTok (S.rimTok d))) h2 (hpp.trans h1)
  | tok y =>
    cases b
    · exact ⟨.er y, rfl⟩
    · exact ⟨.er' y, rfl⟩
  | lsp a =>
    obtain ⟨a, ha⟩ := a
    have h : S.ES (.dc (G.headCorner a)) (.lc (G.headCorner a)) :=
      ⟨rfl, by simpa [inDart, headCorner] using ha⟩
    cases b
    · exact ⟨.es h, rfl⟩
    · exact ⟨.es' h, rfl⟩
  | rsp b' =>
    obtain ⟨b', hb⟩ := b'
    have h : S.ES (.dc (G.tailCorner b')) (.rc (G.tailCorner b')) :=
      ⟨rfl, by simpa [outDart, tailCorner] using hb⟩
    cases b
    · exact ⟨.es h, rfl⟩
    · exact ⟨.es' h, rfl⟩
  | xsp c =>
    obtain ⟨c, hc⟩ := c
    have h : S.ES (.dc c) (.xc c) := ⟨rfl, hc⟩
    cases b
    · exact ⟨.es h, rfl⟩
    · exact ⟨.es' h, rfl⟩

/-- Every arc is a kept dart of the same length between the same copies. -/
theorem keep_of_arc_w : ∀ (a b : Copy G.Vertex E) (e : S.Arc a b),
    ∃ x ∈ S.keep, S.tl x = a ∧ S.tl (S.hrev x) = b ∧ S.dartW lam M x = S.arcW lam M a b e := by
  have hk : ∀ x : S.HD, S.Keep x.1 → x ∈ S.keep := fun x h => by simp [keep, h]
  have hES : ∀ a b : Copy G.Vertex E, S.ES a b →
      ∃ x ∈ S.keep, S.tl x = a ∧ S.tl (S.hrev x) = b ∧ S.dartW lam M x = M ∧
        S.dartW lam M (S.hrev x) = M := by
    intro a b h
    cases a <;> cases b <;> simp only [ES] at h
    · exact ⟨fw (HE.sp _), hk _ trivial, by simp [ends, h], rfl, rfl, rfl⟩
    · obtain ⟨rfl, h⟩ := h
      exact ⟨fw (HE.lsp ⟨_, h⟩), hk _ trivial, by simp [ends, inDart, headCorner],
        by simp [hrev, ends, inDart, headCorner], rfl, rfl⟩
    · obtain ⟨rfl, h⟩ := h
      exact ⟨fw (HE.rsp ⟨_, h⟩), hk _ trivial, by simp [ends, outDart, tailCorner],
        by simp [hrev, ends, outDart, tailCorner], rfl, rfl⟩
    · obtain ⟨rfl, h⟩ := h
      exact ⟨fw (HE.xsp ⟨_, h⟩), hk _ trivial, rfl, rfl, rfl, rfl⟩
  intro a b e
  cases e with
  | er y => exact ⟨fw (HE.tok y), hk _ trivial, rfl, rfl, rfl⟩
  | er' y => exact ⟨bw (HE.tok y), hk _ trivial, rfl, rfl, rfl⟩
  | es h =>
    obtain ⟨x, hx, h1, h2, h3, -⟩ := hES _ _ h
    exact ⟨x, hx, h1, h2, h3⟩
  | es' h =>
    obtain ⟨x, hx, h1, h2, -, h4⟩ := hES _ _ h
    exact ⟨S.hrev x, hk _ (by simpa [keep, hrev] using hx), h2, by simpa [hrev] using h1, h4⟩
  | ec y =>
    obtain ⟨⟨d, l⟩, hy⟩ := y
    have hy' := hy
    simp only [IsTok] at hy'
    by_cases ht : S.atTail (d, l) = true
    · obtain ⟨h1, h2⟩ := S.att_of_atTail hy ht
      refine ⟨fw (HE.rim d), hk _ ?_, by simpa [ends] using h1.symm,
        by simpa [hrev, ends] using h2.symm, ?_⟩
      · cases l <;> simp_all [Keep, atTail]
      · show lam (S.rimTok d) = lam ⟨(d, l), hy⟩
        congr 1
        apply Subtype.ext
        cases l <;> simp_all [rimTok, atTail]
    · cases l with
      | one => simp [atTail] at ht
      | two =>
        have hd : d ∈ S.inc := by simpa [IsTok] using hy
        refine ⟨bw (HE.rim (G.rev d)), hk _ (Or.inl ((S.inc_rev d).2 hd)), ?_, ?_, ?_⟩
        · simp [ends, hrev, att, atTail, alpha, beta, partner, Lab.swap, headCorner]
        · simp [ends, hrev, att, atTail, alpha, beta, partner, Lab.swap, headCorner]
        · show lam (S.partnerTok (S.rimTok (G.rev d))) = lam ⟨(d, .two), hy⟩
          congr 1
          apply Subtype.ext
          simp [rimTok, (S.inc_rev d).2 hd, partnerTok, partner, Lab.swap]
      | zero =>
        have hd : d ∉ S.inc := by simpa [IsTok] using hy
        have hh : S.hostT d = false := by simpa [atTail] using ht
        have hr : S.hostT (G.rev d) = true := by simp [S.hostT_rev d hd, hh]
        refine ⟨bw (HE.rim (G.rev d)), hk _ (Or.inr hr), ?_, ?_, ?_⟩
        · simp [ends, hrev, att, atTail, alpha, beta, partner, Lab.swap, headCorner, hh, hr]
        · simp [ends, hrev, att, atTail, alpha, beta, partner, Lab.swap, headCorner, hh, hr]
        · show lam (S.partnerTok (S.rimTok (G.rev d))) = lam ⟨(d, .zero), hy⟩
          congr 1
          apply Subtype.ext
          have : G.rev d ∉ S.inc := fun h => hd ((S.inc_rev d).1 h)
          simp [rimTok, this, partnerTok, partner, Lab.swap]

/-- The length of a walk of `Ĝ_ℓ`. -/
def awt : {a b : Copy G.Vertex E} → FaceDisjoint.Walk S.Arc a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons e p => S.arcW lam M _ _ e + awt p

/-- The distance in `Ĝ_ℓ` for natural lengths. -/
noncomputable def arcDist (a b : Copy G.Vertex E) : ℝ≥0∞ :=
  ⨅ q : FaceDisjoint.Walk S.Arc a b, ((S.awt lam M q : ℕ) : ℝ≥0∞)

theorem arcDist_self (a : Copy G.Vertex E) : S.arcDist lam M a a = 0 :=
  le_antisymm (iInf_le_of_le (.nil a) (by simp [awt])) bot_le

theorem awt_append : ∀ {a b c : Copy G.Vertex E} (p : FaceDisjoint.Walk S.Arc a b)
    (q : FaceDisjoint.Walk S.Arc b c), S.awt lam M (p.append q) = S.awt lam M p + S.awt lam M q
  | _, _, _, .nil _, q => by simp [awt, FaceDisjoint.Walk.append]
  | _, _, _, .cons e p, q => by
    simp only [FaceDisjoint.Walk.append, awt, awt_append p q]
    omega

/-- One arc more. -/
theorem arcDist_arc (a : Copy G.Vertex E) {b c : Copy G.Vertex E} (e : S.Arc b c) :
    S.arcDist lam M a c ≤ S.arcDist lam M a b + (S.arcW lam M b c e : ℝ≥0∞) := by
  unfold arcDist
  rw [ENNReal.iInf_add]
  refine le_iInf fun q => iInf_le_of_le (q.append (.cons e (.nil c))) ?_
  rw [S.awt_append]
  simp [awt]

end Weights

section Level

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ)

open Classical in
/-- The lengths of the network of a level: the length of the dart on the middle edge of a kept dart,
`0` between a copy and a dart, and `∞` otherwise. -/
noncomputable def levelLen (x y : Fin (n * (n * 21))) : ℕ∞ :=
  if (S.levelPad hN).IsReal x ∧ (S.levelPad hN).IsReal y then
    match (S.levelPad hN).back x, (S.levelPad hN).back y with
    | .inr d, .inr d' => if d' = S.hrev d ∧ d ∈ S.keep then (S.dartW lam M d : ℕ∞) else ⊤
    | .inl _, .inr _ => 0
    | .inr _, .inl _ => 0
    | .inl _, .inl _ => ⊤
  else ⊤

theorem levelLen_ι (x y : S.hRot.Vertex ⊕ S.HD) :
    S.levelLen hN lam M ((S.levelPad hN).ι x) ((S.levelPad hN).ι y) =
      match x, y with
      | .inr d, .inr d' => if d' = S.hrev d ∧ d ∈ S.keep then (S.dartW lam M d : ℕ∞) else ⊤
      | .inl _, .inr _ => 0
      | .inr _, .inl _ => 0
      | .inl _, .inl _ => ⊤ := by
  classical
  unfold levelLen
  rw [if_pos ⟨(S.levelPad hN).isReal_ι x, (S.levelPad hN).isReal_ι y⟩, (S.levelPad hN).back_ι,
    (S.levelPad hN).back_ι]

/-- The copy of an identifier: the copy of the node it names or at which it hangs. -/
noncomputable def copyAt (z : Fin (n * (n * 21))) : Copy N.toRot.Vertex N.G.Dart :=
  S.copyOf ((S.levelPad hN).back z)

theorem copyAt_ι (x : S.hRot.Vertex ⊕ S.HD) : S.copyAt hN ((S.levelPad hN).ι x) = S.copyOf x := by
  rw [copyAt, (S.levelPad hN).back_ι]

theorem vcopy_tail (d : S.HD) : S.vcopy (S.hRot.tail d) = S.tl d := rfl

/-- **The distance from a copy is a potential** of the network of a level. -/
theorem arcDist_step (a₀ : Copy N.toRot.Vertex N.G.Dart) {z z' : Fin (n * (n * 21))}
    (h : (S.levelNet hN).G.Adj z z') :
    S.arcDist lam M a₀ (S.copyAt hN z') ≤
      S.arcDist lam M a₀ (S.copyAt hN z) + lenTop (S.levelLen hN lam M) z z' := by
  classical
  have htop : ∀ {x y}, S.levelLen hN lam M x y = ⊤ →
      S.arcDist lam M a₀ (S.copyAt hN y) ≤ S.arcDist lam M a₀ (S.copyAt hN x) + lenTop (S.levelLen hN lam M) x y :=
    fun hxy => by simp [lenTop, hxy]
  have hnr : ∀ {x y}, (¬ (S.levelPad hN).IsReal x ∨ ¬ (S.levelPad hN).IsReal y) →
      S.levelLen hN lam M x y = ⊤ := fun hxy => by
    unfold levelLen
    rw [if_neg (fun h' => hxy.elim (· h'.1) (· h'.2))]
  rcases padNet_adj_cases h with ⟨x, y, rfl, rfl, hxy⟩ | ⟨hb, rfl⟩ | ⟨ha, rfl⟩
  · rw [S.copyAt_ι, S.copyAt_ι]
    rcases x with v | d <;> rcases y with w | d'
    · exact absurd hxy id
    · obtain rfl : S.hRot.tail d' = v := hxy
      simp only [copyOf, vcopy_tail]
      exact le_self_add
    · obtain rfl : S.hRot.tail d = w := hxy
      simp only [copyOf, vcopy_tail]
      exact le_self_add
    · obtain rfl : d' = S.hRot.rev d := hxy
      by_cases hk : d ∈ S.keep
      · obtain ⟨e, he⟩ := S.arc_of_keep_w lam M d hk
        have hl := S.levelLen_ι hN lam M (.inr d) (.inr (S.hRot.rev d))
        simp only [show S.hRot.rev d = S.hrev d from rfl, true_and, hk, ite_true] at hl
        simp only [copyOf, lenTop, show S.hRot.rev d = S.hrev d from rfl, hl, ENat.toENNReal_coe]
        rw [← he]
        exact S.arcDist_arc lam M a₀ e
      · have ht : S.levelLen hN lam M ((S.levelPad hN).ι (.inr d))
            ((S.levelPad hN).ι (.inr (S.hRot.rev d))) = ⊤ := by
          rw [S.levelLen_ι]
          simp [hk]
        simp [lenTop, ht]
  · exact htop (hnr (.inl hb))
  · exact htop (hnr (.inr ha))

theorem arcDist_walk (a₀ : Copy N.toRot.Vertex N.G.Dart) : ∀ {z z' : Fin (n * (n * 21))}
    (p : SsspFlow.Walk (S.levelNet hN).G.Adj z z'),
    S.arcDist lam M a₀ (S.copyAt hN z') ≤
      S.arcDist lam M a₀ (S.copyAt hN z) + p.wt (lenTop (S.levelLen hN lam M))
  | _, _, .nil _ => by simp [SsspFlow.Walk.wt]
  | _, _, .cons e p => by
    refine (arcDist_walk a₀ p).trans ?_
    simp only [SsspFlow.Walk.wt, ← add_assoc]
    exact add_le_add (S.arcDist_step hN lam M a₀ e) le_rfl

/-- A walk of `Ĝ_ℓ` gives a walk of the network of a level of the same length. -/
theorem lift_walk : ∀ {a b : Copy N.toRot.Vertex N.G.Dart} (q : FaceDisjoint.Walk S.Arc a b)
    (u v : S.hRot.Vertex), S.vcopy u = a → S.vcopy v = b →
    ∃ p : SsspFlow.Walk (S.levelNet hN).G.Adj ((S.levelPad hN).ι (.inl u)) ((S.levelPad hN).ι (.inl v)),
      p.wt (lenTop (S.levelLen hN lam M)) = (S.awt lam M q : ℝ≥0∞)
  | _, _, .nil _, u, v, hu, hv => by
    obtain rfl := S.vcopy_injective (hu.trans hv.symm)
    exact ⟨.nil _, by simp [SsspFlow.Walk.wt, awt]⟩
  | _, _, .cons e q, u, v, hu, hv => by
    obtain ⟨x, hx, h1, h2, h3⟩ := S.keep_of_arc_w lam M _ _ e
    obtain rfl : S.hRot.tail x = u := S.vcopy_injective ((S.vcopy_tail x).trans (h1.trans hu.symm))
    obtain ⟨p, hp⟩ := lift_walk q (S.hRot.tail (S.hrev x)) v (by rw [S.vcopy_tail, h2]) hv
    have e1 : (S.levelNet hN).G.Adj ((S.levelPad hN).ι (.inl (S.hRot.tail x))) ((S.levelPad hN).ι (.inr x)) :=
      padNet_adj_ι (show S.hRot.tail x = S.hRot.tail x from rfl)
    have e2 : (S.levelNet hN).G.Adj ((S.levelPad hN).ι (.inr x)) ((S.levelPad hN).ι (.inr (S.hrev x))) :=
      padNet_adj_ι (show S.hrev x = S.hRot.rev x from rfl)
    have e3 : (S.levelNet hN).G.Adj ((S.levelPad hN).ι (.inr (S.hrev x)))
        ((S.levelPad hN).ι (.inl (S.hRot.tail (S.hrev x)))) :=
      padNet_adj_ι (show S.hRot.tail (S.hrev x) = S.hRot.tail (S.hrev x) from rfl)
    refine ⟨.cons e1 (.cons e2 (.cons e3 p)), ?_⟩
    simp only [SsspFlow.Walk.wt, hp, lenTop, S.levelLen_ι, true_and, hx, ite_true, awt, h3]
    simp

/-- **Distances in the network of a level are distances in `Ĝ_ℓ`.** -/
theorem levelNet_dist (u v : S.hRot.Vertex) :
    dist (S.levelNet hN).G.Adj (lenTop (S.levelLen hN lam M)) Set.univ
      ((S.levelPad hN).ι (.inl u)) ((S.levelPad hN).ι (.inl v)) =
        S.arcDist lam M (S.vcopy u) (S.vcopy v) := by
  apply le_antisymm
  · refine le_iInf fun q => ?_
    obtain ⟨p, hp⟩ := S.lift_walk hN lam M q u v rfl rfl
    exact iInf₂_le_of_le p (fun _ _ => Set.mem_univ _) hp.le
  · refine le_iInf₂ fun p _ => ?_
    have := S.arcDist_walk hN lam M (S.vcopy u) p
    rwa [S.copyAt_ι, S.copyAt_ι, copyOf, copyOf, arcDist_self, zero_add] at this

end Level

end RData

end RotSystem

end SsspFlow
