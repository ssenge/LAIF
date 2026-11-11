import SsspFlow.GHatLevel
import SsspFlow.HostSimK

/-!
# The nodes of the network simulate the network of a level

The host of an identifier `(v, u, k)` is the node `v`. Every edge of the network of a level between two
hosts is the middle edge of a token dart (`RData.levelNet_cross`), so it follows an edge of the
network (`RData.levelNet_host`), and at most four such edges go from one node to another
(`RData.levelNet_card_cross`). So the nodes run any algorithm on the network of a level round for
round, with messages of four times the width, if each node knows the edges at its own identifiers
(`RData.run_levelSim`).
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest

namespace Congest

variable {V₀ W : Type} [Fintype V₀] [DecidableEq V₀] [Fintype W] [DecidableEq W]
  {P : PadMap V₀ W} {N₀ : Net V₀}

/-- An edge of a padded network joins two names of nodes that are adjacent, or a pendant identifier
to the node at which it hangs. -/
theorem padNet_adj_cases {b a : W} (h : (padNet P N₀).G.Adj b a) :
    (∃ x y, b = P.ι x ∧ a = P.ι y ∧ N₀.G.Adj x y) ∨ (¬ P.IsReal b ∧ a = P.ι (P.back b)) ∨
      (¬ P.IsReal a ∧ b = P.ι (P.back a)) := by
  by_cases hb : P.IsReal b
  · have h' : a ∈ padList P N₀ (P.ι (P.back b)) := by rw [← hb]; exact h
    rw [padList_ι, List.mem_append] at h'
    rcases h' with h' | h'
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h'
      exact .inl ⟨P.back b, y, hb, rfl, (N₀.mem_rotList _ _).1 hy⟩
    · rw [Finset.mem_toList, P.mem_extras] at h'
      exact .inr (.inr ⟨h'.1, by rw [h'.2]; exact hb⟩)
  · have h' : a ∈ padList P N₀ b := h
    rw [padList_of_not hb, List.mem_singleton] at h'
    exact .inr (.inl ⟨hb, h'⟩)

end Congest

namespace RotSystem

namespace RData

variable {E : Type} [Fintype E] [DecidableEq E] {G : RotSystem E} (S : G.RData)

/-- The dart of `G` that names a dart of the repaired graph: it starts at the vertex of its first
copy. -/
def baseDart : S.HD → E
  | (.sp c, _) => c
  | (.rim d, _) => d
  | (.tok x, false) => x.1.1
  | (.tok x, true) => G.rev x.1.1
  | (.lsp a, _) => G.rev a.1
  | (.rsp b, _) => b.1
  | (.xsp c, _) => c.1

theorem owner_tl (x : S.HD) : G.owner (S.tl x) = G.tail (S.baseDart x) := by
  obtain ⟨e, b⟩ := x
  rcases e with c | c | x | c | c | c <;> cases b
  all_goals first
    | rfl
    | exact S.owner_alphaD _ |>.trans (G.tail_tailCorner _)
    | exact S.owner_betaD _
    | exact S.owner_alpha _
    | exact S.owner_beta _
    | exact G.tail_tailCorner _

/-- Only the middle edge of a token joins copies of two different vertices. -/
theorem tok_of_owner_ne {x : S.HD} (h : G.owner (S.tl x) ≠ G.owner (S.tl (S.hrev x))) :
    ∃ y : S.Tok, x.1 = .tok y := by
  obtain ⟨e, b⟩ := x
  rcases e with c | c | y | c | c | c
  · exact absurd (by rw [S.owner_tl, S.owner_tl]; cases b <;> rfl) h
  · exact absurd (by rw [S.owner_tl, S.owner_tl]; cases b <;> rfl) h
  · exact ⟨y, rfl⟩
  · exact absurd (by rw [S.owner_tl, S.owner_tl]; cases b <;> rfl) h
  · exact absurd (by rw [S.owner_tl, S.owner_tl]; cases b <;> rfl) h
  · exact absurd (by rw [S.owner_tl, S.owner_tl]; cases b <;> rfl) h

end RData

end RotSystem

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

/-- The host of an identifier. -/
def hostOf (a : Fin (n * (n * 21))) : Fin n := (idEquiv.symm a).1

theorem nameD_fst (x : S.HD) : (S.nameD x).1 = (S.baseDart x).fst := by
  obtain ⟨e, b⟩ := x
  rcases e with c | c | ⟨⟨c, l⟩, hc⟩ | c | c | c <;> (try cases l) <;> cases b <;> rfl

theorem nameC_fst (a : Copy N.toRot.Vertex N.G.Dart) : (N.nameC a).1 = N.vnode (N.toRot.owner a) := by
  cases a with
  | star v => rfl
  | _ c => rfl

/-- The copy of a node of the subdivided repaired graph. -/
noncomputable def copyOf : S.hRot.Vertex ⊕ S.HD → Copy N.toRot.Vertex N.G.Dart
  | .inl v => S.vcopy v
  | .inr d => S.tl d

theorem hostOf_ι (x : S.hRot.Vertex ⊕ S.HD) :
    hostOf ((S.levelPad hN).ι x) = N.vnode (N.toRot.owner (S.copyOf x)) := by
  show (idEquiv.symm (idEquiv (S.name x))).1 = _
  rw [Equiv.symm_apply_apply]
  rcases x with v | d
  · exact nameC_fst _
  · show (S.nameD d).1 = _
    rw [nameD_fst, copyOf, S.owner_tl]
    rfl

theorem copyOf_tail (d : S.HD) : S.copyOf (.inl (S.hRot.tail d)) = S.tl d := rfl

/-- A pendant identifier hangs at a node of its own host. -/
theorem hostOf_back {a : Fin (n * (n * 21))} (ha : ¬ (S.levelPad hN).IsReal a) :
    hostOf ((S.levelPad hN).ι ((S.levelPad hN).back a)) = hostOf a := by
  have hne : ¬ ∃ x, idEquiv (S.name x) = a := by
    rintro ⟨x, rfl⟩
    exact ha ((S.levelPad hN).isReal_ι x)
  have hb : (S.levelPad hN).back a = .inl (S.starV hN (idEquiv.symm a).1) := by
    show (if h : ∃ x, idEquiv (S.name x) = a then h.choose else _) = _
    rw [dite_eq_right_of_eq_false (eq_false hne)]
  rw [hb, S.hostOf_ι]
  rfl

/-- **Edges between hosts.** An edge of the network of a level between two different hosts is the
middle edge of a dart whose two copies belong to different vertices. -/
theorem levelNet_cross {b a : Fin (n * (n * 21))} (h : (S.levelNet hN).G.Adj b a)
    (hne : hostOf b ≠ hostOf a) :
    ∃ d : S.HD, b = (S.levelPad hN).ι (.inr d) ∧ a = (S.levelPad hN).ι (.inr (S.hrev d)) ∧
      N.toRot.owner (S.tl d) ≠ N.toRot.owner (S.tl (S.hrev d)) := by
  rcases padNet_adj_cases h with ⟨x, y, rfl, rfl, hxy⟩ | ⟨hb, rfl⟩ | ⟨ha, rfl⟩
  · rcases x with v | d <;> rcases y with w | d'
    · exact absurd hxy id
    · obtain rfl : S.hRot.tail d' = v := hxy
      exact absurd (by rw [S.hostOf_ι, S.hostOf_ι]; rfl) hne
    · obtain rfl : S.hRot.tail d = w := hxy
      exact absurd (by rw [S.hostOf_ι, S.hostOf_ι]; rfl) hne
    · obtain rfl : d' = S.hRot.rev d := hxy
      refine ⟨d, rfl, rfl, fun ho => hne ?_⟩
      rw [S.hostOf_ι, S.hostOf_ι]
      exact congrArg N.vnode ho
  · exact absurd (S.hostOf_back hN hb).symm hne
  · exact absurd (S.hostOf_back hN ha) hne

/-- **Edges between hosts follow edges of the network.** -/
theorem levelNet_host {b a : Fin (n * (n * 21))} (h : (S.levelNet hN).G.Adj b a)
    (hne : hostOf b ≠ hostOf a) : N.G.Adj (hostOf b) (hostOf a) := by
  obtain ⟨d, rfl, rfl, ho⟩ := S.levelNet_cross hN h hne
  obtain ⟨y, hy⟩ := S.tok_of_owner_ne ho
  obtain ⟨e, β⟩ := d
  simp only at hy
  subst hy
  rw [S.hostOf_ι, S.hostOf_ι]
  simp only [copyOf, S.owner_tl, Net.vnode_tail]
  cases β
  · exact y.1.1.adj
  · exact y.1.1.adj.symm

/-- The key of a dart: for a token, whether its label is `2`, and its side. -/
def tokKey : S.HD → Bool × Bool
  | (.tok x, β) => (decide (x.1.2 = .two), β)
  | (_, β) => (false, β)

theorem tokKey_inj {v u : Fin n} {d d' : S.HD}
    (h1 : hostOf ((S.levelPad hN).ι (.inr d)) = v) (h2 : hostOf ((S.levelPad hN).ι (.inr (S.hrev d))) = u)
    (h1' : hostOf ((S.levelPad hN).ι (.inr d')) = v)
    (h2' : hostOf ((S.levelPad hN).ι (.inr (S.hrev d'))) = u)
    (ho : N.toRot.owner (S.tl d) ≠ N.toRot.owner (S.tl (S.hrev d)))
    (ho' : N.toRot.owner (S.tl d') ≠ N.toRot.owner (S.tl (S.hrev d')))
    (hk : S.tokKey d = S.tokKey d') : d = d' := by
  obtain ⟨x, hx⟩ := S.tok_of_owner_ne ho
  obtain ⟨y, hy⟩ := S.tok_of_owner_ne ho'
  obtain ⟨e, β⟩ := d
  obtain ⟨e', β'⟩ := d'
  simp only at hx hy
  subst hx hy
  simp only [tokKey, Prod.mk.injEq, decide_eq_decide] at hk
  obtain ⟨hk1, rfl⟩ := hk
  simp only [S.hostOf_ι, copyOf, S.owner_tl, Net.vnode_tail, hrev] at h1 h2 h1' h2'
  have hdart : x.1.1 = y.1.1 := by
    cases β <;> simp only [baseDart, Bool.not_false, Bool.not_true, Net.toRot_rev,
      SimpleGraph.Dart.symm_toProd, Prod.fst_swap] at h1 h2 h1' h2' <;>
      exact SimpleGraph.Dart.ext _ _ (Prod.ext (by first | exact h1.trans h1'.symm | exact h2.trans h2'.symm)
        (by first | exact h2.trans h2'.symm | exact h1.trans h1'.symm))
  have hl : x.1.2 = y.1.2 := by
    have tx := x.2
    have ty := y.2
    unfold IsTok at tx ty
    rw [hdart] at tx
    cases hx2 : x.1.2 <;> cases hy2 : y.1.2 <;> simp_all
  rw [Subtype.ext (Prod.ext hdart hl)]

/-- **At most four edges from one host to another.** -/
theorem levelNet_card_cross {v u : Fin n} (hvu : v ≠ u) :
    Nat.card {p : Fin (n * (n * 21)) × Fin (n * (n * 21)) //
      hostOf p.1 = v ∧ hostOf p.2 = u ∧ (S.levelNet hN).G.Adj p.1 p.2} ≤ 4 := by
  classical
  have hx := fun p : {p : Fin (n * (n * 21)) × Fin (n * (n * 21)) //
      hostOf p.1 = v ∧ hostOf p.2 = u ∧ (S.levelNet hN).G.Adj p.1 p.2} =>
    S.levelNet_cross hN p.2.2.2 (by rw [p.2.1, p.2.2.1]; exact hvu)
  refine (Nat.card_le_card_of_injective (fun p => S.tokKey (hx p).choose) ?_).trans (by simp)
  intro p q hpq
  obtain ⟨hp1, hp2, hpo⟩ := (hx p).choose_spec
  obtain ⟨hq1, hq2, hqo⟩ := (hx q).choose_spec
  have hd := S.tokKey_inj hN (hp1 ▸ p.2.1) (hp2 ▸ p.2.2.1) (hq1 ▸ q.2.1) (hq2 ▸ q.2.2.1) hpo hqo hpq
  apply Subtype.ext
  refine Prod.ext (hp1.trans ?_) (hp2.trans ?_)
  · rw [hd]; exact hq1.symm
  · rw [hd]; exact hq2.symm

/-- **The nodes simulate the network of a level.** Each node knows the edges of the network of the
level at its own identifiers. Then the nodes run any algorithm on it, round for round, with messages
of four times the width. -/
theorem run_levelSim {I J σ : Type*} {B : ℕ} (A : Cslib.Congest.Algorithm (Fin (n * (n * 21))) J σ B)
    (view : I → Fin (n * (n * 21)) → Fin (n * (n * 21)) → Prop) (vin : Fin n → I → Fin (n * (n * 21)) → J)
    (inp : Fin n → I) (inp' : Fin (n * (n * 21)) → J)
    (hin : ∀ a, inp' a = vin (hostOf a) (inp (hostOf a)) a)
    (hview : ∀ w b a, (hostOf b = w ∨ hostOf a = w) → (view (inp w) b a ↔ (S.levelNet hN).G.Adj b a))
    (t : ℕ) (w : Fin n) (a : Fin (n * (n * 21))) (ha : hostOf a = w) :
    ((Cslib.Congest.Algorithm.simulateView (k := 4) A hostOf view vin).run N.G inp t w).2 a =
      A.run (S.levelNet hN).G inp' t a :=
  (Cslib.Congest.Algorithm.run_simulateView A hostOf view vin N.G (S.levelNet hN).G inp inp' hin hview
    (fun _ _ h hne => S.levelNet_host hN h hne) (fun _ _ hvu => S.levelNet_card_cross hN hvu) t w).2 a ha

end RData

end RotSystem

end SsspFlow
