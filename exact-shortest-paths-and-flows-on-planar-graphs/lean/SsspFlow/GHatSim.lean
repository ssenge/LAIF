import SsspFlow.GHatProps
import SsspFlow.HostSimK

/-!
# The hosts of `G` simulate the repaired graph

The repaired graph `Ĝ_ℓ` as a simple graph on the copies (`RData.hatGraph`): two distinct copies are
adjacent if an arc of `Ĝ_ℓ` joins them. The vertices of `G` sit at the nodes of a network by a map
`hv`, and every dart between two nodes is an edge of the network, with at most one dart from one node
to another.

* `RData.hatHost_of_adj`: an edge of `Ĝ_ℓ` between copies at two different nodes is an E_R edge, and it
  follows an edge of the network.
* `RData.card_cross_le`: at most four edges of `Ĝ_ℓ` go from the copies at one node to the copies at
  another.
* `RData.run_hatSim`: if each node knows the edges of `Ĝ_ℓ` at its own copies, the nodes run any
  algorithm on `Ĝ_ℓ` in the same number of rounds, with messages of four times the width.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor

namespace RotSystem

universe u

noncomputable instance {V E : Type u} [Finite V] [Finite E] : Fintype (Copy V E) := by
  have : Finite (Copy V E) := by
    refine Finite.of_injective (β := V ⊕ E × Fin 4) (fun
      | .star v => .inl v
      | .dc c => .inr (c, 0)
      | .lc c => .inr (c, 1)
      | .rc c => .inr (c, 2)
      | .xc c => .inr (c, 3)) ?_
    intro a b h
    cases a <;> cases b <;> simp_all
  exact Fintype.ofFinite _

namespace RData

variable {E : Type u} [Fintype E] [DecidableEq E] {G : RotSystem E} (S : G.RData)

theorem arc_symm {a b : Copy G.Vertex E} (h : Nonempty (S.Arc a b)) : Nonempty (S.Arc b a) := by
  obtain ⟨h⟩ := h
  cases h with
  | er x => exact ⟨.er' x⟩
  | er' x => exact ⟨.er x⟩
  | ec x =>
    have h' := Arc.ec (S := S) (S.partnerTok x)
    simp only [partnerTok, G.partner_partner] at h'
    exact ⟨h'⟩
  | es h => exact ⟨.es' h⟩
  | es' h => exact ⟨.es h⟩

/-- `Ĝ_ℓ` as a simple graph on the copies. -/
def hatGraph : SimpleGraph (Copy G.Vertex E) where
  Adj a b := a ≠ b ∧ Nonempty (S.Arc a b)
  symm := ⟨fun _ _ h => ⟨h.1.symm, S.arc_symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- An arc between copies of different vertices is the E_R edge of a token, in one of its two
directions. -/
theorem er_of_arc {a b : Copy G.Vertex E} (h : S.Arc a b) (hne : G.owner a ≠ G.owner b) :
    ∃ x : S.Tok, (S.alpha x.1 = a ∧ S.beta x.1 = b) ∨ (S.beta x.1 = a ∧ S.alpha x.1 = b) := by
  cases h with
  | er x => exact ⟨x, .inl ⟨rfl, rfl⟩⟩
  | er' x => exact ⟨x, .inr ⟨rfl, rfl⟩⟩
  | ec x => exact absurd (S.owner_att_partner x.2).symm hne
  | es h => exact absurd (S.owner_es h) hne
  | es' h => exact absurd (S.owner_es h).symm hne

variable {V : Type*} (hv : G.Vertex → V)

/-- **Edges between nodes.** An edge of `Ĝ_ℓ` between copies at two different nodes follows an edge
of the network, if every dart between two different nodes does. -/
theorem hatHost_of_adj (N : SimpleGraph V)
    (hd : ∀ d, hv (G.tail d) ≠ hv (G.head d) → N.Adj (hv (G.tail d)) (hv (G.head d)))
    {a b : Copy G.Vertex E} (h : S.hatGraph.Adj a b) (hne : hv (G.owner a) ≠ hv (G.owner b)) :
    N.Adj (hv (G.owner a)) (hv (G.owner b)) := by
  obtain ⟨x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := S.er_of_arc h.2.some fun h' => hne (by rw [h'])
  · rw [S.owner_alpha, S.owner_beta] at hne ⊢
    exact hd _ hne
  · rw [S.owner_alpha, S.owner_beta] at hne ⊢
    exact (hd _ hne.symm).symm

/-- **At most four edges from one node to another.** If at most one dart goes from one node to
another, at most four edges of `Ĝ_ℓ` go from the copies at a node `v` to the copies at a different
node `u`. -/
theorem card_cross_le
    (hs : ∀ d d', hv (G.tail d) = hv (G.tail d') → hv (G.head d) = hv (G.head d') →
      hv (G.tail d) ≠ hv (G.head d) → d = d')
    {v u : V} (hvu : v ≠ u) :
    Nat.card {p : Copy G.Vertex E × Copy G.Vertex E //
      hv (G.owner p.1) = v ∧ hv (G.owner p.2) = u ∧ S.hatGraph.Adj p.1 p.2} ≤ 4 := by
  classical
  have hx : ∀ p : {p : Copy G.Vertex E × Copy G.Vertex E //
      hv (G.owner p.1) = v ∧ hv (G.owner p.2) = u ∧ S.hatGraph.Adj p.1 p.2},
      ∃ x : S.Tok, (S.alpha x.1 = p.1.1 ∧ S.beta x.1 = p.1.2) ∨
        (S.beta x.1 = p.1.1 ∧ S.alpha x.1 = p.1.2) := fun p =>
    S.er_of_arc p.2.2.2.2.some fun h' => hvu (p.2.1.symm.trans ((congrArg hv h').trans p.2.2.1))
  let f := fun p => (decide (hv (G.tail (hx p).choose.1.1) = v), decide ((hx p).choose.1.2 = .two))
  have hf : Function.Injective f := by
    intro p q hpq
    simp only [f, Prod.mk.injEq, decide_eq_decide] at hpq
    obtain ⟨h1, h2⟩ := hpq
    have s1 := (hx p).choose_spec
    have s2 := (hx q).choose_spec
    set x := (hx p).choose
    set y := (hx q).choose
    have hb := p.2.1
    have ha := p.2.2.1
    have hb' := q.2.1
    have ha' := q.2.2.1
    -- the ends of `x` and `y` at the two nodes
    have ex : (hv (G.tail x.1.1) = v ∧ hv (G.head x.1.1) = u) ∨
        (hv (G.tail x.1.1) = u ∧ hv (G.head x.1.1) = v) := by
      rcases s1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · left; rw [← S.owner_alpha, ← S.owner_beta, e1, e2]; exact ⟨hb, ha⟩
      · right; rw [← S.owner_alpha, ← S.owner_beta, e1, e2]; exact ⟨ha, hb⟩
    have ey : (hv (G.tail y.1.1) = v ∧ hv (G.head y.1.1) = u) ∨
        (hv (G.tail y.1.1) = u ∧ hv (G.head y.1.1) = v) := by
      rcases s2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · left; rw [← S.owner_alpha, ← S.owner_beta, e1, e2]; exact ⟨hb', ha'⟩
      · right; rw [← S.owner_alpha, ← S.owner_beta, e1, e2]; exact ⟨ha', hb'⟩
    have hd : x.1.1 = y.1.1 := by
      rcases ex with ⟨x1, x2⟩ | ⟨x1, x2⟩ <;> rcases ey with ⟨y1, y2⟩ | ⟨y1, y2⟩
      · exact hs _ _ (x1.trans y1.symm) (x2.trans y2.symm) (by rw [x1, x2]; exact hvu)
      · exact absurd (h1.1 x1) (by rw [y1]; exact hvu.symm)
      · exact absurd (h1.2 y1) (by rw [x1]; exact hvu.symm)
      · exact hs _ _ (x1.trans y1.symm) (x2.trans y2.symm) (by rw [x1, x2]; exact hvu.symm)
    have hl : x.1.2 = y.1.2 := by
      have tx := x.2
      have ty := y.2
      unfold IsTok at tx ty
      rw [hd] at tx
      cases hx2 : x.1.2 <;> cases hy2 : y.1.2 <;> simp_all
    have hxy : x = y := Subtype.ext (Prod.ext hd hl)
    rw [← hxy] at s2
    apply Subtype.ext
    rcases s1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases s2 with ⟨f1, f2⟩ | ⟨f1, f2⟩
    · exact Prod.ext (e1.symm.trans f1) (e2.symm.trans f2)
    · exact absurd (hb.symm.trans ((congrArg (fun c => hv (G.owner c)) (e1.symm.trans f2)).trans ha')) hvu
    · exact absurd (hb.symm.trans ((congrArg (fun c => hv (G.owner c)) (e1.symm.trans f2)).trans ha')) hvu
    · exact Prod.ext (e1.symm.trans f1) (e2.symm.trans f2)
  calc _ ≤ Nat.card (Bool × Bool) := Nat.card_le_card_of_injective f hf
    _ = 4 := by simp

/-- **The hosts simulate `Ĝ_ℓ`.** The nodes of a network `N` hold the copies of their vertices. Every
dart between two different nodes is an edge of `N`, at most one dart goes from one node to another,
and each node knows the edges of `Ĝ_ℓ` at its own copies. Then the nodes run any algorithm on `Ĝ_ℓ`,
round for round, with messages of four times the width. -/
theorem run_hatSim {I J σ : Type*} {B : ℕ} (A : Cslib.Congest.Algorithm (Copy G.Vertex E) J σ B)
    (view : I → Copy G.Vertex E → Copy G.Vertex E → Prop) (vin : V → I → Copy G.Vertex E → J)
    (N : SimpleGraph V) [DecidableRel N.Adj] [DecidableRel S.hatGraph.Adj]
    (inp : V → I) (inp' : Copy G.Vertex E → J)
    (hin : ∀ a, inp' a = vin (hv (G.owner a)) (inp (hv (G.owner a))) a)
    (hview : ∀ w b a, (hv (G.owner b) = w ∨ hv (G.owner a) = w) →
      (view (inp w) b a ↔ S.hatGraph.Adj b a))
    (hd : ∀ d, hv (G.tail d) ≠ hv (G.head d) → N.Adj (hv (G.tail d)) (hv (G.head d)))
    (hs : ∀ d d', hv (G.tail d) = hv (G.tail d') → hv (G.head d) = hv (G.head d') →
      hv (G.tail d) ≠ hv (G.head d) → d = d')
    (t : ℕ) (w : V) (a : Copy G.Vertex E) (ha : hv (G.owner a) = w) :
    ((Cslib.Congest.Algorithm.simulateView (k := 4) A (fun c => hv (G.owner c)) view vin).run N inp
      t w).2 a = A.run S.hatGraph inp' t a :=
  (Cslib.Congest.Algorithm.run_simulateView A _ view vin N S.hatGraph inp inp' hin hview
    (fun _ _ h hne => S.hatHost_of_adj hv N hd h hne) (fun _ _ hvu => S.card_cross_le hv hs hvu)
    t w).2 a ha

end RData

end RotSystem

end SsspFlow
