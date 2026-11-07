import SsspFlow.GHatDist

/-!
# Further properties of the repaired graph

Properties (4) to (6) of Lemma R in `notes/GHAT_REPAIR.md`, as far as they are combinatorics.

* (4), the hops. E_S edges join copies of one vertex (`owner_es`), as E_C edges do
  (`owner_att_partner`). A valid copy other than a star centre is joined to the star centre of its
  vertex by one E_S edge, or by two for the copies `L`, `R`, `X` (`star_walk`). If at most three
  corners are cut, some token of each edge `uv` has at most one end at a copy `L`, `R` or `X`, so the
  star centres of `u` and `v` are joined by a walk of at most four arcs (`hop_dart`). A walk of length
  `k` in `G` gives a walk of at most `4k` arcs between the star centres of its ends (`hop_walk`), and
  two copies whose vertices are joined by a walk of length `k` are joined by a walk of at most
  `4k + 4` arcs (`hop_copies`).
* (5), the choice at `s`. If `G` has no loops, every corner in the first face `p_0` of a dual path
  with distinct faces has a flank that is not an edge of the path (`legal_flank`).
* (6), the levels. Let the data of the level before have fewer incised darts and the same cut
  corners. The parent of a token is the token itself if its dart was incised before, and the token
  `(δ, 0)` otherwise (`parent`). The parents of linked tokens are linked (`link_parent`), so every
  piece refines a piece of the level before (`parentPiece`, `piece_parent`), and the end at the host
  of the parent of a token lies on the path of that piece (`pieceOf_att_parent`). This is the
  refinement of Lemma N and the first part of Claim 3 behind Rule M.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor

namespace RotSystem

universe u

/-- `1` for the copies `L`, `R`, `X`, and `0` for star centres and the copies `D`. -/
def Copy.leaf {V E : Type u} : Copy V E → ℕ
  | .star _ => 0
  | .dc _ => 0
  | .lc _ => 1
  | .rc _ => 1
  | .xc _ => 1

theorem Copy.leaf_le_one {V E : Type u} (a : Copy V E) : a.leaf ≤ 1 := by
  cases a <;> simp [Copy.leaf]

namespace RData

variable {E : Type u} [Fintype E] [DecidableEq E] {G : RotSystem E} (S : G.RData)

/-! ### Property (4) -/

/-- E_S edges join copies of one vertex. -/
theorem owner_es {a b : Copy G.Vertex E} (h : S.ES a b) : G.owner a = G.owner b := by
  cases a <;> cases b <;> simp only [ES] at h
  all_goals first
    | exact h.symm
    | (obtain ⟨rfl, -⟩ := h; rfl)

/-- A valid copy other than a star centre is joined to the star centre of its vertex, in both
directions, by `1 + leaf` E_S arcs. -/
theorem star_walk {a : Copy G.Vertex E} (ha : S.Valid a) (hs : ∀ v, a ≠ .star v) {v : G.Vertex}
    (hv : G.owner a = v) :
    (∃ p : FaceDisjoint.Walk S.Arc (.star v) a, p.len = 1 + a.leaf) ∧
      ∃ q : FaceDisjoint.Walk S.Arc a (.star v), q.len = 1 + a.leaf := by
  subst hv
  cases a with
  | star w => exact absurd rfl (hs w)
  | dc c =>
    have h : S.ES (.star (G.tail c)) (.dc c) := rfl
    exact ⟨⟨.cons (.es h) (.nil _), rfl⟩, .cons (.es' h) (.nil _), rfl⟩
  | lc c =>
    have h₁ : S.ES (.star (G.tail c)) (.dc c) := rfl
    have h₂ : S.ES (.dc c) (.lc c) := ⟨rfl, ha⟩
    exact ⟨⟨.cons (.es h₁) (.cons (.es h₂) (.nil _)), rfl⟩,
      .cons (.es' h₂) (.cons (.es' h₁) (.nil _)), rfl⟩
  | rc c =>
    have h₁ : S.ES (.star (G.tail c)) (.dc c) := rfl
    have h₂ : S.ES (.dc c) (.rc c) := ⟨rfl, ha⟩
    exact ⟨⟨.cons (.es h₁) (.cons (.es h₂) (.nil _)), rfl⟩,
      .cons (.es' h₂) (.cons (.es' h₁) (.nil _)), rfl⟩
  | xc c =>
    have h₁ : S.ES (.star (G.tail c)) (.dc c) := rfl
    have h₂ : S.ES (.dc c) (.xc c) := ⟨rfl, ha⟩
    exact ⟨⟨.cons (.es h₁) (.cons (.es h₂) (.nil _)), rfl⟩,
      .cons (.es' h₂) (.cons (.es' h₁) (.nil _)), rfl⟩

/-- The E_R edge of a token joins the star centres of the tail and the head of its dart. -/
theorem token_walk {x : E × Lab} (hx : S.IsTok x) :
    (∃ p : FaceDisjoint.Walk S.Arc (.star (G.tail x.1)) (.star (G.head x.1)),
      p.len = 3 + (S.alpha x).leaf + (S.beta x).leaf) ∧
    ∃ p : FaceDisjoint.Walk S.Arc (.star (G.head x.1)) (.star (G.tail x.1)),
      p.len = 3 + (S.alpha x).leaf + (S.beta x).leaf := by
  obtain ⟨⟨p₁, h₁⟩, q₁, h₁'⟩ := S.star_walk (S.valid_alpha hx) (S.alpha_ne_star x) (S.owner_alpha x)
  obtain ⟨⟨p₂, h₂⟩, q₂, h₂'⟩ := S.star_walk (S.valid_beta hx) (S.beta_ne_star x) (S.owner_beta x)
  refine ⟨⟨p₁.append (.cons (.er ⟨x, hx⟩) q₂), ?_⟩, p₂.append (.cons (.er' ⟨x, hx⟩) q₁), ?_⟩
  · simp only [FaceDisjoint.Walk.len_append, FaceDisjoint.Walk.len_cons, h₁, h₂']
    omega
  · simp only [FaceDisjoint.Walk.len_append, FaceDisjoint.Walk.len_cons, h₂, h₁']
    omega

theorem leaf_alphaD (c : E) :
    (S.alphaD c).leaf = if c ∈ S.cut ∧ S.modeL c = false then 1 else 0 := by
  unfold alphaD
  split_ifs <;> rfl

theorem leaf_betaD (c : E) :
    (S.betaD c).leaf = if c ∈ S.cut ∧ S.modeL c = true then 1 else 0 := by
  unfold betaD
  split_ifs <;> rfl

/-- If every token of an edge has both ends at copies `L`, `R` or `X`, four distinct corners are
cut: the two corners at each end of the edge. -/
theorem four_corners (d : E) (h1 : G.tailCorner d ∈ S.cut ∧ S.modeL (G.tailCorner d) = false)
    (h2 : G.rev d ∈ S.cut ∧ S.modeL (G.rev d) = true)
    (h3 : G.tailCorner (G.rev d) ∈ S.cut ∧ S.modeL (G.tailCorner (G.rev d)) = false)
    (h4 : d ∈ S.cut ∧ S.modeL d = true) : 4 ≤ S.cut.card := by
  have hm : ∀ {a b : E}, S.modeL a = false → S.modeL b = true → a ≠ b := fun ha hb hab => by
    rw [hab, hb] at ha
    exact absurd ha (by decide)
  have hτ : G.tailCorner d ≠ G.tailCorner (G.rev d) := fun h =>
    G.rev_ne d (G.rot.symm.injective h).symm
  have hnd : [G.tailCorner d, G.rev d, G.tailCorner (G.rev d), d].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨hm h1.2 h2.2, hτ, hm h1.2 h4.2⟩, ⟨fun h => hm h3.2 h2.2 h.symm, G.rev_ne d⟩,
      hm h3.2 h4.2⟩
  have hsub : [G.tailCorner d, G.rev d, G.tailCorner (G.rev d), d].toFinset ⊆ S.cut := by
    intro z hz
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact h1.1
    · exact h2.1
    · exact h3.1
    · exact h4.1
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd] at this
  simpa using this

/-- **Property (4) of Lemma R, the hops.** If at most three corners are cut, the star centres of
the two ends of an edge are joined by a walk of at most four arcs. -/
theorem hop_dart (hcut : S.cut.card ≤ 3) (d : E) :
    ∃ p : FaceDisjoint.Walk S.Arc (.star (G.tail d)) (.star (G.head d)), p.len ≤ 4 := by
  have hcorner : ¬ ((G.tailCorner d ∈ S.cut ∧ S.modeL (G.tailCorner d) = false) ∧
      (G.rev d ∈ S.cut ∧ S.modeL (G.rev d) = true) ∧
      (G.tailCorner (G.rev d) ∈ S.cut ∧ S.modeL (G.tailCorner (G.rev d)) = false) ∧
      (d ∈ S.cut ∧ S.modeL d = true)) := fun ⟨h1, h2, h3, h4⟩ => by
    have := S.four_corners d h1 h2 h3 h4
    omega
  have hηr : G.headCorner (G.rev d) = d := G.rev_rev d
  -- the walk through a token of `d`, and through a token of `rev d` read backwards
  have viaD : ∀ l : Lab, S.IsTok (d, l) → ∃ p : FaceDisjoint.Walk S.Arc (.star (G.tail d))
      (.star (G.head d)), p.len = 3 + (S.alpha (d, l)).leaf + (S.beta (d, l)).leaf :=
    fun l h => (S.token_walk h).1
  have tr : ∀ {a a' b : Copy G.Vertex E} (n : ℕ), a = a' →
      (∃ p : FaceDisjoint.Walk S.Arc a b, p.len = n) →
        ∃ p : FaceDisjoint.Walk S.Arc a' b, p.len = n := by
    rintro a a' b n rfl h
    exact h
  have viaR : ∀ l : Lab, S.IsTok (G.rev d, l) → ∃ p : FaceDisjoint.Walk S.Arc (.star (G.tail d))
      (.star (G.head d)), p.len = 3 + (S.alpha (G.rev d, l)).leaf + (S.beta (G.rev d, l)).leaf :=
    fun l h => tr _ (congrArg Copy.star (G.head_rev d)) (S.token_walk h).2
  by_cases hd : d ∈ S.inc
  · have hr : G.rev d ∈ S.inc := (S.inc_rev d).2 hd
    have t1 : S.IsTok (d, .one) := by unfold IsTok; simp [hd]
    have t2 : S.IsTok (d, .two) := by unfold IsTok; simp [hd]
    have t3 : S.IsTok (G.rev d, .one) := by unfold IsTok; simp [hr]
    have t4 : S.IsTok (G.rev d, .two) := by unfold IsTok; simp [hr]
    by_cases c1 : G.tailCorner d ∈ S.cut ∧ S.modeL (G.tailCorner d) = false
    · by_cases c2 : G.rev d ∈ S.cut ∧ S.modeL (G.rev d) = true
      · by_cases c3 : G.tailCorner (G.rev d) ∈ S.cut ∧ S.modeL (G.tailCorner (G.rev d)) = false
        · have c4 : ¬ (d ∈ S.cut ∧ S.modeL d = true) := fun c4 => hcorner ⟨c1, c2, c3, c4⟩
          obtain ⟨p, hp⟩ := viaR .two t4
          refine ⟨p, ?_⟩
          simp only [alpha, beta, hηr, S.leaf_betaD] at hp
          simp only [Copy.leaf, ite_eq_right c4] at hp
          omega
        · obtain ⟨p, hp⟩ := viaR .one t3
          refine ⟨p, ?_⟩
          simp only [alpha, beta, S.leaf_alphaD] at hp
          simp only [Copy.leaf, ite_eq_right c3] at hp
          omega
      · obtain ⟨p, hp⟩ := viaD .two t2
        refine ⟨p, ?_⟩
        simp only [alpha, beta, RotSystem.headCorner, S.leaf_betaD] at hp
        simp only [Copy.leaf, ite_eq_right c2] at hp
        omega
    · obtain ⟨p, hp⟩ := viaD .one t1
      refine ⟨p, ?_⟩
      simp only [alpha, beta, S.leaf_alphaD] at hp
      simp only [Copy.leaf, ite_eq_right c1] at hp
      omega
  · have hr : G.rev d ∉ S.inc := fun h => hd ((S.inc_rev d).1 h)
    have t0 : S.IsTok (d, .zero) := by unfold IsTok; simp [hd]
    have t0' : S.IsTok (G.rev d, .zero) := by unfold IsTok; simp [hr]
    by_cases c12 : (G.tailCorner d ∈ S.cut ∧ S.modeL (G.tailCorner d) = false) ∧
        (G.rev d ∈ S.cut ∧ S.modeL (G.rev d) = true)
    · have c34 : ¬ ((G.tailCorner (G.rev d) ∈ S.cut ∧
          S.modeL (G.tailCorner (G.rev d)) = false) ∧ (d ∈ S.cut ∧ S.modeL d = true)) :=
        fun c34 => hcorner ⟨c12.1, c12.2, c34.1, c34.2⟩
      obtain ⟨p, hp⟩ := viaR .zero t0'
      refine ⟨p, ?_⟩
      simp only [alpha, beta, hηr, S.leaf_alphaD, S.leaf_betaD] at hp
      split_ifs at hp with h3 h4 <;> first | omega | exact absurd ⟨h3, h4⟩ c34
    · obtain ⟨p, hp⟩ := viaD .zero t0
      refine ⟨p, ?_⟩
      simp only [alpha, beta, S.leaf_alphaD, S.leaf_betaD, RotSystem.headCorner] at hp
      split_ifs at hp with h1 h2 <;> first | omega | exact absurd ⟨h1, h2⟩ c12

/-- A walk of length `k` in `G` gives a walk of at most `4k` arcs between the star centres of its
ends. -/
theorem hop_walk (hcut : S.cut.card ≤ 3) : ∀ (p : List E) {u v : G.Vertex}, G.IsWalk u p v →
    ∃ q : FaceDisjoint.Walk S.Arc (.star u) (.star v), q.len ≤ 4 * p.length
  | [], u, v, h => by
    obtain rfl : u = v := h
    exact ⟨.nil _, by simp⟩
  | x :: p, u, v, h => by
    obtain ⟨hx, hp⟩ := h
    subst hx
    obtain ⟨q₁, h₁⟩ := S.hop_dart hcut x
    obtain ⟨q₂, h₂⟩ := hop_walk hcut p hp
    refine ⟨q₁.append q₂, ?_⟩
    simp only [FaceDisjoint.Walk.len_append, List.length_cons]
    omega

/-- Two valid copies other than star centres whose vertices are joined by a walk of length `k` in
`G` are joined by a walk of at most `4k + 4` arcs. -/
theorem hop_copies (hcut : S.cut.card ≤ 3) {a b : Copy G.Vertex E} (ha : S.Valid a)
    (hsa : ∀ v, a ≠ .star v) (hb : S.Valid b) (hsb : ∀ v, b ≠ .star v) {p : List E}
    (hp : G.IsWalk (G.owner a) p (G.owner b)) :
    ∃ q : FaceDisjoint.Walk S.Arc a b, q.len ≤ 4 * p.length + 4 := by
  obtain ⟨-, q₁, h₁⟩ := S.star_walk ha hsa rfl
  obtain ⟨⟨q₂, h₂⟩, -⟩ := S.star_walk hb hsb rfl
  obtain ⟨q, hq⟩ := S.hop_walk hcut p hp
  refine ⟨q₁.append (q.append q₂), ?_⟩
  have := a.leaf_le_one
  have := b.leaf_le_one
  simp only [FaceDisjoint.Walk.len_append]
  omega

end RData

/-! ### Property (5) -/

variable {E : Type u} [Fintype E] [DecidableEq E] (G : RotSystem E)

/-- **Property (5) of Lemma R.** Let `p 0, …, p m` be distinct faces, read by a labelling `fc` of
darts that is constant along the face walk of the note, and let the edge of `e k` have the faces
`p (k - 1)` and `p k` on its two sides. If `G` has no loops, a corner `c` in the face `p 0` has a
flank that is not an edge of the path. -/
theorem legal_flank (hG : ∀ d, G.head d ≠ G.tail d) {F : Type*} (fc : E → F)
    (hfc : ∀ d, fc (G.noteFace d) = fc d) (m : ℕ) (p : ℕ → F) (e : ℕ → E)
    (hp : ∀ i j, i ≤ m → j ≤ m → p i = p j → i = j)
    (he : ∀ k, 1 ≤ k → k ≤ m → (fc (e k) = p (k - 1) ∧ fc (G.rev (e k)) = p k) ∨
      (fc (e k) = p k ∧ fc (G.rev (e k)) = p (k - 1)))
    (c : E) (hc : fc (G.rev c) = p 0) :
    (∀ k, 1 ≤ k → k ≤ m → c ≠ e k ∧ c ≠ G.rev (e k)) ∨
      (∀ k, 1 ≤ k → k ≤ m → G.rot c ≠ e k ∧ G.rot c ≠ G.rev (e k)) := by
  have hrot : fc (G.rot c) = p 0 := by
    rw [← hc, ← hfc (G.rev c)]
    simp [G.rev_rev]
  -- an edge with the face `p 0` on a side is the edge of `e 1`
  have only1 : ∀ k, 1 ≤ k → k ≤ m → ∀ z, (z = e k ∨ z = G.rev (e k)) → fc z = p 0 → k = 1 := by
    intro k hk hkm z hz hz0
    rcases hz with rfl | rfl <;> rcases he k hk hkm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hp (k - 1) 0 (by omega) (by omega) (h1.symm.trans hz0)
      omega
    · have := hp k 0 hkm (by omega) (h1.symm.trans hz0)
      omega
    · have := hp k 0 hkm (by omega) (h2.symm.trans hz0)
      omega
    · have := hp (k - 1) 0 (by omega) (by omega) (h2.symm.trans hz0)
      omega
  by_contra hcon
  obtain ⟨⟨k₁, hk₁, hk₁m, hc₁⟩, ⟨k₂, hk₂, hk₂m, hc₂⟩⟩ :
      (∃ k, 1 ≤ k ∧ k ≤ m ∧ (c = e k ∨ c = G.rev (e k))) ∧
        ∃ k, 1 ≤ k ∧ k ≤ m ∧ (G.rot c = e k ∨ G.rot c = G.rev (e k)) := by
    constructor
    · by_contra h
      exact hcon (.inl fun k hk hkm =>
        ⟨fun h' => h ⟨k, hk, hkm, .inl h'⟩, fun h' => h ⟨k, hk, hkm, .inr h'⟩⟩)
    · by_contra h
      exact hcon (.inr fun k hk hkm =>
        ⟨fun h' => h ⟨k, hk, hkm, .inl h'⟩, fun h' => h ⟨k, hk, hkm, .inr h'⟩⟩)
  -- both flanks are the edge of `e 1`
  have e₁ : k₁ = 1 := by
    rcases hc₁ with h | h
    · exact only1 k₁ hk₁ hk₁m (G.rev c) (.inr (by rw [h])) hc
    · exact only1 k₁ hk₁ hk₁m (G.rev c) (.inl (by rw [h, G.rev_rev])) hc
  have e₂ : k₂ = 1 := only1 k₂ hk₂ hk₂m (G.rot c) hc₂ hrot
  subst e₁ e₂
  -- so `rot c` is `c` or `rev c`; the second is a loop, the first puts `p 0` on both sides
  have hcc : G.rot c = c := by
    have hz : G.rot c = c ∨ G.rot c = G.rev c := by
      rcases hc₁ with h | h <;> rcases hc₂ with h' | h'
      · exact .inl (h'.trans h.symm)
      · rw [h', ← h]
        exact .inr rfl
      · rw [h', h, G.rev_rev]
        exact .inr rfl
      · rw [h', ← h]
        exact .inl rfl
    rcases hz with h | h
    · exact h
    · exfalso
      apply hG c
      show G.tail (G.rev c) = G.tail c
      rw [← h, G.tail_rot]
  have hcf : fc c = p 0 := by
    rw [← hc, ← hfc (G.rev c)]
    simp [G.rev_rev, hcc]
  have hb : fc (e 1) = p 0 ∧ fc (G.rev (e 1)) = p 0 := by
    rcases hc₁ with h | h
    · rw [← h]
      exact ⟨hcf, hc⟩
    · exact ⟨by rw [show e 1 = G.rev c by rw [h, G.rev_rev]]; exact hc, by rw [← h]; exact hcf⟩
  have h01 : p 0 = p 1 := by
    rcases (he 1 le_rfl hk₁m : (fc (e 1) = p 0 ∧ fc (G.rev (e 1)) = p 1) ∨
        (fc (e 1) = p 1 ∧ fc (G.rev (e 1)) = p 0)) with ⟨-, h⟩ | ⟨h, -⟩
    · exact hb.2.symm.trans h
    · exact hb.1.symm.trans h
  have := hp 0 1 (by omega) hk₁m h01
  omega

/-! ### Property (6) -/

namespace RData

variable {G}

/-- The parent of a token at the level before: the token itself if its dart was incised before,
and the token `(δ, 0)` otherwise. -/
def parent (S' : G.RData) (x : E × Lab) : E × Lab := if x.1 ∈ S'.inc then x else (x.1, .zero)

variable (S S' : G.RData)

theorem isTok_parent (hinc : S'.inc ⊆ S.inc) {x : E × Lab} (hx : S.IsTok x) :
    S'.IsTok (S'.parent x) := by
  unfold parent
  split_ifs with h
  · unfold IsTok at hx ⊢
    rw [hx]
    exact ⟨fun h' => absurd (hinc h) h', fun h' => absurd h h'⟩
  · unfold IsTok
    simp [h]

/-- The parents of two linked tokens are linked at the level before. -/
theorem link_parent (hinc : S'.inc ⊆ S.inc) (hcut : S'.cut = S.cut) {x y : E × Lab}
    (hl : S.Link x y) : S'.Link (S'.parent x) (S'.parent y) := by
  obtain ⟨rfl, h1, h2⟩ := hl
  obtain ⟨d, l⟩ := x
  have hs : S.succ (d, l) = (G.noteFace d, S.firstLab (G.noteFace d)) := by
    cases l
    · rfl
    · exact absurd rfl h1
    · rfl
  have hfirst : S'.parent (G.noteFace d, S.firstLab (G.noteFace d)) =
      (G.noteFace d, S'.firstLab (G.noteFace d)) := by
    unfold parent firstLab
    by_cases h' : G.noteFace d ∈ S'.inc
    · have h'' := hinc h'
      simp only [h', h'', ite_true]
    · simp only [h', ite_false]
  refine ⟨?_, ?_, ?_⟩
  · rw [hs, hfirst]
    unfold parent
    split_ifs with h
    · cases l
      · rfl
      · exact absurd rfl h1
      · rfl
    · rfl
  · unfold parent
    split_ifs
    · exact h1
    · simp
  · unfold parent
    split_ifs
    · rwa [hcut]
    · rwa [hcut]

/-- The parent of a token, as a token of the level before. -/
def parentTok (hinc : S'.inc ⊆ S.inc) (x : S.Tok) : S'.Tok :=
  ⟨S'.parent x.1, S.isTok_parent S' hinc x.2⟩

/-- **Lemma N, refinement.** The piece of the level before that a piece refines: the parents of
the tokens of a piece lie in one piece of the level before. -/
def parentPiece (hinc : S'.inc ⊆ S.inc) (hcut : S'.cut = S.cut) : S.Piece → S'.Piece :=
  Quot.lift (fun x => S'.piece (S.parentTok S' hinc x)) fun _ _ h =>
    S'.piece_eq_of_link (S.link_parent S' hinc hcut h)

theorem parentPiece_piece (hinc : S'.inc ⊆ S.inc) (hcut : S'.cut = S.cut) (x : S.Tok) :
    S.parentPiece S' hinc hcut (S.piece x) = S'.piece (S.parentTok S' hinc x) := rfl

/-- Two tokens of one piece have parents in one piece of the level before. -/
theorem piece_parent (hinc : S'.inc ⊆ S.inc) (hcut : S'.cut = S.cut) {x y : S.Tok}
    (h : S.piece x = S.piece y) :
    S'.piece (S.parentTok S' hinc x) = S'.piece (S.parentTok S' hinc y) :=
  congrArg (S.parentPiece S' hinc hcut) h

/-- **Claim 3, first part.** The end at the host of the parent of a token lies on the path of the
piece of the level before that the piece of the token refines. -/
theorem pieceOf_att_parent (hinc : S'.inc ⊆ S.inc) (hcut : S'.cut = S.cut) (x : S.Tok) :
    S'.pieceOf ⟨S'.att (S'.parent x.1), S.parentTok S' hinc x, S'.isEnd_att _⟩ =
      S.parentPiece S' hinc hcut (S.piece x) :=
  S'.pieceOf_att (S.parentTok S' hinc x)

end RData

end RotSystem

end SsspFlow
