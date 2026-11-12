import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The primal-dual insertion

`notes/MATCHING.md`, Section 5, for a new vertex `h` on the side `A`; the side `B` is the same statement with
`A` and `B` swapped. `update_ok` is the dual update, and `flip` follows a simple alternating path by moving the
one free hole along it, one exchange at a time. Simplicity is the hypothesis `L.Nodup` of `flip`.
`optimal` is weak duality.
-/

namespace PlanarMatching

open Finset

variable {A B : Type*} [DecidableEq A] [DecidableEq B]

/-- A set of pairs in which every vertex occurs at most once. -/
def IsMatching (M : Finset (A × B)) : Prop :=
  (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q) ∧ (∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q)

def FreeA (M : Finset (A × B)) (a : A) : Prop := ∀ p ∈ M, p.1 ≠ a
def FreeB (M : Finset (A × B)) (b : B) : Prop := ∀ p ∈ M, p.2 ≠ b

/-- Dual feasibility (D1) on an edge set. -/
structure Feasible (E : Set (A × B)) (w : A × B → ℤ) (y : A → ℤ) (z : B → ℤ) : Prop where
  nonnegA : ∀ a, 0 ≤ y a
  nonnegB : ∀ b, 0 ≤ z b
  cover : ∀ e ∈ E, w e ≤ y e.1 + z e.2

/-- Tightness (D2) and zero duals on free vertices (D3). -/
structure Slack (M : Finset (A × B)) (w : A × B → ℤ) (y : A → ℤ) (z : B → ℤ) : Prop where
  tight : ∀ e ∈ M, y e.1 + z e.2 = w e
  freeA : ∀ a, FreeA M a → y a = 0
  freeB : ∀ b, FreeB M b → z b = 0

/-- Weak duality: a matching that satisfies (D1) to (D3) has the largest weight. -/
theorem optimal [Fintype A] [Fintype B] {E : Set (A × B)} {w : A × B → ℤ} {y : A → ℤ} {z : B → ℤ}
    {M N : Finset (A × B)} (hF : Feasible E w y z) (hM : IsMatching M) (hS : Slack M w y z)
    (hN : IsMatching N) (hNE : ∀ e ∈ N, e ∈ E) : ∑ e ∈ N, w e ≤ ∑ e ∈ M, w e := by
  classical
  -- the duals of the vertices covered by a matching sum over its edges
  have cov : ∀ P : Finset (A × B), IsMatching P →
      ∑ e ∈ P, (y e.1 + z e.2) = ∑ a ∈ P.image Prod.fst, y a + ∑ b ∈ P.image Prod.snd, z b := by
    intro P hP
    rw [sum_add_distrib, sum_image (f := y), sum_image (f := z)]
    · intro p hp q hq e; exact hP.2 p hp q hq e
    · intro p hp q hq e; exact hP.1 p hp q hq e
  have upper : ∑ e ∈ N, w e ≤ ∑ a, y a + ∑ b, z b := by
    calc ∑ e ∈ N, w e ≤ ∑ e ∈ N, (y e.1 + z e.2) := sum_le_sum fun e he => hF.cover e (hNE e he)
      _ = ∑ a ∈ N.image Prod.fst, y a + ∑ b ∈ N.image Prod.snd, z b := cov N hN
      _ ≤ ∑ a, y a + ∑ b, z b := by
        apply add_le_add
        · exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun a _ _ => hF.nonnegA a
        · exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun b _ _ => hF.nonnegB b
  have exact : ∑ e ∈ M, w e = ∑ a, y a + ∑ b, z b := by
    calc ∑ e ∈ M, w e = ∑ e ∈ M, (y e.1 + z e.2) := (sum_congr rfl fun e he => hS.tight e he).symm
      _ = ∑ a ∈ M.image Prod.fst, y a + ∑ b ∈ M.image Prod.snd, z b := cov M hM
      _ = ∑ a, y a + ∑ b, z b := by
        congr 1
        · apply sum_subset (subset_univ _)
          intro a _ ha
          apply hS.freeA
          intro p hp e
          exact ha (mem_image.mpr ⟨p, hp, e⟩)
        · apply sum_subset (subset_univ _)
          intro b _ hb
          apply hS.freeB
          intro p hp e
          exact hb (mem_image.mpr ⟨p, hp, e⟩)
  linarith

/-- The dual update of the note. `da`, `db` are the distances from `h`, capped at any value `≥ δ` for vertices
out of reach, so they satisfy the arc inequalities everywhere. The result satisfies (D1), (D2), and (D3) on all free
vertices of `M` except `h`. -/
theorem update_ok {E : Set (A × B)} {w : A × B → ℤ} {y : A → ℤ} {z : B → ℤ} {M : Finset (A × B)} {h : A}
    (hF : Feasible E w y z) (htight : ∀ e ∈ M, y e.1 + z e.2 = w e)
    (hfreeA : ∀ a, a ≠ h → FreeA M a → y a = 0) (hfreeB : ∀ b, FreeB M b → z b = 0)
    {da : A → ℤ} {db : B → ℤ} {δ : ℤ}
    (harc : ∀ e ∈ E, e ∉ M → db e.2 ≤ da e.1 + (y e.1 + z e.2 - w e))
    (hmatched : ∀ e ∈ M, da e.1 = db e.2)
    (hδA : ∀ a, δ ≤ da a + y a) (hδB : ∀ b, FreeB M b → δ ≤ db b) :
    let y' := fun a => y a - max 0 (δ - da a)
    let z' := fun b => z b + max 0 (δ - db b)
    Feasible E w y' z' ∧ (∀ e ∈ M, y' e.1 + z' e.2 = w e) ∧ (∀ a, a ≠ h → FreeA M a → y' a = 0) ∧
      (∀ b, FreeB M b → z' b = 0) := by
  intro y' z'
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a
    have := hδA a
    have h1 := hF.nonnegA a
    simp only [y']
    rcases max_cases 0 (δ - da a) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> linarith
  · intro b
    have h1 := hF.nonnegB b
    have h2 : 0 ≤ max 0 (δ - db b) := le_max_left _ _
    simp only [z']
    linarith
  · intro e he
    have h1 := hF.cover e he
    simp only [y', z']
    by_cases hm : e ∈ M
    · have h2 := hmatched e hm
      rw [h2]
      linarith
    · have h2 := harc e he hm
      rcases max_cases 0 (δ - da e.1) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
        rcases max_cases 0 (δ - db e.2) with ⟨e2, _⟩ | ⟨e2, _⟩ <;> rw [e1, e2] <;> linarith
  · intro e he
    have h1 := htight e he
    have h2 := hmatched e he
    simp only [y', z']
    rw [h2]
    linarith
  · intro a hne hfree
    have h1 := hfreeA a hne hfree
    have h2 := hδA a
    simp only [y', h1]
    rw [h1] at h2
    have : max 0 (δ - da a) = 0 := max_eq_left (by linarith)
    rw [this]; ring
  · intro b hfree
    have h1 := hfreeB b hfree
    have h2 := hδB b hfree
    simp only [z', h1]
    have : max 0 (δ - db b) = 0 := max_eq_left (by linarith)
    rw [this]; ring

omit [DecidableEq A] [DecidableEq B] in
/-- An arc with `db b = da a + ℓ`, `da a ≤ δ` and `db b ≤ δ` is tight after the update. -/
theorem tight_after {w : A × B → ℤ} {y : A → ℤ} {z : B → ℤ} {da : A → ℤ} {db : B → ℤ} {δ : ℤ} {e : A × B}
    (hl : db e.2 = da e.1 + (y e.1 + z e.2 - w e)) (h1 : da e.1 ≤ δ) (h2 : db e.2 ≤ δ) :
    (y e.1 - max 0 (δ - da e.1)) + (z e.2 + max 0 (δ - db e.2)) = w e := by
  rw [max_eq_right (by linarith), max_eq_right (by linarith)]
  linarith

/-- The state during a flip: `M` is a matching, all its edges are tight, `hole` is free, and every other free vertex
has dual zero. -/
structure Hole (E : Set (A × B)) (w : A × B → ℤ) (y : A → ℤ) (z : B → ℤ) (M : Finset (A × B)) (hole : A) :
    Prop where
  sub : ∀ e ∈ M, e ∈ E
  match_ : IsMatching M
  tight : ∀ e ∈ M, y e.1 + z e.2 = w e
  free : FreeA M hole
  freeA : ∀ a, a ≠ hole → FreeA M a → y a = 0
  freeB : ∀ b, FreeB M b → z b = 0

/-- One exchange: the hole takes the partner of `a`, and `a` becomes the hole. -/
theorem exchange {E : Set (A × B)} {w : A × B → ℤ} {y : A → ℤ} {z : B → ℤ} {M : Finset (A × B)} {h a : A} {b : B}
    (hH : Hole E w y z M h) (hab : (a, b) ∈ M) (hE : (h, b) ∈ E) (ht : y h + z b = w (h, b)) :
    Hole E w y z (insert (h, b) (M.erase (a, b))) a := by
  have hna : a ≠ h := fun e => hH.free _ hab e
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · exact hE
    · exact hH.sub e (mem_of_mem_erase he)
  · intro p hp q hq e
    rcases mem_insert.mp hp with rfl | hp <;> rcases mem_insert.mp hq with rfl | hq
    · rfl
    · exact absurd e.symm (hH.free q (mem_of_mem_erase hq))
    · exact absurd e (hH.free p (mem_of_mem_erase hp))
    · exact hH.match_.1 p (mem_of_mem_erase hp) q (mem_of_mem_erase hq) e
  · intro p hp q hq e
    rcases mem_insert.mp hp with rfl | hp <;> rcases mem_insert.mp hq with rfl | hq
    · rfl
    · have := hH.match_.2 _ hab _ (mem_of_mem_erase hq) e
      exact absurd this.symm (ne_of_mem_erase hq)
    · have := hH.match_.2 _ hab _ (mem_of_mem_erase hp) e.symm
      exact absurd this.symm (ne_of_mem_erase hp)
    · exact hH.match_.2 p (mem_of_mem_erase hp) q (mem_of_mem_erase hq) e
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · exact ht
    · exact hH.tight e (mem_of_mem_erase he)
  · intro p hp e
    rcases mem_insert.mp hp with rfl | hp
    · exact hna e.symm
    · have := hH.match_.1 _ hab _ (mem_of_mem_erase hp) e.symm
      exact (ne_of_mem_erase hp) this.symm
  · intro c hc hfree
    by_cases hch : c = h
    · exact absurd hch.symm (hfree (h, b) (mem_insert_self _ _))
    · apply hH.freeA c hch
      intro p hp e
      by_cases hpe : p = (a, b)
      · subst hpe; exact hc e.symm
      · exact hfree p (mem_insert_of_mem (mem_erase.mpr ⟨hpe, hp⟩)) e
  · intro c hfree
    apply hH.freeB c
    intro p hp e
    by_cases hpe : p = (a, b)
    · subst hpe
      exact hfree (h, b) (mem_insert_self _ _) e
    · exact hfree p (mem_insert_of_mem (mem_erase.mpr ⟨hpe, hp⟩)) e

/-- Flip along a simple alternating path. `L` lists the matched pairs `(a_i, b_i)` of the path in order, and the path
leaves `h` for `b_1`, then each `a_i` for `b_{i+1}`. The arcs that enter a `b_i` are edges and tight. After the flip the
hole is the last `a`, or `h` when `L` is empty, and free vertices of `B` stay free. `L.Nodup` is where a simple path is
needed. -/
theorem flip {E : Set (A × B)} {w : A × B → ℤ} {y : A → ℤ} {z : B → ℤ} :
    ∀ (L : List (A × B)) {M : Finset (A × B)} {h : A}, Hole E w y z M h → L.Nodup → (∀ p ∈ L, p ∈ M) →
      (L.IsChain fun p q => (p.1, q.2) ∈ E ∧ y p.1 + z q.2 = w (p.1, q.2)) →
      (∀ p ∈ L.head?, (h, p.2) ∈ E ∧ y h + z p.2 = w (h, p.2)) →
      ∃ M', Hole E w y z M' ((L.getLast?.map Prod.fst).getD h) ∧ ∀ b, FreeB M b → FreeB M' b
  | [], M, h, hH, _, _, _, _ => ⟨M, hH, fun _ hb => hb⟩
  | p :: L, M, h, hH, hnd, hmem, hch, hhead => by
    have hp := hmem p List.mem_cons_self
    obtain ⟨a, b⟩ := p
    obtain ⟨hE, ht⟩ := hhead (a, b) (by simp)
    have hex := exchange hH hp hE ht
    have hnd' := List.nodup_cons.mp hnd
    have hmem' : ∀ q ∈ L, q ∈ insert (h, b) (M.erase (a, b)) := by
      intro q hq
      refine mem_insert_of_mem (mem_erase.mpr ⟨?_, hmem q (List.mem_cons_of_mem _ hq)⟩)
      rintro rfl
      exact hnd'.1 hq
    have hch' : L.IsChain fun p q => (p.1, q.2) ∈ E ∧ y p.1 + z q.2 = w (p.1, q.2) := hch.tail
    have hhead' : ∀ q ∈ L.head?, (a, q.2) ∈ E ∧ y a + z q.2 = w (a, q.2) := by
      intro q hq
      cases L with
      | nil => simp at hq
      | cons c L' =>
        have : q = c := by simpa using hq.symm
        subst this
        exact (List.isChain_cons_cons.mp hch).1
    obtain ⟨M', hM', hfree⟩ := flip L hex hnd'.2 hmem' hch' hhead'
    have hfree' : ∀ c, FreeB M c → FreeB M' c := by
      intro c hc
      apply hfree
      intro q hq e
      rcases mem_insert.mp hq with rfl | hq
      · exact hc _ hp e
      · exact hc q (mem_of_mem_erase hq) e
    refine ⟨M', ?_, hfree'⟩
    cases L with
    | nil => exact hM'
    | cons c L' =>
      have e : ((a, b) :: c :: L').getLast? = (c :: L').getLast? := List.getLast?_cons_cons
      rw [e]
      have hsome : ∃ q, (c :: L').getLast? = some q := ⟨_, List.getLast?_eq_some_getLast (by simp)⟩
      obtain ⟨q, hq⟩ := hsome
      rw [hq] at hM' ⊢
      exact hM'

/-- The hole gets a free partner, as when the path ends on a free vertex of `B`. -/
theorem fill {E : Set (A × B)} {w : A × B → ℤ} {y : A → ℤ} {z : B → ℤ} {M : Finset (A × B)} {h : A} {b : B}
    (hH : Hole E w y z M h) (hb : FreeB M b) (ht : y h + z b = w (h, b)) :
    IsMatching (insert (h, b) M) ∧ Slack (insert (h, b) M) w y z := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · intro p hp q hq e
    rcases mem_insert.mp hp with rfl | hp <;> rcases mem_insert.mp hq with rfl | hq
    · rfl
    · exact absurd e.symm (hH.free q hq)
    · exact absurd e (hH.free p hp)
    · exact hH.match_.1 p hp q hq e
  · intro p hp q hq e
    rcases mem_insert.mp hp with rfl | hp <;> rcases mem_insert.mp hq with rfl | hq
    · rfl
    · exact absurd e.symm (hb q hq)
    · exact absurd e (hb p hp)
    · exact hH.match_.2 p hp q hq e
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · exact ht
    · exact hH.tight e he
  · intro a hfree
    have hne : a ≠ h := fun e => hfree (h, b) (mem_insert_self _ _) e.symm
    exact hH.freeA a hne fun p hp => hfree p (mem_insert_of_mem hp)
  · intro c hfree
    exact hH.freeB c fun p hp => hfree p (mem_insert_of_mem hp)

omit [DecidableEq A] [DecidableEq B] in
/-- A hole with dual zero is an ordinary free vertex, as when the path ends on an `a` with `y' a = 0`. -/
theorem close {E : Set (A × B)} {w : A × B → ℤ} {y : A → ℤ} {z : B → ℤ} {M : Finset (A × B)} {h : A}
    (hH : Hole E w y z M h) (h0 : y h = 0) : IsMatching M ∧ Slack M w y z :=
  ⟨hH.match_, hH.tight, fun a hfree => by
    by_cases e : a = h
    · rw [e, h0]
    · exact hH.freeA a e hfree, hH.freeB⟩

/-- One insertion, all together. Start from duals that are feasible and a matching that satisfies (D2) and (D3) except at
the free vertex `h`. Distances give the update. A simple path of tight arcs leads from `h` to its end, which is either a
vertex of `A` whose updated dual is zero, or a free vertex of `B`. The flipped matching is optimal on `E` and the updated
duals certify it. The arc conditions are stated for the updated duals; `tight_after` supplies them from the distances. -/
theorem insertion [Fintype A] [Fintype B] {E : Set (A × B)} {w : A × B → ℤ} {y : A → ℤ} {z : B → ℤ}
    {M : Finset (A × B)} {h : A} (hF : Feasible E w y z) (hsub : ∀ e ∈ M, e ∈ E) (hM : IsMatching M) (hh : FreeA M h)
    (htight : ∀ e ∈ M, y e.1 + z e.2 = w e) (hfreeA : ∀ a, a ≠ h → FreeA M a → y a = 0)
    (hfreeB : ∀ b, FreeB M b → z b = 0)
    {da : A → ℤ} {db : B → ℤ} {δ : ℤ}
    (harc : ∀ e ∈ E, e ∉ M → db e.2 ≤ da e.1 + (y e.1 + z e.2 - w e))
    (hmatched : ∀ e ∈ M, da e.1 = db e.2)
    (hδA : ∀ a, δ ≤ da a + y a) (hδB : ∀ b, FreeB M b → δ ≤ db b)
    (L : List (A × B)) (hnd : L.Nodup) (hmem : ∀ p ∈ L, p ∈ M)
    (hch : L.IsChain fun p q => (p.1, q.2) ∈ E ∧
      (y p.1 - max 0 (δ - da p.1)) + (z q.2 + max 0 (δ - db q.2)) = w (p.1, q.2))
    (hhead : ∀ p ∈ L.head?, (h, p.2) ∈ E ∧
      (y h - max 0 (δ - da h)) + (z p.2 + max 0 (δ - db p.2)) = w (h, p.2))
    (hend : (y ((L.getLast?.map Prod.fst).getD h) - max 0 (δ - da ((L.getLast?.map Prod.fst).getD h)) = 0) ∨
      ∃ b, FreeB M b ∧ ((L.getLast?.map Prod.fst).getD h, b) ∈ E ∧
        (y ((L.getLast?.map Prod.fst).getD h) - max 0 (δ - da ((L.getLast?.map Prod.fst).getD h))) +
          (z b + max 0 (δ - db b)) = w ((L.getLast?.map Prod.fst).getD h, b)) :
    ∃ M', IsMatching M' ∧ (∀ e ∈ M', e ∈ E) ∧ ∀ N : Finset (A × B), IsMatching N → (∀ e ∈ N, e ∈ E) →
      ∑ e ∈ N, w e ≤ ∑ e ∈ M', w e := by
  obtain ⟨hF', ht', hA', hB'⟩ := update_ok hF htight hfreeA hfreeB harc hmatched hδA hδB
  have hH : Hole E w (fun a => y a - max 0 (δ - da a)) (fun b => z b + max 0 (δ - db b)) M h :=
    ⟨hsub, hM, ht', hh, hA', hB'⟩
  obtain ⟨M', hM', hfree⟩ := flip L hH hnd hmem hch hhead
  rcases hend with h0 | ⟨b, hb, hbE, hbt⟩
  · obtain ⟨hm, hs⟩ := close hM' h0
    exact ⟨M', hm, hM'.sub, fun N hN hNE => optimal hF' hm hs hN hNE⟩
  · obtain ⟨hm, hs⟩ := fill hM' (hfree b hb) hbt
    have hsub' : ∀ e ∈ insert (((L.getLast?.map Prod.fst).getD h), b) M', e ∈ E := by
      intro e he
      rcases mem_insert.mp he with rfl | he
      · exact hbE
      · exact hM'.sub e he
    exact ⟨_, hm, hsub', fun N hN hNE => optimal hF' hm hs hN hNE⟩

end PlanarMatching
