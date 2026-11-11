import Mathlib

/-!
# Walks over path colours and copies of trees with three branching path vertices

A walk in the auxiliary graph of the st-connectivity reduction visits vertices of `G` whose colours, read along the
walk, start at `0`, end at `k - 1` and change by exactly one at every step. Such a walk may go back and forth between
neighbouring colours. The first index at which colour `q ≥ 2` is reached is preceded by colours `q - 1` and `q - 2`
(`first_arrival`), which gives a stretch of `k` consecutive walk vertices whose colours at three consecutive
positions are exact (`window`). Attaching leaves of distinct colours to these three vertices gives a copy of the tree
(`tree_copy`).
-/

namespace TreeDetect

/-- Colours read along a walk of length `r`: every step changes the colour by exactly one. -/
def Steps (c : ℕ → ℕ) (r : ℕ) : Prop :=
  ∀ p < r, c (p + 1) = c p + 1 ∨ c p = c (p + 1) + 1

lemma Steps.mono {c : ℕ → ℕ} {r r' : ℕ} (h : Steps c r) (hr : r' ≤ r) : Steps c r' :=
  fun p hp => h p (lt_of_lt_of_le hp hr)

/-- A colour sequence moves by at most one per step. -/
lemma le_add_of_steps {c : ℕ → ℕ} {r : ℕ} (h : Steps c r) :
    ∀ a b, a ≤ b → b ≤ r → c b ≤ c a + (b - a) := by
  intro a b hab hbr
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have := ih (by omega)
    rcases h b (by omega) with h1 | h1 <;> omega

/-- Discrete intermediate values: a value between the first and the last colour is attained. -/
lemma exists_hit {c : ℕ → ℕ} {r : ℕ} (h : Steps c r) (q : ℕ) (h0 : c 0 ≤ q) (hr : q ≤ c r) :
    ∃ p ≤ r, c p = q := by
  induction r with
  | zero => exact ⟨0, le_rfl, by omega⟩
  | succ r ih =>
    by_cases hq : q ≤ c r
    · obtain ⟨p, hp, hcp⟩ := ih (h.mono (Nat.le_succ r)) hq
      exact ⟨p, by omega, hcp⟩
    · rcases h r (by omega) with h1 | h1
      · exact ⟨r + 1, le_rfl, by omega⟩
      · omega

/-- Before the first arrival at `q`, all colours lie below `q`. -/
lemma lt_of_lt_first {c : ℕ → ℕ} {r : ℕ} (h : Steps c r) (q τ : ℕ) (h0 : c 0 < q) (hτr : τ ≤ r)
    (hfirst : ∀ p < τ, c p ≠ q) : ∀ p < τ, c p < q := by
  intro p hp
  induction p with
  | zero => exact h0
  | succ p ih =>
    have := ih (by omega)
    have := hfirst (p + 1) hp
    rcases h p (by omega) with h1 | h1 <;> omega

/-- **First arrival.** If the colours start at `0` and `τ` is the first index with colour `q ≥ 2`, the two
preceding colours are `q - 1` and `q - 2`, and `q ≤ τ`. -/
theorem first_arrival {c : ℕ → ℕ} {r : ℕ} (h : Steps c r) (hc0 : c 0 = 0) (q τ : ℕ) (hq : 2 ≤ q)
    (hτr : τ ≤ r) (hτ : c τ = q) (hfirst : ∀ p < τ, c p ≠ q) :
    q ≤ τ ∧ c (τ - 1) = q - 1 ∧ c (τ - 2) = q - 2 := by
  have hlt := lt_of_lt_first h q τ (by omega) hτr hfirst
  have hqτ : q ≤ τ := by
    have := le_add_of_steps h 0 τ (Nat.zero_le τ) hτr
    omega
  have h1 : c (τ - 1) = q - 1 := by
    have := hlt (τ - 1) (by omega)
    rcases h (τ - 1) (by omega) with h1 | h1
    · rw [show τ - 1 + 1 = τ by omega] at h1; omega
    · rw [show τ - 1 + 1 = τ by omega] at h1; omega
  have h2 : c (τ - 2) = q - 2 := by
    have := hlt (τ - 2) (by omega)
    rcases h (τ - 2) (by omega) with h2 | h2
    · rw [show τ - 2 + 1 = τ - 1 by omega] at h2; omega
    · rw [show τ - 2 + 1 = τ - 1 by omega] at h2; omega
  exact ⟨hqτ, h1, h2⟩

/-- **Window.** If the colours of a walk of length `r` start at `0`, end at `k - 1` and change by one per step,
then for every `i` with `i + 2 < k` there is a start `a` with `a + (k - 1) ≤ r` such that the colours at `a + i`,
`a + i + 1` and `a + i + 2` are exactly `i`, `i + 1` and `i + 2`. -/
theorem window {c : ℕ → ℕ} {r k i : ℕ} (h : Steps c r) (hc0 : c 0 = 0) (hcr : c r = k - 1) (hik : i + 2 < k) :
    ∃ a, a + (k - 1) ≤ r ∧ c (a + i) = i ∧ c (a + i + 1) = i + 1 ∧ c (a + i + 2) = i + 2 := by
  classical
  have hex : ∃ p, p ≤ r ∧ c p = i + 2 := by
    obtain ⟨p, hp, hcp⟩ := exists_hit h (i + 2) (by omega) (by omega)
    exact ⟨p, hp, hcp⟩
  let τ := Nat.find hex
  have hτ : τ ≤ r ∧ c τ = i + 2 := Nat.find_spec hex
  have hfirst : ∀ p < τ, c p ≠ i + 2 := by
    intro p hp hcp
    have hpr : p ≤ r := by omega
    exact Nat.find_min hex hp ⟨hpr, hcp⟩
  obtain ⟨hqτ, h1, h2⟩ := first_arrival h hc0 (i + 2) τ (by omega) hτ.1 hτ.2 hfirst
  have htail : c r ≤ c τ + (r - τ) := le_add_of_steps h τ r hτ.1 le_rfl
  refine ⟨τ - (i + 2), by omega, ?_, ?_, ?_⟩
  · rw [show τ - (i + 2) + i = τ - 2 by omega, h2]; omega
  · rw [show τ - (i + 2) + i + 1 = τ - 1 by omega, h1]; omega
  · rw [show τ - (i + 2) + i + 2 = τ by omega, hτ.2]

/-- Vertices of the tree: the path vertices `0, …, k - 1`, and for `j < 3` the leaves `0, …, d j - 1` attached to
path vertex `i + j`. -/
abbrev TreeV (k : ℕ) (d : Fin 3 → ℕ) := Fin k ⊕ (Σ j : Fin 3, Fin (d j))

/-- The tree: a path on `k` vertices with `d j` leaves at path vertex `i + j`, `j < 3`. -/
def tree (k i : ℕ) (d : Fin 3 → ℕ) : SimpleGraph (TreeV k d) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | .inl a, .inl b => a.1 + 1 = b.1
    | .inl a, .inr l => a.1 = i + l.1.1
    | _, _ => False

/-- **Copies from walks.** Let a walk `w 0, …, w r` in `G` have pairwise distinct vertices, colours below `k` that
start at `0`, end at `k - 1` and change by one per step. Suppose every walk vertex of colour `i + j`, `j < 3`, has
for each `l < d j` a neighbour of colour `lc ⟨j, l⟩`, where the leaf colours `lc` are pairwise distinct and at least
`k`. Then `G` contains the tree as a subgraph. -/
theorem tree_copy {V : Type*} (G : SimpleGraph V) (col : V → ℕ) {k i r : ℕ} (hik : i + 2 < k)
    (d : Fin 3 → ℕ) (lc : (Σ j : Fin 3, Fin (d j)) → ℕ) (hlc : Function.Injective lc) (hlck : ∀ l, k ≤ lc l)
    (w : ℕ → V) (hinj : ∀ p ≤ r, ∀ p' ≤ r, w p = w p' → p = p') (hadj : ∀ p < r, G.Adj (w p) (w (p + 1)))
    (hlt : ∀ p ≤ r, col (w p) < k) (hstep : Steps (fun p => col (w p)) r)
    (h0 : col (w 0) = 0) (hr : col (w r) = k - 1)
    (hleaf : ∀ p ≤ r, ∀ l : (Σ j : Fin 3, Fin (d j)), col (w p) = i + l.1.1 →
      ∃ u, G.Adj (w p) u ∧ col u = lc l) :
    ∃ φ : TreeV k d → V, Function.Injective φ ∧ ∀ x y, (tree k i d).Adj x y → G.Adj (φ x) (φ y) := by
  classical
  obtain ⟨a, har, hci, hci1, hci2⟩ := window hstep h0 hr hik
  have hcol : ∀ l : (Σ j : Fin 3, Fin (d j)), col (w (a + i + l.1.1)) = i + l.1.1 := by
    rintro ⟨⟨j, hj⟩, l⟩
    interval_cases j
    · simpa using hci
    · simpa using hci1
    · simpa using hci2
  have hex : ∀ l : (Σ j : Fin 3, Fin (d j)), ∃ u, G.Adj (w (a + i + l.1.1)) u ∧ col u = lc l := fun l =>
    hleaf _ (by have := l.1.2; omega) l (hcol l)
  choose leaf hleafAdj hleafCol using hex
  let φ : TreeV k d → V := fun x =>
    match x with
    | .inl b => w (a + b.1)
    | .inr l => leaf l
  have hpathcol : ∀ b : Fin k, col (φ (.inl b)) < k := fun b => hlt _ (by have := b.2; omega)
  refine ⟨φ, ?_, ?_⟩
  · rintro (b | l) (b' | l') hbb
    · have := hinj _ (by have := b.2; omega) _ (by have := b'.2; omega) hbb
      exact congrArg Sum.inl (Fin.ext (by omega))
    · have h1 := hpathcol b
      have h2 : col (φ (.inr l')) = lc l' := hleafCol l'
      have h3 := hlck l'
      rw [hbb] at h1
      omega
    · have h1 := hpathcol b'
      have h2 : col (φ (.inr l)) = lc l := hleafCol l
      have h3 := hlck l
      rw [← hbb] at h1
      omega
    · have : lc l = lc l' := by
        have h1 : col (φ (.inr l)) = lc l := hleafCol l
        have h2 : col (φ (.inr l')) = lc l' := hleafCol l'
        rw [← h1, ← h2, hbb]
      exact congrArg Sum.inr (hlc this)
  · intro x y hxy
    rw [tree, SimpleGraph.fromRel_adj] at hxy
    obtain ⟨-, hxy | hxy⟩ := hxy
    · rcases x with b | l <;> rcases y with b' | l' <;> simp only at hxy
      · show G.Adj (w (a + b.1)) (w (a + b'.1))
        rw [show a + b'.1 = a + b.1 + 1 by omega]
        exact hadj _ (by have := b'.2; omega)
      · show G.Adj (w (a + b.1)) (leaf l')
        rw [show a + b.1 = a + i + l'.1.1 by omega]
        exact hleafAdj l'
    · rcases x with b | l <;> rcases y with b' | l' <;> simp only at hxy
      · show G.Adj (w (a + b.1)) (w (a + b'.1))
        rw [show a + b.1 = a + b'.1 + 1 by omega]
        exact (hadj _ (by have := b.2; omega)).symm
      · show G.Adj (leaf l) (w (a + b'.1))
        rw [show a + b'.1 = a + i + l.1.1 by omega]
        exact (hleafAdj l).symm

end TreeDetect
