import SsspFlow.RunPick
import SsspFlow.RunComp
import SsspFlow.SideCorners

/-!
# The computed indices of picked runs

The ranges of the subruns at least halve from one depth to the next, so below depth `ℓ` with
`k - j < 2 ^ ℓ` every subrun is a leaf and computes no index inside its range. A picked node computes
its middle index, `i1` and `i2` of its data when they lie inside the range, and the indices of a side
whose walk visits a corner of that side. In the runs of the levels, the computed indices of a subrun
at depth `ℓ` are fixed from level `ℓ + 1` on, and they are those of the node picked at level `ℓ`.

* `CutPath.Run.subs_len`: the ranges at depth `ℓ`.
* `CutPath.Run.loc_deep`: no computed indices below the depth of the range.
* `CutPath.Live.loc_pickNode`, `CutPath.loc_pickF`: the computed indices of a picked node.
* `CutPath.Run.seq_lkeys`, `CutPath.Run.seq_loc`: the computed indices in the runs of the levels.
-/

set_option autoImplicit false

universe u

namespace SsspFlow

open FourColor
open scoped ENNReal

namespace RotSystem

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace CutPath

section Depth

variable {C : R.CutPath} {g : D → ℝ≥0∞} {hR : R.Planar} {hC : R.Connected}
  {hg : ∀ x, g (R.rev x) = g x}

mutual
/-- **The ranges at depth `ℓ`.** The range of a subrun at depth `ℓ`, less one, times `2 ^ ℓ` is at
most the range of the run less one. -/
theorem Run.subs_len : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ : ℕ), ∀ s ∈ r.subs ℓ, 2 ^ ℓ * (s.2.1.2 - s.2.1.1 - 1) ≤ k - j - 1
  | _, _, _, _, .leaf .., 0, s, hs => by
    simp only [Run.subs, List.mem_singleton] at hs
    subst hs
    simp
  | _, _, _, _, .node .., 0, s, hs => by
    simp only [Run.subs, List.mem_singleton] at hs
    subst hs
    simp
  | _, _, _, _, .leaf .., _ + 1, s, hs => by simp [Run.subs] at hs
  | _, L, j, k, .node hjk hxa _ hxb _ p _ i1 i2 h1 h2 _ _ left right, ℓ + 1, s, hs => by
    have m1 := h1.2 (L.mem_idx (i := (j + k) / 2) (by omega) (by omega) p)
    have m2 := h2.2 (L.mem_idx (i := (j + k) / 2) (by omega) (by omega) p)
    simp only [Run.subs, List.mem_append] at hs
    have e : 2 ^ (ℓ + 1) * (s.2.1.2 - s.2.1.1 - 1) = 2 * (2 ^ ℓ * (s.2.1.2 - s.2.1.1 - 1)) := by ring
    rw [e]
    rcases hs with hs | hs
    · have h := SideA.subs_len left ℓ s hs
      generalize 2 ^ ℓ * (s.2.1.2 - s.2.1.1 - 1) = y at h ⊢
      omega
    · have h := SideB.subs_len right ℓ s hs
      generalize 2 ^ ℓ * (s.2.1.2 - s.2.1.1 - 1) = y at h ⊢
      omega
theorem SideA.subs_len : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ : ℕ),
    ∀ x ∈ s.subs ℓ, 2 ^ ℓ * (x.2.1.2 - x.2.1.1 - 1) ≤ hi - lo - 1
  | _, _, _, _, _, _, _, .overlap .., _, x, hx => by simp [SideA.subs] at hx
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, x, hx => Run.subs_len r ℓ x hx
  | _, _, _, _, _, _, _, .empty _, _, x, hx => by simp [SideA.subs] at hx
theorem SideB.subs_len : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ : ℕ),
    ∀ x ∈ s.subs ℓ, 2 ^ ℓ * (x.2.1.2 - x.2.1.1 - 1) ≤ hi - lo - 1
  | _, _, _, _, _, _, _, .overlap .., _, x, hx => by simp [SideB.subs] at hx
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, x, hx => Run.subs_len r ℓ x hx
  | _, _, _, _, _, _, _, .empty _, _, x, hx => by simp [SideB.subs] at hx
end

/-- A run on a range of at most two indices computes no index inside it. -/
theorem Run.loc_eq_empty {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ} (r : Run hR hC hg Γ L j k)
    (h : k ≤ j + 1) : r.loc = ∅ := by
  cases r with
  | leaf => rfl
  | node hjk => omega

/-- **No computed indices below the depth of the range.** -/
theorem Run.loc_deep {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ} (r : Run hR hC hg Γ L j k)
    {ℓ : ℕ} (h : k - j < 2 ^ ℓ) : ∀ s ∈ r.subs ℓ, s.2.2.loc = ∅ := by
  intro s hs
  refine s.2.2.loc_eq_empty ?_
  have hl := r.subs_len ℓ s hs
  by_contra hc
  have h1 : 2 ^ ℓ * 1 ≤ 2 ^ ℓ * (s.2.1.2 - s.2.1.1 - 1) := Nat.mul_le_mul_left _ (by omega)
  rw [mul_one] at h1
  generalize 2 ^ ℓ * (s.2.1.2 - s.2.1.1 - 1) = y at hl h1
  omega

end Depth

variable {C : R.CutPath} {g₀ : D → ℕ} (hR : R.Planar) (hC : R.Connected)
  (hgc : ∀ x, (Nat.cast ∘ g₀ : D → ℝ≥0∞) (R.rev x) = (Nat.cast ∘ g₀ : D → ℝ≥0∞) x)

namespace Live

variable {Γ : Finset (D × Bool)} (L : C.Live (Nat.cast ∘ g₀) Γ) {j k : ℕ} (hjk : j + 2 ≤ k)
  (hxa : L.xa ≤ j) (hya : L.ya ≤ j) (hxb : k ≤ L.xb) (hyb : k ≤ L.yb)
  {q : List (D × Bool)} (hq : L.Shortest ((j + k) / 2) q) {i1 i2 : ℕ}
  (hI1 : IsLeast (C.idx (L.κ0 ((j + k) / 2)) q) i1) (hI2 : IsGreatest (C.idx (L.κ0 ((j + k) / 2)) q) i2)
  (S : L.Step) (hsub : ∃ p₁ p₃, q = p₁ ++ (List.range S.n).map S.q ++ p₃)

/-- **The computed indices of a picked node**: the middle index, `i1` and `i2` when they lie inside
the range, and the indices of a side whose walk visits a corner of that side. -/
theorem loc_pickNode {t : ℕ} (ht : t ∈ (L.pickNode hR hC hgc hjk hxa hya hxb hyb hq hI1 hI2 S hsub).loc) :
    t = (j + k) / 2 ∨ (t = i1 ∧ j < i1) ∨ (t = i2 ∧ i2 < k) ∨
      ((∃ c, L.CornerA c ∧ L.Visits ((j + k) / 2) q c) ∧ j < t ∧ t ≤ (j + k) / 2) ∨
      ((∃ c, L.CornerB c ∧ L.Visits ((j + k) / 2) q c) ∧ (j + k) / 2 ≤ t ∧ t < k) := by
  unfold pickNode at ht
  rcases ht with h | h | h | ⟨ho, h1, h2⟩ | ⟨ho, h1, h2⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · refine .inr (.inr (.inr (.inl ⟨?_, h1, h2⟩)))
    by_contra hA
    have hA' : ¬ ∃ c, (c = L.κ0 L.xa ∨ c ∈ L.La ∨ c = L.κ1 L.ya) ∧ L.Visits ((j + k) / 2) q c := hA
    rw [dite_eq_right_of_eq_false (eq_false hA')] at ho
    split_ifs at ho
    · exact ho
    · exact ho
  · refine .inr (.inr (.inr (.inr ⟨?_, h1, h2⟩)))
    by_contra hB
    have hB' : ¬ ∃ c, (c = L.κ0 L.xb ∨ c ∈ L.Lb ∨ c = L.κ1 L.yb) ∧ L.Visits ((j + k) / 2) q c := hB
    rw [dite_eq_right_of_eq_false (eq_false hB')] at ho
    split_ifs at ho
    · exact ho
    · exact ho

end Live

variable (P : (Σ Γ' : Finset (D × Bool), C.Live (Nat.cast ∘ g₀) Γ') → ℕ → List (D × Bool) →
  List (D × Bool) → Prop)

/-- **The computed indices of the picking graft.** If an annulus that is not a leaf has data whose walk
and step darts satisfy `P`, every computed index of the picked run is one of a node with such data. -/
theorem loc_pickF {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ} {j k : ℕ}
    (r : Run hR hC hgc Γ L j k)
    (h : j + 2 ≤ k → Nonempty {d : NodeData L j k // P ⟨Γ, L⟩ ((j + k) / 2) d.q d.S.darts})
    {t : ℕ} (ht : t ∈ (pickF hR hC hgc P r).loc) :
    ∃ d : NodeData L j k, P ⟨Γ, L⟩ ((j + k) / 2) d.q d.S.darts ∧
      (t = (j + k) / 2 ∨ (t = d.i1 ∧ j < d.i1) ∨ (t = d.i2 ∧ d.i2 < k) ∨
        ((∃ c, L.CornerA c ∧ L.Visits ((j + k) / 2) d.q c) ∧ j < t ∧ t ≤ (j + k) / 2) ∨
        ((∃ c, L.CornerB c ∧ L.Visits ((j + k) / 2) d.q c) ∧ (j + k) / 2 ≤ t ∧ t < k)) := by
  unfold pickF at ht
  by_cases hn : Nonempty {d : NodeData L j k // P ⟨Γ, L⟩ ((j + k) / 2) d.q d.S.darts}
  · rw [dite_eq_left_of_eq_true (eq_true hn)] at ht
    exact ⟨(Classical.choice hn).1, (Classical.choice hn).2,
      Live.loc_pickNode _ _ _ _ _ _ _ _ _ _ _ _ _ _ ht⟩
  · rw [dite_eq_right_of_eq_false (eq_false hn)] at ht
    cases r with
    | leaf => exact absurd ht (Set.notMem_empty _)
    | node hjk => exact absurd (h hjk) hn

section Seq

variable {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ} {j k : ℕ}
  (Pof : ℕ → Run hR hC hgc Γ L j k → (Σ Γ' : Finset (D × Bool), C.Live (Nat.cast ∘ g₀) Γ') → ℕ →
    List (D × Bool) → List (D × Bool) → Prop)
  (r₀ : Run hR hC hgc Γ L j k)

/-- The subruns at depth `ℓ`, up to annuli, ranges and computed indices, are fixed from level `ℓ + 1`
on. -/
theorem Run.seq_lkeys {ℓ m : ℕ} (h : ℓ < m) :
    ((r₀.seq hR hC hgc Pof m).subs ℓ).map Sub.lkey = ((r₀.seq hR hC hgc Pof (ℓ + 1)).subs ℓ).map Sub.lkey := by
  induction m, (show ℓ + 1 ≤ m from h) using Nat.le_induction with
  | base => rfl
  | succ m hm ih => rw [← ih (by omega)]; exact Run.lkey_subs_graft _ _ ℓ m (by omega)

/-- **The computed indices in the runs of the levels.** If at level `ℓ` every subrun at depth `ℓ` on an
annulus that is not a leaf has data that satisfy the choice of that level, then every computed index
of a subrun at depth `ℓ` of the run of a later level is one of a node with such data, on the annulus
and range of a subrun at depth `ℓ` of the run of level `ℓ`. -/
theorem Run.seq_loc {ℓ m : ℕ} (h : ℓ < m)
    (hP : ∀ s ∈ (r₀.seq hR hC hgc Pof ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
      Nonempty {d : NodeData s.1.2 s.2.1.1 s.2.1.2 //
        Pof ℓ (r₀.seq hR hC hgc Pof ℓ) s.1 ((s.2.1.1 + s.2.1.2) / 2) d.q d.S.darts})
    {s : Sub C hR hC hgc} (hs : s ∈ (r₀.seq hR hC hgc Pof m).subs ℓ) {t : ℕ} (ht : t ∈ s.2.2.loc) :
    ∃ s' ∈ (r₀.seq hR hC hgc Pof ℓ).subs ℓ, s'.1 = s.1 ∧ s'.2.1 = s.2.1 ∧
      ∃ d : NodeData s'.1.2 s'.2.1.1 s'.2.1.2,
        Pof ℓ (r₀.seq hR hC hgc Pof ℓ) s'.1 ((s'.2.1.1 + s'.2.1.2) / 2) d.q d.S.darts ∧
        (t = (s'.2.1.1 + s'.2.1.2) / 2 ∨ (t = d.i1 ∧ s'.2.1.1 < d.i1) ∨ (t = d.i2 ∧ d.i2 < s'.2.1.2) ∨
          ((∃ c, s'.1.2.CornerA c ∧ s'.1.2.Visits ((s'.2.1.1 + s'.2.1.2) / 2) d.q c) ∧
            s'.2.1.1 < t ∧ t ≤ (s'.2.1.1 + s'.2.1.2) / 2) ∨
          ((∃ c, s'.1.2.CornerB c ∧ s'.1.2.Visits ((s'.2.1.1 + s'.2.1.2) / 2) d.q c) ∧
            (s'.2.1.1 + s'.2.1.2) / 2 ≤ t ∧ t < s'.2.1.2)) := by
  have hk : Sub.lkey s ∈ ((r₀.seq hR hC hgc Pof (ℓ + 1)).subs ℓ).map Sub.lkey := by
    rw [← r₀.seq_lkeys hR hC hgc Pof h]
    exact List.mem_map_of_mem hs
  obtain ⟨s₁, hs₁, he⟩ := List.mem_map.1 hk
  rw [show r₀.seq hR hC hgc Pof (ℓ + 1) = (r₀.seq hR hC hgc Pof ℓ).graft
    (fun r => pickF hR hC hgc (Pof ℓ (r₀.seq hR hC hgc Pof ℓ)) r) ℓ from rfl, Run.subs_graft_self] at hs₁
  obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs₁
  simp only [Sub.lkey, Prod.mk.injEq] at he
  obtain ⟨e1, e2, e3⟩ := he
  have ht' : t ∈ (pickF hR hC hgc (Pof ℓ (r₀.seq hR hC hgc Pof ℓ)) s'.2.2).loc := by
    rw [e3]; exact ht
  obtain ⟨d, hd, hdis⟩ := loc_pickF hR hC hgc _ s'.2.2 (hP s' hs') ht'
  exact ⟨s', hs', e1, e2, d, hd, hdis⟩

end Seq

end CutPath

end RotSystem

end SsspFlow
