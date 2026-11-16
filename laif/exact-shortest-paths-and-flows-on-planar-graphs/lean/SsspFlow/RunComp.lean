import SsspFlow.RunKappa
import SsspFlow.RunGraft

/-!
# The indices computed inside the ranges of a run

Each annulus of a run that is not a leaf computes its length at its middle index, at `i1` and `i2` when
they lie strictly inside its range, and, for each side that is an overlap, at the indices of the side
that are not ends of its range. Every index of a computed pair of the run is then an end of the range
of the run or such an index of one of its subruns.

* `CutPath.Run.loc`: the indices computed at the top of a run, strictly inside its range.
* `CutPath.Run.loc_lt`: the indices of `loc` lie strictly inside the range.
* `CutPath.Run.loc_corners`: at an index of `loc` of a subrun, its corners are those of the top annulus.
* `CutPath.Run.lkey_subs_graft`: a deeper graft keeps the annuli, ranges and `loc` of the subruns.
* `CutPath.Run.vals_cover`: every index of a computed pair is an end of the range or an index of `loc`
  of a subrun.
-/

set_option autoImplicit false

universe u

namespace SsspFlow

open FourColor
open scoped ENNReal

namespace RotSystem

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace CutPath

variable {C : R.CutPath} {g : D → ℝ≥0∞} {hR : R.Planar} {hC : R.Connected}
  {hg : ∀ x, g (R.rev x) = g x}

/-- The side of `κ0(x_a)` is an overlap. -/
def SideA.Ov {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} : SideA hR hC hg Γ L p i S lo hi → Prop
  | .overlap .. => True
  | .child .. => False
  | .empty .. => False

/-- The side of `κ0(x_b)` is an overlap. -/
def SideB.Ov {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} : SideB hR hC hg Γ L p i S lo hi → Prop
  | .overlap .. => True
  | .child .. => False
  | .empty .. => False

/-- The indices computed at the top of a run: for an annulus that is not a leaf, its middle index,
`i1` and `i2` when they lie strictly inside the range, and the indices of an overlap side that are not
ends of the range. -/
def Run.loc : {Γ : Finset (D × Bool)} → {L : C.Live g Γ} → {j k : ℕ} →
    Run hR hC hg Γ L j k → Set ℕ
  | _, _, _, _, .leaf .. => ∅
  | _, _, j, k, .node _ _ _ _ _ _ _ i1 i2 _ _ _ _ left right =>
    {t | t = (j + k) / 2 ∨ (t = i1 ∧ j < i1) ∨ (t = i2 ∧ i2 < k) ∨
      (left.Ov ∧ j < t ∧ t ≤ (j + k) / 2) ∨ (right.Ov ∧ (j + k) / 2 ≤ t ∧ t < k)}

/-- **The indices of `loc` lie strictly inside the range.** -/
theorem Run.loc_lt {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ} :
    ∀ (r : Run hR hC hg Γ L j k), ∀ t ∈ r.loc, j < t ∧ t < k
  | .leaf .., _, ht => absurd ht (Set.notMem_empty _)
  | .node hjk hxa _ hxb _ p _ i1 i2 h1 h2 _ _ _ _, t, ht => by
    have m1 := h1.2 (L.mem_idx (i := (j + k) / 2) (by omega) (by omega) p)
    have m2 := h2.2 (L.mem_idx (i := (j + k) / 2) (by omega) (by omega) p)
    rcases ht with rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨-, h, h'⟩ | ⟨-, h, h'⟩ <;> omega

/-- **The corners at an index of `loc`.** At an index of `loc` of a subrun, the corners of its annulus
are those of the top annulus, and the index lies in the ranges of its annulus. -/
theorem Run.loc_corners {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ} (r : Run hR hC hg Γ L j k)
    (ℓ : ℕ) {s : Sub C hR hC hg} (hs : s ∈ r.subs ℓ) {t : ℕ} (ht : t ∈ s.2.2.loc) :
    s.1.2.κ0 t = L.κ0 t ∧ s.1.2.κ1 t = L.κ1 t ∧
      s.1.2.xa ≤ t ∧ s.1.2.ya ≤ t ∧ t ≤ s.1.2.xb ∧ t ≤ s.1.2.yb := by
  have hA : s.1 ∈ r.nodes ℓ := by
    rw [Run.nodes_eq_subs]
    exact List.mem_map_of_mem hs
  obtain ⟨-, -, -, -, h0, h1⟩ := r.below_nodes ℓ s.1 hA
  obtain ⟨-, hxa, hya, hxb, hyb⟩ := s.2.2.bounds
  obtain ⟨l1, l2⟩ := s.2.2.loc_lt t ht
  exact ⟨h0 _ (by omega) (by omega), h1 _ (by omega) (by omega), by omega, by omega, by omega, by omega⟩

mutual
/-- **Every computed index is covered.** The index of a computed pair of a run is an end of its range
or an index of `loc` of one of its subruns. -/
theorem Run.vals_cover : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k), ∀ v ∈ r.vals, v.1 = j ∨ v.1 = k ∨ ∃ ℓ, ∃ s ∈ r.subs ℓ, v.1 ∈ s.2.2.loc
  | _, _, _, _, .leaf .., v, hv => by
    simp only [Run.vals, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
  | Γ, L, j, k, .node hjk hxa hya hxb hyb p hp i1 i2 h1 h2 S sub left right, v, hv => by
    have h0 : ∀ t, (t = (j + k) / 2 ∨ (t = i1 ∧ j < i1) ∨ (t = i2 ∧ i2 < k) ∨
        (left.Ov ∧ j < t ∧ t ≤ (j + k) / 2) ∨ (right.Ov ∧ (j + k) / 2 ≤ t ∧ t < k)) →
        ∃ ℓ, ∃ s ∈ (Run.node hjk hxa hya hxb hyb p hp i1 i2 h1 h2 S sub left right :
          Run hR hC hg Γ L j k).subs ℓ, t ∈ s.2.2.loc := fun t ht =>
      ⟨0, _, List.mem_singleton_self _, ht⟩
    simp only [Run.vals, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with ((rfl | rfl | rfl) | hl) | hr
    · exact .inr (.inr (h0 _ (.inl rfl)))
    · by_cases h : j < i1
      · exact .inr (.inr (h0 _ (.inr (.inl ⟨max_eq_left h.le, h⟩))))
      · exact .inl (max_eq_right (not_lt.1 h))
    · by_cases h : i2 < k
      · exact .inr (.inr (h0 _ (.inr (.inr (.inl ⟨min_eq_left h.le, h⟩)))))
      · exact .inr (.inl (min_eq_right (not_lt.1 h)))
    · rcases SideA.vals_cover left v hl with e | ⟨e, hle⟩ | ⟨ho, h1, h2⟩ | ⟨ℓ, s, hs, ht⟩
      · exact .inl e
      · rcases hle.lt_or_eq with h | h
        · exact .inr (.inr (h0 _ (.inr (.inl ⟨e, h⟩))))
        · exact .inl (e.trans h.symm)
      · exact .inr (.inr (h0 _ (.inr (.inr (.inr (.inl ⟨ho, h1, h2⟩))))))
      · exact .inr (.inr ⟨ℓ + 1, s, List.mem_append_left _ hs, ht⟩)
    · rcases SideB.vals_cover right v hr with ⟨e, hle⟩ | e | ⟨ho, h1, h2⟩ | ⟨ℓ, s, hs, ht⟩
      · rcases hle.lt_or_eq with h | h
        · exact .inr (.inr (h0 _ (.inr (.inr (.inl ⟨e, h⟩)))))
        · exact .inr (.inl (e.trans h))
      · exact .inr (.inl e)
      · exact .inr (.inr (h0 _ (.inr (.inr (.inr (.inr ⟨ho, h1, h2⟩))))))
      · exact .inr (.inr ⟨ℓ + 1, s, List.mem_append_right _ hs, ht⟩)
/-- The side of `κ0(x_a)`: an index of a computed pair is `lo`, or `hi` with `lo ≤ hi`, or an index of
the overlap above `lo`, or an index of `loc` of a subrun. -/
theorem SideA.vals_cover : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi), ∀ v ∈ s.vals,
      v.1 = lo ∨ (v.1 = hi ∧ lo ≤ hi) ∨ (s.Ov ∧ lo < v.1 ∧ v.1 ≤ i) ∨
        ∃ ℓ, ∃ x ∈ s.subs ℓ, v.1 ∈ x.2.2.loc
  | _, _, _, _, _, _, _, .overlap .., v, hv => by
    obtain ⟨μ, h1, h2, rfl⟩ := hv
    rcases h1.lt_or_eq with h | h
    · exact .inr (.inr (.inl ⟨trivial, h, h2⟩))
    · exact .inl h.symm
  | _, _, _, _, _, _, _, .child _ _ r, v, hv => by
    rcases Run.vals_cover r v hv with e | e | h
    · exact .inl e
    · exact .inr (.inl ⟨e, r.bounds.1⟩)
    · exact .inr (.inr (.inr h))
  | _, _, _, _, _, _, _, .empty _, _, hv => absurd hv (Set.notMem_empty _)
/-- The side of `κ0(x_b)`: an index of a computed pair is `lo` with `lo ≤ hi`, or `hi`, or an index of
the overlap below `hi`, or an index of `loc` of a subrun. -/
theorem SideB.vals_cover : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi), ∀ v ∈ s.vals,
      (v.1 = lo ∧ lo ≤ hi) ∨ v.1 = hi ∨ (s.Ov ∧ i ≤ v.1 ∧ v.1 < hi) ∨
        ∃ ℓ, ∃ x ∈ s.subs ℓ, v.1 ∈ x.2.2.loc
  | _, _, _, _, _, _, _, .overlap .., v, hv => by
    obtain ⟨μ, h1, h2, rfl⟩ := hv
    rcases h2.lt_or_eq with h | h
    · exact .inr (.inr (.inl ⟨trivial, h1, h⟩))
    · exact .inr (.inl h)
  | _, _, _, _, _, _, _, .child _ _ r, v, hv => by
    rcases Run.vals_cover r v hv with e | e | h
    · exact .inl ⟨e, r.bounds.1⟩
    · exact .inr (.inl e)
    · exact .inr (.inr (.inr h))
  | _, _, _, _, _, _, _, .empty _, _, hv => absurd hv (Set.notMem_empty _)
end

section Graft

variable (f : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ},
  Run hR hC hg Γ L j k → Run hR hC hg Γ L j k)

theorem SideA.ov_graft {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ : ℕ) : (s.graft f ℓ).Ov = s.Ov := by
  cases s <;> rfl

theorem SideB.ov_graft {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ : ℕ) : (s.graft f ℓ).Ov = s.Ov := by
  cases s <;> rfl

theorem Run.loc_graft {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ} (r : Run hR hC hg Γ L j k)
    (ℓ : ℕ) : (r.graft f (ℓ + 1)).loc = r.loc := by
  cases r with
  | leaf => rfl
  | node _ _ _ _ _ _ _ _ _ _ _ _ _ left right =>
    simp only [Run.graft, Run.loc, SideA.ov_graft, SideB.ov_graft]

/-- The annulus, the range and the computed indices of a subrun. -/
def Sub.lkey (s : Sub C hR hC hg) : (Σ Γ' : Finset (D × Bool), C.Live g Γ') × (ℕ × ℕ) × Set ℕ :=
  (s.1, s.2.1, s.2.2.loc)

mutual
/-- **A deeper graft keeps the computed indices of the subruns above it.** -/
theorem Run.lkey_subs_graft : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ ℓ' : ℕ), ℓ < ℓ' →
      ((r.graft f ℓ').subs ℓ).map Sub.lkey = (r.subs ℓ).map Sub.lkey
  | _, _, _, _, r, 0, ℓ' + 1, _ => by
    rw [Run.subs_zero, Run.subs_zero]
    simp only [List.map_cons, List.map_nil, Sub.lkey, Run.loc_graft]
  | _, _, _, _, .leaf .., _ + 1, _ + 1, _ => rfl
  | _, _, _, _, .node _ _ _ _ _ _ _ _ _ _ _ _ _ left right, ℓ + 1, ℓ' + 1, h => by
    simp only [Run.graft, Run.subs, List.map_append]
    rw [SideA.lkey_subs_graft left ℓ ℓ' (by omega), SideB.lkey_subs_graft right ℓ ℓ' (by omega)]
theorem SideA.lkey_subs_graft : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ ℓ' : ℕ), ℓ < ℓ' →
      ((s.graft f ℓ').subs ℓ).map Sub.lkey = (s.subs ℓ).map Sub.lkey
  | _, _, _, _, _, _, _, .overlap .., _, _, _ => rfl
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, ℓ', h => by
    simp only [SideA.graft, SideA.subs]
    exact Run.lkey_subs_graft r ℓ ℓ' h
  | _, _, _, _, _, _, _, .empty _, _, _, _ => rfl
theorem SideB.lkey_subs_graft : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ ℓ' : ℕ), ℓ < ℓ' →
      ((s.graft f ℓ').subs ℓ).map Sub.lkey = (s.subs ℓ).map Sub.lkey
  | _, _, _, _, _, _, _, .overlap .., _, _, _ => rfl
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, ℓ', h => by
    simp only [SideB.graft, SideB.subs]
    exact Run.lkey_subs_graft r ℓ ℓ' h
  | _, _, _, _, _, _, _, .empty _, _, _, _ => rfl
end

end Graft

end CutPath

end RotSystem

end SsspFlow
