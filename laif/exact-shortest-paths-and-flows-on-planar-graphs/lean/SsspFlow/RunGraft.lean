import SsspFlow.Annuli

/-!
# Grafting a run at a depth

A run can be changed at one depth: every subrun at depth `ℓ` is replaced by a run on the same annulus
and range. The annuli and incisions above depth `ℓ` stay, and those at depth `ℓ + m` are those of the
new subruns at depth `m`. This builds a run level by level, with the choices of each level made after
the levels above it are fixed.

* `CutPath.Run.subs`: the subruns at depth `ℓ`, with their annuli and ranges.
* `CutPath.Run.graft`: the run with every subrun at depth `ℓ` replaced by its image under `f`.
* `CutPath.Run.nodes_graft_le`, `CutPath.Run.steps_graft_le`: the annuli and incisions up to depth
  `ℓ` stay.
* `CutPath.Run.nodes_graft`, `CutPath.Run.subs_graft`, `CutPath.Run.mem_steps_graft`: below depth `ℓ`
  they are those of the new subruns.
* `CutPath.Run.key_subs_graft`: a deeper graft keeps the annuli, ranges and tops of the subruns.
* `CutPath.Run.mem_steps_graft_succ`: the incisions of the next depth are the digon corners of the
  darts of the steps at the tops of the new subruns.
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

variable (C hR hC hg) in
/-- A subrun with its annulus and range. -/
abbrev Sub : Type u :=
  Σ (A : Σ Γ' : Finset (D × Bool), C.Live g Γ') (jk : ℕ × ℕ), Run hR hC hg A.1 A.2 jk.1 jk.2

mutual
/-- The subruns of a run at depth `ℓ`. -/
def Run.subs : {Γ : Finset (D × Bool)} → {L : C.Live g Γ} → {j k : ℕ} →
    Run hR hC hg Γ L j k → ℕ → List (Sub C hR hC hg)
  | Γ, L, j, k, r@(.leaf ..), 0 => [⟨⟨Γ, L⟩, (j, k), r⟩]
  | _, _, _, _, .leaf .., _ + 1 => []
  | Γ, L, j, k, r@(.node ..), 0 => [⟨⟨Γ, L⟩, (j, k), r⟩]
  | _, _, _, _, .node _ _ _ _ _ _ _ _ _ _ _ _ _ left right, ℓ + 1 => left.subs ℓ ++ right.subs ℓ
/-- The subruns below a side, at depth `ℓ` below it. -/
def SideA.subs : {Γ : Finset (D × Bool)} → {L : C.Live g Γ} → {p : List (D × Bool)} → {i : ℕ} →
    {S : L.Step} → {lo hi : ℕ} → SideA hR hC hg Γ L p i S lo hi → ℕ → List (Sub C hR hC hg)
  | _, _, _, _, _, _, _, .overlap .., _ => []
  | _, _, _, _, _, _, _, .child _ _ r, ℓ => r.subs ℓ
  | _, _, _, _, _, _, _, .empty _, _ => []
/-- The subruns below a side, at depth `ℓ` below it. -/
def SideB.subs : {Γ : Finset (D × Bool)} → {L : C.Live g Γ} → {p : List (D × Bool)} → {i : ℕ} →
    {S : L.Step} → {lo hi : ℕ} → SideB hR hC hg Γ L p i S lo hi → ℕ → List (Sub C hR hC hg)
  | _, _, _, _, _, _, _, .overlap .., _ => []
  | _, _, _, _, _, _, _, .child _ _ r, ℓ => r.subs ℓ
  | _, _, _, _, _, _, _, .empty _, _ => []
end

variable (f : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ},
  Run hR hC hg Γ L j k → Run hR hC hg Γ L j k)

mutual
/-- The run with every subrun at depth `ℓ` replaced by its image under `f`. -/
def Run.graft : {Γ : Finset (D × Bool)} → {L : C.Live g Γ} → {j k : ℕ} →
    Run hR hC hg Γ L j k → ℕ → Run hR hC hg Γ L j k
  | _, _, _, _, r@(.leaf ..), 0 => f r
  | _, _, _, _, .leaf h1 h2 h3 h4 h5 h6, _ + 1 => .leaf h1 h2 h3 h4 h5 h6
  | _, _, _, _, r@(.node ..), 0 => f r
  | _, _, _, _, .node hjk hxa hya hxb hyb p hp i1 i2 h1 h2 S sub left right, ℓ + 1 =>
    .node hjk hxa hya hxb hyb p hp i1 i2 h1 h2 S sub (SideA.graft left ℓ) (SideB.graft right ℓ)
/-- The side with every subrun at depth `ℓ` below it replaced by its image under `f`. -/
def SideA.graft : {Γ : Finset (D × Bool)} → {L : C.Live g Γ} → {p : List (D × Bool)} → {i : ℕ} →
    {S : L.Step} → {lo hi : ℕ} → SideA hR hC hg Γ L p i S lo hi → ℕ → SideA hR hC hg Γ L p i S lo hi
  | _, _, _, _, _, _, _, .overlap c hc P₁ P₂ hs h1 h2, _ => .overlap c hc P₁ P₂ hs h1 h2
  | _, _, _, _, _, _, _, .child noA hdeg r, ℓ => .child noA hdeg (Run.graft r ℓ)
  | _, _, _, _, _, _, _, .empty h, _ => .empty h
/-- The side with every subrun at depth `ℓ` below it replaced by its image under `f`. -/
def SideB.graft : {Γ : Finset (D × Bool)} → {L : C.Live g Γ} → {p : List (D × Bool)} → {i : ℕ} →
    {S : L.Step} → {lo hi : ℕ} → SideB hR hC hg Γ L p i S lo hi → ℕ → SideB hR hC hg Γ L p i S lo hi
  | _, _, _, _, _, _, _, .overlap c hc P₁ P₂ hs h1 h2, _ => .overlap c hc P₁ P₂ hs h1 h2
  | _, _, _, _, _, _, _, .child noB hdeg r, ℓ => .child noB hdeg (Run.graft r ℓ)
  | _, _, _, _, _, _, _, .empty h, _ => .empty h
end


section Lemmas

variable {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}

theorem Run.nodes_zero (r : Run hR hC hg Γ L j k) : r.nodes 0 = [⟨Γ, L⟩] := by cases r <;> rfl

theorem Run.steps_zero (r : Run hR hC hg Γ L j k) : r.steps 0 = ∅ := by cases r <;> rfl

theorem Run.subs_zero (r : Run hR hC hg Γ L j k) : r.subs 0 = [⟨⟨Γ, L⟩, (j, k), r⟩] := by cases r <;> rfl

theorem Run.graft_zero (r : Run hR hC hg Γ L j k) : r.graft f 0 = f r := by cases r <;> rfl

end Lemmas

mutual
/-- The annuli up to depth `ℓ` stay. -/
theorem Run.nodes_graft_le : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ m : ℕ), m ≤ ℓ → (r.graft f ℓ).nodes m = r.nodes m
  | _, _, _, _, r, 0, m, h => by
    obtain rfl : m = 0 := by omega
    rw [Run.graft_zero, Run.nodes_zero, Run.nodes_zero]
  | _, _, _, _, .leaf .., _ + 1, _, _ => rfl
  | _, _, _, _, .node .., _ + 1, 0, _ => rfl
  | _, _, _, _, .node _ _ _ _ _ _ _ _ _ _ _ _ _ left right, ℓ + 1, m + 1, h => by
    simp only [Run.graft, Run.nodes]
    rw [SideA.nodes_graft_le left ℓ m (by omega), SideB.nodes_graft_le right ℓ m (by omega)]
theorem SideA.nodes_graft_le : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ m : ℕ), m ≤ ℓ →
      (s.graft f ℓ).nodes m = s.nodes m
  | _, _, _, _, _, _, _, .overlap .., _, _, _ => rfl
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, m, h => by
    simp only [SideA.graft, SideA.nodes]
    exact Run.nodes_graft_le r ℓ m h
  | _, _, _, _, _, _, _, .empty _, _, _, _ => rfl
theorem SideB.nodes_graft_le : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ m : ℕ), m ≤ ℓ →
      (s.graft f ℓ).nodes m = s.nodes m
  | _, _, _, _, _, _, _, .overlap .., _, _, _ => rfl
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, m, h => by
    simp only [SideB.graft, SideB.nodes]
    exact Run.nodes_graft_le r ℓ m h
  | _, _, _, _, _, _, _, .empty _, _, _, _ => rfl
end

mutual
/-- The incisions up to depth `ℓ` stay. -/
theorem Run.steps_graft_le : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ m : ℕ), m ≤ ℓ → (r.graft f ℓ).steps m = r.steps m
  | _, _, _, _, r, 0, m, h => by
    obtain rfl : m = 0 := by omega
    rw [Run.graft_zero, Run.steps_zero, Run.steps_zero]
  | _, _, _, _, .leaf .., _ + 1, _, _ => rfl
  | _, _, _, _, .node .., _ + 1, 0, _ => rfl
  | _, _, _, _, .node _ _ _ _ _ _ _ _ _ _ _ _ _ left right, ℓ + 1, m + 1, h => by
    simp only [Run.graft, Run.steps]
    rw [SideA.steps_graft_le left ℓ m (by omega), SideB.steps_graft_le right ℓ m (by omega)]
theorem SideA.steps_graft_le : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ m : ℕ), m ≤ ℓ →
      (s.graft f ℓ).steps m = s.steps m
  | _, _, _, _, _, _, _, .overlap .., _, _, _ => rfl
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, m, h => by
    simp only [SideA.graft, SideA.steps]
    exact Run.steps_graft_le r ℓ m h
  | _, _, _, _, _, _, _, .empty _, _, _, _ => rfl
theorem SideB.steps_graft_le : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ m : ℕ), m ≤ ℓ →
      (s.graft f ℓ).steps m = s.steps m
  | _, _, _, _, _, _, _, .overlap .., _, _, _ => rfl
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, m, h => by
    simp only [SideB.graft, SideB.steps]
    exact Run.steps_graft_le r ℓ m h
  | _, _, _, _, _, _, _, .empty _, _, _, _ => rfl
end

mutual
/-- **The annuli below the graft** at depth `ℓ + m` are those of the new subruns at depth `m`. -/
theorem Run.nodes_graft : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ m : ℕ),
      (r.graft f ℓ).nodes (ℓ + m) = (r.subs ℓ).flatMap fun s => (f s.2.2).nodes m
  | _, _, _, _, r, 0, m => by
    rw [Run.graft_zero, Run.subs_zero, Nat.zero_add]
    simp
  | _, _, _, _, .leaf .., ℓ + 1, m => by
    rw [show ℓ + 1 + m = ℓ + m + 1 by omega]
    rfl
  | _, _, _, _, .node _ _ _ _ _ _ _ _ _ _ _ _ _ left right, ℓ + 1, m => by
    rw [show ℓ + 1 + m = ℓ + m + 1 by omega]
    simp only [Run.graft, Run.nodes, Run.subs, List.flatMap_append]
    rw [SideA.nodes_graft left ℓ m, SideB.nodes_graft right ℓ m]
theorem SideA.nodes_graft : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ m : ℕ),
      (s.graft f ℓ).nodes (ℓ + m) = (s.subs ℓ).flatMap fun s => (f s.2.2).nodes m
  | _, _, _, _, _, _, _, .overlap .., _, _ => rfl
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, m => by
    simp only [SideA.graft, SideA.nodes, SideA.subs]
    exact Run.nodes_graft r ℓ m
  | _, _, _, _, _, _, _, .empty _, _, _ => rfl
theorem SideB.nodes_graft : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ m : ℕ),
      (s.graft f ℓ).nodes (ℓ + m) = (s.subs ℓ).flatMap fun s => (f s.2.2).nodes m
  | _, _, _, _, _, _, _, .overlap .., _, _ => rfl
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, m => by
    simp only [SideB.graft, SideB.nodes, SideB.subs]
    exact Run.nodes_graft r ℓ m
  | _, _, _, _, _, _, _, .empty _, _, _ => rfl
end

mutual
/-- **The subruns below the graft** at depth `ℓ + m` are those of the new subruns at depth `m`. -/
theorem Run.subs_graft : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ m : ℕ),
      (r.graft f ℓ).subs (ℓ + m) = (r.subs ℓ).flatMap fun s => (f s.2.2).subs m
  | _, _, _, _, r, 0, m => by
    rw [Run.graft_zero, Run.subs_zero, Nat.zero_add]
    simp
  | _, _, _, _, .leaf .., ℓ + 1, m => by
    rw [show ℓ + 1 + m = ℓ + m + 1 by omega]
    rfl
  | _, _, _, _, .node _ _ _ _ _ _ _ _ _ _ _ _ _ left right, ℓ + 1, m => by
    rw [show ℓ + 1 + m = ℓ + m + 1 by omega]
    simp only [Run.graft, Run.subs, List.flatMap_append]
    rw [SideA.subs_graft left ℓ m, SideB.subs_graft right ℓ m]
theorem SideA.subs_graft : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ m : ℕ),
      (s.graft f ℓ).subs (ℓ + m) = (s.subs ℓ).flatMap fun s => (f s.2.2).subs m
  | _, _, _, _, _, _, _, .overlap .., _, _ => rfl
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, m => by
    simp only [SideA.graft, SideA.subs]
    exact Run.subs_graft r ℓ m
  | _, _, _, _, _, _, _, .empty _, _, _ => rfl
theorem SideB.subs_graft : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ m : ℕ),
      (s.graft f ℓ).subs (ℓ + m) = (s.subs ℓ).flatMap fun s => (f s.2.2).subs m
  | _, _, _, _, _, _, _, .overlap .., _, _ => rfl
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, m => by
    simp only [SideB.graft, SideB.subs]
    exact Run.subs_graft r ℓ m
  | _, _, _, _, _, _, _, .empty _, _, _ => rfl
end

mutual
/-- **The incisions below the graft**: up to depth `ℓ + m` they are those up to depth `ℓ` and those
of the new subruns up to depth `m`. -/
theorem Run.mem_steps_graft : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ m : ℕ) (x : D × Bool),
      x ∈ (r.graft f ℓ).steps (ℓ + m) ↔ x ∈ r.steps ℓ ∨ ∃ s ∈ r.subs ℓ, x ∈ (f s.2.2).steps m
  | _, _, _, _, r, 0, m, x => by
    rw [Run.graft_zero, Run.subs_zero, Run.steps_zero, Nat.zero_add]
    simp
  | _, _, _, _, .leaf .., ℓ + 1, m, x => by
    simp [Run.graft, Run.steps, Run.subs]
  | _, _, _, _, .node _ _ _ _ _ _ _ _ _ _ _ _ _ left right, ℓ + 1, m, x => by
    rw [show ℓ + 1 + m = ℓ + m + 1 by omega]
    simp only [Run.graft, Run.steps, Run.subs, Finset.mem_union, List.mem_append]
    rw [SideA.mem_steps_graft left ℓ m x, SideB.mem_steps_graft right ℓ m x]
    constructor
    · rintro ((h | h | ⟨s, hs, h⟩) | h | ⟨s, hs, h⟩)
      · exact .inl (.inl (.inl h))
      · exact .inl (.inl (.inr h))
      · exact .inr ⟨s, .inl hs, h⟩
      · exact .inl (.inr h)
      · exact .inr ⟨s, .inr hs, h⟩
    · rintro (((h | h) | h) | ⟨s, hs | hs, h⟩)
      · exact .inl (.inl h)
      · exact .inl (.inr (.inl h))
      · exact .inr (.inl h)
      · exact .inl (.inr (.inr ⟨s, hs, h⟩))
      · exact .inr (.inr ⟨s, hs, h⟩)
theorem SideA.mem_steps_graft : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ m : ℕ) (x : D × Bool),
      x ∈ (s.graft f ℓ).steps (ℓ + m) ↔ x ∈ s.steps ℓ ∨ ∃ s' ∈ s.subs ℓ, x ∈ (f s'.2.2).steps m
  | _, _, _, _, _, _, _, .overlap .., _, _, _ => by simp [SideA.graft, SideA.steps, SideA.subs]
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, m, x => by
    simp only [SideA.graft, SideA.steps, SideA.subs]
    exact Run.mem_steps_graft r ℓ m x
  | _, _, _, _, _, _, _, .empty _, _, _, _ => by simp [SideA.graft, SideA.steps, SideA.subs]
theorem SideB.mem_steps_graft : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ m : ℕ) (x : D × Bool),
      x ∈ (s.graft f ℓ).steps (ℓ + m) ↔ x ∈ s.steps ℓ ∨ ∃ s' ∈ s.subs ℓ, x ∈ (f s'.2.2).steps m
  | _, _, _, _, _, _, _, .overlap .., _, _, _ => by simp [SideB.graft, SideB.steps, SideB.subs]
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, m, x => by
    simp only [SideB.graft, SideB.steps, SideB.subs]
    exact Run.mem_steps_graft r ℓ m x
  | _, _, _, _, _, _, _, .empty _, _, _, _ => by simp [SideB.graft, SideB.steps, SideB.subs]
end

mutual
/-- The annuli of a run at a depth are those of its subruns there. -/
theorem Run.nodes_eq_subs : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ : ℕ), r.nodes ℓ = (r.subs ℓ).map Sigma.fst
  | _, _, _, _, .leaf .., 0 => rfl
  | _, _, _, _, .leaf .., _ + 1 => rfl
  | _, _, _, _, .node .., 0 => rfl
  | _, _, _, _, .node _ _ _ _ _ _ _ _ _ _ _ _ _ left right, ℓ + 1 => by
    simp only [Run.nodes, Run.subs, List.map_append]
    rw [SideA.nodes_eq_subs left ℓ, SideB.nodes_eq_subs right ℓ]
theorem SideA.nodes_eq_subs : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ : ℕ),
      s.nodes ℓ = (s.subs ℓ).map Sigma.fst
  | _, _, _, _, _, _, _, .overlap .., _ => rfl
  | _, _, _, _, _, _, _, .child _ _ r, ℓ => Run.nodes_eq_subs r ℓ
  | _, _, _, _, _, _, _, .empty _, _ => rfl
theorem SideB.nodes_eq_subs : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ : ℕ),
      s.nodes ℓ = (s.subs ℓ).map Sigma.fst
  | _, _, _, _, _, _, _, .overlap .., _ => rfl
  | _, _, _, _, _, _, _, .child _ _ r, ℓ => Run.nodes_eq_subs r ℓ
  | _, _, _, _, _, _, _, .empty _, _ => rfl
end


/-- The walk and the darts of the step of the root of a run, `none` at a leaf. -/
def Run.top {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ} :
    Run hR hC hg Γ L j k → Option (List (D × Bool) × List (D × Bool))
  | .leaf .. => none
  | .node _ _ _ _ _ p _ _ _ _ _ S _ _ _ => some (p, (List.range S.n).map S.q)

/-- The annulus, the range and the top of a subrun. -/
def Sub.key (s : Sub C hR hC hg) :
    (Σ Γ' : Finset (D × Bool), C.Live g Γ') × (ℕ × ℕ) × Option (List (D × Bool) × List (D × Bool)) :=
  (s.1, s.2.1, s.2.2.top)

theorem Run.top_graft {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ} (r : Run hR hC hg Γ L j k)
    (ℓ : ℕ) : (r.graft f (ℓ + 1)).top = r.top := by
  cases r <;> rfl

mutual
/-- **A deeper graft keeps the subruns above it**, up to their annuli, ranges and tops. -/
theorem Run.key_subs_graft : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ ℓ' : ℕ), ℓ < ℓ' →
      ((r.graft f ℓ').subs ℓ).map Sub.key = (r.subs ℓ).map Sub.key
  | _, _, _, _, r, 0, ℓ' + 1, _ => by
    rw [Run.subs_zero, Run.subs_zero]
    simp only [List.map_cons, List.map_nil, Sub.key, Run.top_graft]
  | _, _, _, _, .leaf .., _ + 1, _ + 1, _ => rfl
  | _, _, _, _, .node _ _ _ _ _ _ _ _ _ _ _ _ _ left right, ℓ + 1, ℓ' + 1, h => by
    simp only [Run.graft, Run.subs, List.map_append]
    rw [SideA.key_subs_graft left ℓ ℓ' (by omega), SideB.key_subs_graft right ℓ ℓ' (by omega)]
theorem SideA.key_subs_graft : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ ℓ' : ℕ), ℓ < ℓ' →
      ((s.graft f ℓ').subs ℓ).map Sub.key = (s.subs ℓ).map Sub.key
  | _, _, _, _, _, _, _, .overlap .., _, _, _ => rfl
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, ℓ', h => by
    simp only [SideA.graft, SideA.subs]
    exact Run.key_subs_graft r ℓ ℓ' h
  | _, _, _, _, _, _, _, .empty _, _, _, _ => rfl
theorem SideB.key_subs_graft : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ ℓ' : ℕ), ℓ < ℓ' →
      ((s.graft f ℓ').subs ℓ).map Sub.key = (s.subs ℓ).map Sub.key
  | _, _, _, _, _, _, _, .overlap .., _, _, _ => rfl
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, ℓ', h => by
    simp only [SideB.graft, SideB.subs]
    exact Run.key_subs_graft r ℓ ℓ' h
  | _, _, _, _, _, _, _, .empty _, _, _, _ => rfl
end

/-- The subruns at the depth of the graft are the images of the old ones. -/
theorem Run.subs_graft_self {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ : ℕ) :
    (r.graft f ℓ).subs ℓ = (r.subs ℓ).map fun s => ⟨s.1, s.2.1, f s.2.2⟩ := by
  have h := r.subs_graft f ℓ 0
  rw [Nat.add_zero] at h
  rw [h, List.flatMap_eq_foldl]
  clear h
  generalize r.subs ℓ = l
  suffices ∀ acc, List.foldl (fun acc s => acc ++ (f s.2.2).subs 0) acc l =
      acc ++ l.map fun s => ⟨s.1, s.2.1, f s.2.2⟩ by simpa using this []
  induction l with
  | nil => simp
  | cons s l ih =>
    intro acc
    rw [List.foldl_cons, ih, Run.subs_zero]
    simp


theorem SideA.steps_zero {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) : s.steps 0 = ∅ := by
  cases s with
  | overlap => rfl
  | child _ _ r => exact r.steps_zero
  | empty => rfl

theorem SideB.steps_zero {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) : s.steps 0 = ∅ := by
  cases s with
  | overlap => rfl
  | child _ _ r => exact r.steps_zero
  | empty => rfl

/-- The incisions of the root of a run are the digon corners of the darts of its step. -/
theorem Run.mem_steps_one {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (x : D × Bool) :
    x ∈ r.steps 1 ↔ ∃ q sd, r.top = some (q, sd) ∧ ∃ z ∈ sd, x = (z.1, false) ∨ x = (R.rev z.1, false) := by
  cases r with
  | leaf => simp [Run.steps, Run.top]
  | node _ _ _ _ _ p _ _ _ _ _ S _ left right =>
    simp only [Run.steps, Run.top, SideA.steps_zero, SideB.steps_zero, Finset.union_empty,
      Option.some.injEq, Prod.mk.injEq, S.mem_corners]
    constructor
    · rintro ⟨j', hj', e⟩
      exact ⟨_, _, ⟨rfl, rfl⟩, S.q j', List.mem_map.2 ⟨j', List.mem_range.2 hj', rfl⟩, e⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, z, hz, e⟩
      obtain ⟨j', hj', rfl⟩ := List.mem_map.1 hz
      exact ⟨j', List.mem_range.1 hj', e⟩

/-- **The incisions of the next depth** after a graft at depth `ℓ`: those up to depth `ℓ` and the
digon corners of the darts of the steps at the tops of the new subruns at depth `ℓ`. -/
theorem Run.mem_steps_graft_succ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ : ℕ) (x : D × Bool) :
    x ∈ (r.graft f ℓ).steps (ℓ + 1) ↔ x ∈ r.steps ℓ ∨ ∃ s ∈ (r.graft f ℓ).subs ℓ, ∃ q sd,
      s.2.2.top = some (q, sd) ∧ ∃ z ∈ sd, x = (z.1, false) ∨ x = (R.rev z.1, false) := by
  rw [Run.mem_steps_graft, Run.subs_graft_self]
  simp only [List.mem_map, Run.mem_steps_one]
  constructor
  · rintro (h | ⟨s, hs, h⟩)
    · exact .inl h
    · exact .inr ⟨_, ⟨s, hs, rfl⟩, h⟩
  · rintro (h | ⟨_, ⟨s, hs, rfl⟩, h⟩)
    · exact .inl h
    · exact .inr ⟨s, hs, h⟩

end CutPath

end RotSystem

end SsspFlow
