import SsspFlow.RunGraft

/-!
# A node with given data, and the runs of the levels

For an annulus that is not a leaf, any shortest walk at the middle index, its least and greatest
index of the cut path, and a step that is a segment of the walk give a node of a run. Each side is
an overlap when the walk visits one of its corners, otherwise a call on the side of the cut along the
step when its range is not empty, with any run there, and otherwise empty.

Grafting such nodes at depth `ℓ`, with data chosen by a rule that may depend on the run so far, gives
the run of the next level. The choices made at a level stay in all later levels.

* `CutPath.Live.pickNode`: the node with the given walk, indices and step.
* `CutPath.pickF`, `CutPath.Run.picked`: the graft of nodes with data that satisfy a rule.
* `CutPath.Run.seq`: the runs of the levels.
* `CutPath.Run.seq_steps`, `CutPath.Run.seq_nodes`, `CutPath.Run.seq_keys`: the incisions, annuli and
  subruns up to a depth are fixed from that level on.
* `CutPath.Run.seq_picked`: in the run of level `N`, every node at depth `ℓ < N` has data that satisfy
  the rule of level `ℓ`.
-/

set_option autoImplicit false

universe u

namespace SsspFlow

open FourColor
open scoped ENNReal

namespace RotSystem

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace CutPath

variable {C : R.CutPath} {g₀ : D → ℕ} (hR : R.Planar) (hC : R.Connected)
  (hgc : ∀ x, (Nat.cast ∘ g₀ : D → ℝ≥0∞) (R.rev x) = (Nat.cast ∘ g₀ : D → ℝ≥0∞) x)

/-- The side of `κ0(x_a)` is an overlap. -/
def SideA.IsOverlap {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} : SideA hR hC hgc Γ L p i S lo hi → Prop
  | .overlap .. => True
  | .child .. => False
  | .empty .. => False

/-- The side of `κ0(x_b)` is an overlap. -/
def SideB.IsOverlap {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ} {p : List (D × Bool)} {i : ℕ}
    {S : L.Step} {lo hi : ℕ} : SideB hR hC hgc Γ L p i S lo hi → Prop
  | .overlap .. => True
  | .child .. => False
  | .empty .. => False

theorem SideA.subs_of_isOverlap {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ}
    {p : List (D × Bool)} {i : ℕ} {S : L.Step} {lo hi : ℕ} {s : SideA hR hC hgc Γ L p i S lo hi}
    (h : s.IsOverlap hR hC hgc) (ℓ : ℕ) : s.subs ℓ = [] := by
  cases s with
  | overlap => rfl
  | child => exact h.elim
  | empty => exact h.elim

theorem SideB.subs_of_isOverlap {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ}
    {p : List (D × Bool)} {i : ℕ} {S : L.Step} {lo hi : ℕ} {s : SideB hR hC hgc Γ L p i S lo hi}
    (h : s.IsOverlap hR hC hgc) (ℓ : ℕ) : s.subs ℓ = [] := by
  cases s with
  | overlap => rfl
  | child => exact h.elim
  | empty => exact h.elim

namespace Live

variable {Γ : Finset (D × Bool)} (L : C.Live (Nat.cast ∘ g₀) Γ) {j k : ℕ} (hjk : j + 2 ≤ k)
  (hxa : L.xa ≤ j) (hya : L.ya ≤ j) (hxb : k ≤ L.xb) (hyb : k ≤ L.yb)
  {q : List (D × Bool)} (hq : L.Shortest ((j + k) / 2) q) {i1 i2 : ℕ}
  (hI1 : IsLeast (C.idx (L.κ0 ((j + k) / 2)) q) i1) (hI2 : IsGreatest (C.idx (L.κ0 ((j + k) / 2)) q) i2)
  (S : L.Step) (hsub : ∃ p₁ p₃, q = p₁ ++ (List.range S.n).map S.q ++ p₃)

include hjk hxa hxb hq hI1 hI2 hsub in
theorem pick_facts :
    (∀ j', j' < S.n → S.q j' ∈ q) ∧ L.Visits ((j + k) / 2) q (L.κ0 S.x) ∧
      i1 ≤ S.x ∧ i1 ≤ S.y ∧ S.x ≤ i2 ∧ S.y ≤ i2 := by
  have h1 : L.xa ≤ (j + k) / 2 := by omega
  have h2 : (j + k) / 2 ≤ L.xb := by omega
  obtain ⟨p₁, p₃, hsub⟩ := hsub
  have hmem : ∀ j', j' < S.n → S.q j' ∈ q := fun j' hj' => by
    rw [hsub]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨j', List.mem_range.2 hj', rfl⟩))
  have vx : L.Visits ((j + k) / 2) q (L.κ0 S.x) :=
    L.visits_of_mem hq.1 (hmem 0 S.pos) (((R.double.split Γ).tail_eq_iff _ _).2 S.start).symm
  have vy : L.Visits ((j + k) / 2) q (L.κ1 S.y) :=
    Or.inr ⟨S.q (S.n - 1), hmem _ (by have := S.pos; omega), ((R.double.split Γ).tail_eq_iff _ _).2 S.stop⟩
  have mx := L.mem_idx_of (S.hxb.trans L.xb_le) (L.piece0 S.x S.hxa S.hxb) vx
  have my := L.mem_idx_of (S.hyb.trans L.yb_le) (L.piece1 S.y S.hya S.hyb) vy
  exact ⟨hmem, vx, hI1.2 mx, hI1.2 my, hI2.2 mx, hI2.2 my⟩

open Classical in
/-- **The node with given data.** -/
noncomputable def pickNode : Run hR hC hgc Γ L j k :=
  have hf := L.pick_facts hjk hxa hxb hq hI1 hI2 S hsub
  .node hjk hxa hya hxb hyb q hq i1 i2 hI1 hI2 S hsub
    (if hA : ∃ c, (c = L.κ0 L.xa ∨ c ∈ L.La ∨ c = L.κ1 L.ya) ∧ L.Visits ((j + k) / 2) q c then
      (Classical.choice (by
        obtain ⟨c, hc, hv⟩ := hA
        obtain ⟨P₁, P₂, s, hs, e1, e2, rfl, -⟩ := hq.1.split_first
          (fun w => w = (R.double.split Γ).tail c) (hv.imp Eq.symm id)
        exact ⟨⟨.overlap c hc P₁ P₂ hs e1 e2, trivial⟩⟩ :
          Nonempty {s : SideA hR hC hgc Γ L q ((j + k) / 2) S j i1 // s.IsOverlap hR hC hgc})).1
    else if hj : j ≤ i1 then
      have noA : ∀ j', 0 < j' → j' < S.n → ∀ c ∈ L.La,
          ¬ fconnect (R.double.split Γ).rot (S.q j') c := fun j' _ hj' c hc hfc =>
        hA ⟨c, Or.inr (Or.inl hc), L.visits_of_mem hq.1 (hf.1 j' hj')
          (((R.double.split Γ).tail_eq_iff _ _).2 hfc).symm⟩
      have hdeg : L.hiB S.x S.y ≠ [] ∨ 1 < S.n ∨ ((S.rq 0).1, false) ∉ Γ := by
        have hx : S.x ≠ L.xa := fun e => hA ⟨L.κ0 L.xa, Or.inl rfl, e ▸ hf.2.1⟩
        exact Or.inl (List.ne_nil_of_mem (a := L.κ0 L.xa) (by
          simp only [Live.hiB, List.mem_append, List.mem_map, List.mem_range'_1]
          exact Or.inr ⟨L.xa, ⟨le_rfl, by have := S.hxa; omega⟩, rfl⟩))
      .child noA hdeg (Classical.choice (exists_run hR hC hgc (i1 - j + 1) (L.lo hR hC S noA hdeg hgc)
        (j := j) (k := i1) (by omega) hj hxa hya hf.2.2.1 hf.2.2.2.1))
    else .empty (by omega))
    (if hB : ∃ c, (c = L.κ0 L.xb ∨ c ∈ L.Lb ∨ c = L.κ1 L.yb) ∧ L.Visits ((j + k) / 2) q c then
      (Classical.choice (by
        obtain ⟨c, hc, hv⟩ := hB
        obtain ⟨P₁, P₂, s, hs, e1, e2, rfl, -⟩ := hq.1.split_first
          (fun w => w = (R.double.split Γ).tail c) (hv.imp Eq.symm id)
        exact ⟨⟨.overlap c hc P₁ P₂ hs e1 e2, trivial⟩⟩ :
          Nonempty {s : SideB hR hC hgc Γ L q ((j + k) / 2) S i2 k // s.IsOverlap hR hC hgc})).1
    else if hj : i2 ≤ k then
      have noB : ∀ j', 0 < j' → j' < S.n → ∀ c ∈ L.Lb,
          ¬ fconnect (R.double.split Γ).rot (S.q j') c := fun j' _ hj' c hc hfc =>
        hB ⟨c, Or.inr (Or.inl hc), L.visits_of_mem hq.1 (hf.1 j' hj')
          (((R.double.split Γ).tail_eq_iff _ _).2 hfc).symm⟩
      have hdeg : L.hiA S.x S.y ≠ [] ∨ 1 < S.n ∨ ((S.q 0).1, false) ∉ Γ := by
        have hx : S.x ≠ L.xb := fun e => hB ⟨L.κ0 L.xb, Or.inl rfl, e ▸ hf.2.1⟩
        exact Or.inl (List.ne_nil_of_mem (a := L.κ0 L.xb) (by
          simp only [Live.hiA, List.mem_append]
          exact Or.inl (Or.inl (mem_cornerSeg.2 ⟨L.xb, by have := S.hxb; omega, le_rfl, rfl⟩))))
      .child noB hdeg (Classical.choice (exists_run hR hC hgc (k - i2 + 1) (L.hi hR hC S noB hdeg hgc)
        (j := i2) (k := k) (by omega) hj hf.2.2.2.2.1 hf.2.2.2.2.2 hxb hyb))
    else .empty (by omega))

theorem top_pickNode :
    (L.pickNode hR hC hgc hjk hxa hya hxb hyb hq hI1 hI2 S hsub).top = some (q, (List.range S.n).map S.q) :=
  rfl

end Live


/-- The data of a node on an annulus with a range: a shortest walk at the middle index, its least and
greatest index of the cut path, and a step that is a segment of the walk. -/
structure NodeData {Γ : Finset (D × Bool)} (L : C.Live (Nat.cast ∘ g₀) Γ) (j k : ℕ) where
  hjk : j + 2 ≤ k
  q : List (D × Bool)
  hq : L.Shortest ((j + k) / 2) q
  i1 : ℕ
  i2 : ℕ
  hI1 : IsLeast (C.idx (L.κ0 ((j + k) / 2)) q) i1
  hI2 : IsGreatest (C.idx (L.κ0 ((j + k) / 2)) q) i2
  S : L.Step
  hsub : ∃ p₁ p₃, q = p₁ ++ (List.range S.n).map S.q ++ p₃

/-- The darts of a step. -/
def Live.Step.darts {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ} (S : L.Step) :
    List (D × Bool) :=
  (List.range S.n).map S.q

variable (P : (Σ Γ' : Finset (D × Bool), C.Live (Nat.cast ∘ g₀) Γ') → ℕ → List (D × Bool) →
  List (D × Bool) → Prop)

open Classical in
/-- **The picking graft.** A subrun on an annulus that is not a leaf becomes the node with data whose
walk and step darts satisfy `P`, if there are such data; otherwise it stays. -/
noncomputable def pickF {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ} {j k : ℕ}
    (r : Run hR hC hgc Γ L j k) : Run hR hC hgc Γ L j k :=
  if h : Nonempty {d : NodeData L j k // P ⟨Γ, L⟩ ((j + k) / 2) d.q d.S.darts} then
    L.pickNode hR hC hgc (Classical.choice h).1.hjk
      (by cases r <;> assumption) (by cases r <;> assumption) (by cases r <;> assumption)
      (by cases r <;> assumption) (Classical.choice h).1.hq (Classical.choice h).1.hI1
      (Classical.choice h).1.hI2 (Classical.choice h).1.S (Classical.choice h).1.hsub
  else r

/-- **The subruns at the depth of a picking graft.** If every subrun at depth `ℓ` on an annulus that
is not a leaf has data whose walk and step darts satisfy `P`, then after the picking graft at depth
`ℓ` every such subrun is a node whose walk and step darts satisfy `P`. -/
theorem Run.picked {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ} {j k : ℕ}
    (r : Run hR hC hgc Γ L j k) (ℓ : ℕ)
    (h : ∀ s ∈ r.subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
      Nonempty {d : NodeData s.1.2 s.2.1.1 s.2.1.2 //
        P s.1 ((s.2.1.1 + s.2.1.2) / 2) d.q d.S.darts}) :
    ∀ s ∈ (r.graft (fun r => pickF hR hC hgc P r) ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
      ∃ q sd, s.2.2.top = some (q, sd) ∧ P s.1 ((s.2.1.1 + s.2.1.2) / 2) q sd := by
  intro s' hs' hjk
  rw [Run.subs_graft_self] at hs'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs'
  have hn := h s hs hjk
  refine ⟨_, _, ?_, (Classical.choice hn).2⟩
  show (pickF hR hC hgc P s.2.2).top = _
  unfold pickF
  rw [dite_eq_left_of_eq_true (eq_true hn)]
  rfl


section Seq

variable {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ} {j k : ℕ}
  (Pof : ℕ → Run hR hC hgc Γ L j k → (Σ Γ' : Finset (D × Bool), C.Live (Nat.cast ∘ g₀) Γ') → ℕ →
    List (D × Bool) → List (D × Bool) → Prop)

/-- **The runs of the levels.** The run of level `ℓ + 1` is that of level `ℓ` after the picking graft
at depth `ℓ`, for the choice `Pof ℓ` made from the run of level `ℓ`. -/
noncomputable def Run.seq (r₀ : Run hR hC hgc Γ L j k) : ℕ → Run hR hC hgc Γ L j k
  | 0 => r₀
  | ℓ + 1 => (Run.seq r₀ ℓ).graft (fun r => pickF hR hC hgc (Pof ℓ (Run.seq r₀ ℓ)) r) ℓ

variable (r₀ : Run hR hC hgc Γ L j k)

/-- The incisions up to depth `ℓ` are fixed from level `ℓ` on. -/
theorem Run.seq_steps {ℓ m : ℕ} (h : ℓ ≤ m) : (r₀.seq hR hC hgc Pof m).steps ℓ = (r₀.seq hR hC hgc Pof ℓ).steps ℓ := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hm ih => rw [← ih]; exact Run.steps_graft_le _ _ m ℓ hm

/-- The annuli up to depth `ℓ` are fixed from level `ℓ` on. -/
theorem Run.seq_nodes {ℓ m : ℕ} (h : ℓ ≤ m) : (r₀.seq hR hC hgc Pof m).nodes ℓ = (r₀.seq hR hC hgc Pof ℓ).nodes ℓ := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hm ih => rw [← ih]; exact Run.nodes_graft_le _ _ m ℓ hm

/-- The subruns at depth `ℓ`, up to annuli, ranges and tops, are fixed from level `ℓ + 1` on. -/
theorem Run.seq_keys {ℓ m : ℕ} (h : ℓ < m) :
    ((r₀.seq hR hC hgc Pof m).subs ℓ).map Sub.key = ((r₀.seq hR hC hgc Pof (ℓ + 1)).subs ℓ).map Sub.key := by
  induction m, (show ℓ + 1 ≤ m from h) using Nat.le_induction with
  | base => rfl
  | succ m hm ih => rw [← ih (by omega)]; exact Run.key_subs_graft _ _ ℓ m (by omega)

/-- The subruns at depth `ℓ` of the run of level `ℓ + 1`, up to annuli and ranges, are those of the
run of level `ℓ`. -/
theorem Run.seq_subs_succ (ℓ : ℕ) :
    ((r₀.seq hR hC hgc Pof (ℓ + 1)).subs ℓ).map (fun s => (s.1, s.2.1)) =
      ((r₀.seq hR hC hgc Pof ℓ).subs ℓ).map (fun s => (s.1, s.2.1)) := by
  show (((r₀.seq hR hC hgc Pof ℓ).graft _ ℓ).subs ℓ).map _ = _
  rw [Run.subs_graft_self, List.map_map]
  rfl

/-- **The picked levels.** If at every level `ℓ < N` every subrun at depth `ℓ` on an annulus that is
not a leaf has data whose walk and step darts satisfy the choice of that level, then in the run of
level `N` every such subrun at depth `ℓ < N` is a node whose walk and step darts satisfy it. -/
theorem Run.seq_picked (N : ℕ)
    (h : ∀ ℓ < N, ∀ s ∈ (r₀.seq hR hC hgc Pof ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
      Nonempty {d : NodeData s.1.2 s.2.1.1 s.2.1.2 //
        Pof ℓ (r₀.seq hR hC hgc Pof ℓ) s.1 ((s.2.1.1 + s.2.1.2) / 2) d.q d.S.darts}) :
    ∀ ℓ < N, ∀ s ∈ (r₀.seq hR hC hgc Pof N).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
      ∃ q sd, s.2.2.top = some (q, sd) ∧
        Pof ℓ (r₀.seq hR hC hgc Pof ℓ) s.1 ((s.2.1.1 + s.2.1.2) / 2) q sd := by
  intro ℓ hℓ s hs hjk
  have hk : Sub.key s ∈ ((r₀.seq hR hC hgc Pof (ℓ + 1)).subs ℓ).map Sub.key := by
    rw [← r₀.seq_keys hR hC hgc Pof hℓ]
    exact List.mem_map_of_mem hs
  obtain ⟨s₁, hs₁, he⟩ := List.mem_map.1 hk
  simp only [Sub.key, Prod.mk.injEq] at he
  obtain ⟨e1, e2, e3⟩ := he
  have hp := Run.picked hR hC hgc (Pof ℓ (r₀.seq hR hC hgc Pof ℓ)) (r₀.seq hR hC hgc Pof ℓ) ℓ
    (fun s' hs' hjk' => h ℓ hℓ s' hs' hjk') s₁ hs₁ (by rw [e2]; exact hjk)
  rw [e3, e2, e1] at hp
  exact hp

end Seq

end CutPath

end RotSystem

end SsspFlow
