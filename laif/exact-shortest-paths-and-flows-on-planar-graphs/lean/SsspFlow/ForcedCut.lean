import SsspFlow.Select

/-!
# A prescribed first cut

The first cut of a decomposition may be any set of at most two corners with flag `true`, for example the
two corners of one face at the ends of an edge. Later levels follow the rule of `sel`. The prescribed cut
is a cut in the sense of `IsCutW` (`isCutW_of_true`), the levels form a decomposition (`forcedSeq_decomp`),
and the cuts are balanced from the first level on (`forcedSeq_bal`), so the height grows by one level
(`forcedSeq_final`). Every ancestor of a vertex of the prescribed cut has a corner from the first level on
(`not_np_forcedSeq`), so it is a hub of the root bag of the hierarchy (`forced_hub_root`). Values between the hubs of the
root bag are within their factors of the distances in the whole graph (`RHierarchy.root_hub_bounds`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SsspFlow

open FourColor

open scoped ENNReal

namespace RHierarchy

variable {V : Type*} {ι : Type*} {adj : V → V → Prop} (H : RHierarchy V ι adj)

/-- The region of the root bag holds every walk. -/
theorem distR_root_le (w : V → V → ℝ≥0∞) (a b : V) :
    distR adj w (H.arc H.root) a b ≤ dist adj w Set.univ a b :=
  le_iInf fun p => le_iInf fun _ => iInf₂_le p (Walk.arcsIn_of_adj H.root_arc p)

/-- **Values at the root.** Values between hubs that lie within a factor `κ` below the distance and a
factor `lam` above the distance in the region of their bag lie, at the root bag, within these factors
of the distance in the whole graph. -/
theorem root_hub_bounds (w : V → V → ℝ≥0∞) (κ lam : ℝ≥0∞) (dV : ι → V → V → ℝ≥0∞)
    (hlo : ∀ x, ∀ a ∈ H.hub x, ∀ b ∈ H.hub x, κ * dist adj w Set.univ a b ≤ dV x a b)
    (hhi : ∀ x, ∀ a ∈ H.hub x, ∀ b ∈ H.hub x, dV x a b ≤ lam * distR adj w (H.arc x) a b)
    {a b : V} (ha : a ∈ H.hub H.root) (hb : b ∈ H.hub H.root) :
    κ * dist adj w Set.univ a b ≤ dV H.root a b ∧ dV H.root a b ≤ lam * dist adj w Set.univ a b :=
  ⟨hlo _ a ha b hb, (hhi _ a ha b hb).trans (by gcongr; exact H.distR_root_le w a b)⟩

end RHierarchy

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace RootedTree

variable {V : Type*} [Fintype V] [DecidableEq V] {t : R.RootedTree V}

open Classical in
/-- At most two corners with flag `true` cut every level. -/
theorem isCutW_of_true {Γ C : Finset (D × Bool)} (hC : ∀ c ∈ C, c.2 = true) (hcard : C.card ≤ 2) :
    t.IsCutW Γ C where
  pair := fun d hd => by simpa using hC _ hd
  two := fun _ => (Finset.card_filter_le _ _).trans hcard

/-- **Rails.** After a cut, every ancestor of the vertex of a cut corner has a corner. -/
theorem not_np_next_of_anc {Γ C : Finset (D × Bool)} (hroot : ∃ z ∈ Γ, t.vertM z = t.root)
    {c : D × Bool} (hc : c ∈ C) {w : V} (hw : t.Anc w (t.vertM c)) : ¬ t.NP (t.next Γ C) w := by
  intro hn
  by_cases hΓ : t.NP Γ w
  · have hwr : w ≠ t.root := by
      rintro rfl
      obtain ⟨z, hz, hzr⟩ := hroot
      exact hΓ z hz hzr
    exact hn (t.r0 w) (t.mem_next.2 (Or.inr ⟨c, hc, Or.inr (t.mem_railsUp.2 ⟨w, hΓ, hw, Or.inl rfl⟩)⟩))
      (t.vertM_r0 hwr)
  · simp only [NP, not_forall, not_not] at hΓ
    obtain ⟨z, hz, hzw⟩ := hΓ
    exact hn z (t.mem_next.2 (Or.inl hz)) hzw

/-- **The next level for any cut.** A dart belongs to it if it is a corner, a corner of the cut, or a rail
of a vertex whose interval on the tour through all darts holds a corner of the cut. -/
theorem mem_next_iff_cut {Γ C : Finset (D × Bool)} {w₀ : D × Bool} (hL : t.IsLevel Γ)
    (h₀ : t.vertM w₀ = t.root) (h₁ : w₀.2 = true) (z : D × Bool) :
    z ∈ t.next Γ C ↔ z ∈ Γ ∨ z ∈ C ∨
      ∃ u, u ≠ t.root ∧ (z = t.r0 u ∨ z = t.c0 u) ∧ ∃ c ∈ C,
        pos (t.tau w₀) w₀ (t.c1 u) ≤ pos (t.tau w₀) w₀ c ∧
          pos (t.tau w₀) w₀ c ≤ pos (t.tau w₀) w₀ (t.r0 u) := by
  rw [t.mem_next]
  constructor
  · rintro (h | ⟨c, hc, rfl | h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl hc)
    · obtain ⟨w, hwn, ha, hz⟩ := t.mem_railsUp.1 h
      have hne := hwn.ne_root hL
      exact Or.inr (Or.inr ⟨w, hne, hz, c, hc, (anc_iff_interval h₀ h₁ hne c).1 ha⟩)
  · rintro (h | h | ⟨u, hu, hz, c, hc, hi⟩)
    · exact Or.inl h
    · exact Or.inr ⟨z, h, Or.inl rfl⟩
    · by_cases hzΓ : z ∈ Γ
      · exact Or.inl hzΓ
      · have hn : t.NP Γ u := by
          rcases hz with rfl | rfl
          · exact np_of_r0_not_mem hL hu hzΓ
          · exact np_of_c0_not_mem hL hu hzΓ
        exact Or.inr ⟨c, hc, Or.inr (t.mem_railsUp.2 ⟨u, hn, (anc_iff_interval h₀ h₁ hu c).2 hi, hz⟩)⟩

section Forced

variable (code : D × Bool → ℕ) (W : ℕ) (fid : D × Bool → ℕ) (w₀ : D × Bool) (C₀ : Finset (D × Bool))

variable (t) in
/-- Levels with the prescribed first cut `C₀`, then the rule. -/
noncomputable def forcedSeq : ℕ → Finset (D × Bool)
  | 0 => {w₀}
  | d + 1 => t.next (forcedSeq d) (if d = 0 then C₀ else t.sel code W fid (forcedSeq d))

variable (t) in
/-- The cuts of `forcedSeq`. -/
noncomputable def forcedCut (d : ℕ) : Finset (D × Bool) :=
  if d = 0 then C₀ else t.sel code W fid (t.forcedSeq code W fid w₀ C₀ d)

variable {code W fid w₀ C₀}

theorem forcedSeq_succ (d : ℕ) :
    t.forcedSeq code W fid w₀ C₀ (d + 1) =
      t.next (t.forcedSeq code W fid w₀ C₀ d) (t.forcedCut code W fid w₀ C₀ d) := rfl

/-- **The forced levels are a decomposition.** -/
theorem forcedSeq_decomp (h₀ : t.vertM w₀ = t.root) (h₁ : w₀.2 = true) (hR : R.Planar)
    (hc : R.Connected) (hinj : Function.Injective code) (hW : ∀ z, code z < W)
    (hfid : ∀ x y, fid x = fid y ↔ fconnect R.double.facePerm x y)
    (hC : ∀ c ∈ C₀, c.2 = true) (hcard : C₀.card ≤ 2) :
    t.Decomp w₀ (t.forcedSeq code W fid w₀ C₀) (t.forcedCut code W fid w₀ C₀) := by
  have hL₀ := isLevel_singleton (t := t) h₀ h₁
  have hcut : ∀ d, t.IsLevel (t.forcedSeq code W fid w₀ C₀ d) → w₀ ∈ t.forcedSeq code W fid w₀ C₀ d →
      t.IsCutW (t.forcedSeq code W fid w₀ C₀ d) (t.forcedCut code W fid w₀ C₀ d) := by
    intro d hL hw
    unfold forcedCut
    split_ifs
    · exact isCutW_of_true hC hcard
    · exact (isCut_sel hL₀ hL hw hR hc hinj hW hfid).toW
  have hall : ∀ d, t.IsLevel (t.forcedSeq code W fid w₀ C₀ d) ∧ w₀ ∈ t.forcedSeq code W fid w₀ C₀ d := by
    intro d
    induction d with
    | zero => exact ⟨hL₀, Finset.mem_singleton_self _⟩
    | succ d ih =>
      obtain ⟨hL, hw⟩ := ih
      rw [forcedSeq_succ]
      exact ⟨hL.next (hcut d hL hw).pair, subset_next _ _ hw⟩
  exact ⟨h₀, h₁, rfl, forcedSeq_succ, fun d => hcut d (hall d).1 (hall d).2⟩

/-- The cuts after the prescribed one are balanced. -/
theorem forcedSeq_bal (h₀ : t.vertM w₀ = t.root) (h₁ : w₀.2 = true) (hR : R.Planar)
    (hc : R.Connected) (hinj : Function.Injective code) (hW : ∀ z, code z < W)
    (hfid : ∀ x y, fid x = fid y ↔ fconnect R.double.facePerm x y)
    (hC : ∀ c ∈ C₀, c.2 = true) (hcard : C₀.card ≤ 2) :
    t.BalFrom (t.forcedSeq code W fid w₀ C₀) 1 := fun d hd u hu => by
  have hD := forcedSeq_decomp h₀ h₁ hR hc hinj hW hfid hC hcard
  have hb := (isCut_sel (isLevel_singleton (t := t) h₀ h₁) (hD.level d) (hD.w₀_mem d) hR hc hinj hW
    hfid).balance u hu
  have hd0 : d ≠ 0 := by omega
  rw [forcedSeq_succ, forcedCut]
  simpa only [hd0, ↓reduceIte] using hb

/-- **Height with a prescribed first cut.** One level more than for the rule alone. -/
theorem forcedSeq_final (h₀ : t.vertM w₀ = t.root) (h₁ : w₀.2 = true) (hR : R.Planar)
    (hc : R.Connected) (hinj : Function.Injective code) (hW : ∀ z, code z < W)
    (hfid : ∀ x y, fid x = fid y ↔ fconnect R.double.facePerm x y)
    (hC : ∀ c ∈ C₀, c.2 = true) (hcard : C₀.card ≤ 2) {k : ℕ} (hk : 2 * Fintype.card V < 2 ^ k)
    (v : V) : ¬ t.NP (t.forcedSeq code W fid w₀ C₀ (1 + 3 * k)) v :=
  (forcedSeq_decomp h₀ h₁ hR hc hinj hW hfid hC hcard).final
    (forcedSeq_bal h₀ h₁ hR hc hinj hW hfid hC hcard) hk v

/-- **The prescribed cut reaches the root.** From the first level on, every ancestor of the vertex of a
corner of `C₀` has a corner. -/
theorem not_np_forcedSeq (hD : t.Decomp w₀ (t.forcedSeq code W fid w₀ C₀) (t.forcedCut code W fid w₀ C₀))
    {c : D × Bool} (hc : c ∈ C₀) {w : V} (hw : t.Anc w (t.vertM c)) {d : ℕ} (hd : 1 ≤ d) :
    ¬ t.NP (t.forcedSeq code W fid w₀ C₀ d) w := by
  have h1 : ¬ t.NP (t.forcedSeq code W fid w₀ C₀ 1) w := by
    rw [forcedSeq_succ]
    exact not_np_next_of_anc ⟨w₀, Finset.mem_singleton_self _, hD.root⟩ (by simpa [forcedCut] using hc) hw
  exact fun hn => h1 fun z hz => hn z (hD.mono hd hz)

end Forced

section Hub

variable {code : D × Bool → ℕ} {Γ C : ℕ → Finset (D × Bool)} {w₀ : D × Bool}
  (hD : t.Decomp w₀ Γ C) (hc : R.Connected) (hinj : Function.Injective code)
  {adj : V → V → Prop} (hadj : ∀ a b, adj a b → ∃ d, t.vert d = a ∧ t.vert (R.rev d) = b)
  (hsurj : ∀ v, ∃ d, t.vert d = v) {H : ℕ} (hH : ∀ v, ¬ t.NP (Γ H) v)

/-- **Hubs of the root.** Every vertex with a corner in the first level is a hub of the root bag. -/
theorem Decomp.mem_hub_root {v : V} (hv : ¬ t.NP (Γ 1) v) :
    v ∈ (hD.hierarchy hc hinj hadj hsurj hH).hub (hD.hierarchy hc hinj hadj hsurj hH).root := by
  simp only [NP, not_forall, not_not] at hv
  obtain ⟨g, hg, hgv⟩ := hv
  have hb : R.InBag code Γ H (R.bagName code Γ 0 w₀) g := by
    refine (inBag_name (Nat.zero_le H) w₀).same ?_
    rw [bagName_fst]
    exact hD.same_zero hc _ _
  refine ⟨g, hb, ?_, hgv⟩
  show g ∈ Γ ((Nat.unpair (R.bagName code Γ 0 w₀)).1 + 1)
  rw [bagName_fst]
  exact hg

end Hub

/-- **The prescribed cut gives root hubs.** Every ancestor of the vertex of a corner of `C₀` is a hub of
the root bag of the hierarchy of the forced levels. -/
theorem forced_hub_root {code : D × Bool → ℕ} {W : ℕ} {fid : D × Bool → ℕ} {w₀ : D × Bool}
    {C₀ : Finset (D × Bool)}
    (hD : t.Decomp w₀ (t.forcedSeq code W fid w₀ C₀) (t.forcedCut code W fid w₀ C₀)) (hc : R.Connected)
    (hinj : Function.Injective code) {adj : V → V → Prop}
    (hadj : ∀ a b, adj a b → ∃ d, t.vert d = a ∧ t.vert (R.rev d) = b) (hsurj : ∀ v, ∃ d, t.vert d = v)
    {H : ℕ} (hH : ∀ v, ¬ t.NP (t.forcedSeq code W fid w₀ C₀ H) v)
    {c : D × Bool} (hcC : c ∈ C₀) {w : V} (hw : t.Anc w (t.vertM c)) :
    w ∈ (hD.hierarchy hc hinj hadj hsurj hH).hub (hD.hierarchy hc hinj hadj hsurj hH).root :=
  hD.mem_hub_root hc hinj hadj hsurj hH (not_np_forcedSeq hD hcC hw le_rfl)

end RootedTree

end RotSystem

end SsspFlow
