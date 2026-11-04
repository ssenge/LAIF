import Covers.Basic
import Mathlib.Tactic.Ring

/-!
# The gap test of Section 3

`u` is a border of `S` of length `ℓ ≥ 1`. Starts are cut into blocks of `s = ⌈ℓ/2⌉`.

* `covers_iff_no_gap`: `u` covers `S` iff consecutive occurrences differ by at most `ℓ`.
* `lemma5`: `u` covers `S` iff no block satisfies the predicate `GapPred`.
* `lemma5_blocks`: the same with the quantifier restricted to the actual blocks, and `numBlocks_le` bounds their number
  by `2n/ℓ + 1`.
-/

namespace Strings

variable {α : Type*}

/-- `g < g'` are consecutive among the positions satisfying `O`. -/
def Consecutive (O : ℕ → Prop) (g g' : ℕ) : Prop :=
  O g ∧ O g' ∧ g < g' ∧ ∀ t, g < t → t < g' → ¬ O t

/-- `u` covers `S` iff consecutive occurrences differ by at most `|u|`, for a nonempty border `u`. -/
theorem covers_iff_no_gap {u S : List α} (hb : IsBorder u S) (hu : u ≠ []) :
    Covers u S ↔ ∀ g g', Consecutive (OccursAt u S) g g' → g' ≤ g + u.length := by
  have hℓ : 0 < u.length := List.length_pos_iff.2 hu
  have hle := hb.length_le
  constructor
  · rintro hcov g g' ⟨hg, hg', hlt, hcons⟩
    by_contra hgap
    have h' := hg'.1
    obtain ⟨t, ht, h1, h2⟩ := hcov (g + u.length) (by omega)
    exact hcons t (by omega) (by omega) ht
  · intro hgap p hp
    classical
    -- `g` is the largest occurrence at most `p`
    have hP : (OccursAt u S 0) ∧ 0 ≤ p := ⟨hb.occursAt_zero, Nat.zero_le _⟩
    set g := Nat.findGreatest (fun t => OccursAt u S t ∧ t ≤ p) p with hgdef
    have hspec : OccursAt u S g ∧ g ≤ p :=
      Nat.findGreatest_spec (P := fun t => OccursAt u S t ∧ t ≤ p) (Nat.zero_le p) hP
    have hmax : ∀ t, OccursAt u S t → t ≤ p → t ≤ g := fun t ht htp =>
      Nat.le_findGreatest htp ⟨ht, htp⟩
    by_cases hin : p < g + u.length
    · exact ⟨g, hspec.1, hspec.2, hin⟩
    · exfalso
      have hge : g < S.length - u.length := by omega
      -- `g'` is the next occurrence after `g`
      have hex : ∃ t, OccursAt u S t ∧ g < t := ⟨_, hb.occursAt_end, hge⟩
      obtain ⟨hg'occ, hg'lt⟩ := Nat.find_spec hex
      have hcons : Consecutive (OccursAt u S) g (Nat.find hex) :=
        ⟨hspec.1, hg'occ, hg'lt, fun t h1 h2 ht => Nat.find_min hex h2 ⟨ht, h1⟩⟩
      have := hgap _ _ hcons
      have hnot : ¬ Nat.find hex ≤ p := fun hle' => by
        have := hmax _ hg'occ hle'
        omega
      omega

/-- The block size `⌈ℓ/2⌉`. -/
def blockSize (ℓ : ℕ) : ℕ := (ℓ + 1) / 2

theorem blockSize_pos {ℓ : ℕ} (h : 0 < ℓ) : 0 < blockSize ℓ := by
  unfold blockSize; omega

theorem le_two_mul_blockSize (ℓ : ℕ) : ℓ ≤ 2 * blockSize ℓ := by
  unfold blockSize; omega

/-- `t` lies in block `j`. -/
def InBlock (s j t : ℕ) : Prop := s * j ≤ t ∧ t < s * (j + 1)

/-- `t` lies in one of the blocks `j, j + 1, j + 2`. -/
def InWindow (s j t : ℕ) : Prop := s * j ≤ t ∧ t < s * (j + 3)

/-- The occurrences of `u` in the window of `j`, for blocks of size `s`. -/
def WindowOcc (s : ℕ) (u S : List α) (j t : ℕ) : Prop := OccursAt u S t ∧ InWindow s j t

/-- The predicate of Section 3 for an arbitrary block size `s`. -/
def GapPredAt (s : ℕ) (u S : List α) (j : ℕ) : Prop :=
  (∃ g g', Consecutive (WindowOcc s u S j) g g' ∧ g + u.length < g') ∨
    (∃ g, WindowOcc s u S j g ∧ (∀ t, WindowOcc s u S j t → t ≤ g) ∧ InBlock s j g ∧
      g ≠ S.length - u.length)

/-- The predicate `pred(j)` of Section 3. Using the occurrences in blocks `j, j + 1, j + 2`: either two consecutive
ones differ by more than `ℓ`, or the last of them lies in block `j` and is not `n - ℓ`. -/
def GapPred (u S : List α) (j : ℕ) : Prop := GapPredAt (blockSize u.length) u S j

/-- **Lemma 5, for any block size `s` with `ℓ ≤ 2s`.** -/
theorem lemma5_at {u S : List α} {s : ℕ} (hb : IsBorder u S) (hu : u ≠ []) (hs : 0 < s)
    (hsℓ : u.length ≤ 2 * s) : Covers u S ↔ ∀ j, ¬ GapPredAt s u S j := by
  rw [covers_iff_no_gap hb hu]
  constructor
  · rintro hgap j (⟨g, g', ⟨hg, hg', hlt, hcons⟩, hd⟩ | ⟨g, hg, hlast, hblock, hne⟩)
    · -- the first rule: the window is an interval, so `g, g'` are consecutive overall
      have hc : Consecutive (OccursAt u S) g g' := by
        refine ⟨hg.1, hg'.1, hlt, fun t h1 h2 ht => hcons t h1 h2 ⟨ht, ?_⟩⟩
        exact ⟨by have := hg.2.1; omega, by have := hg'.2.2; omega⟩
      have := hgap _ _ hc
      omega
    · -- the second rule: the next occurrence is past block `j + 2`
      classical
      have hg1 := hg.1.1
      have hglt : g < S.length - u.length := by
        have := hb.length_le
        omega
      have hex : ∃ t, OccursAt u S t ∧ g < t := ⟨_, hb.occursAt_end, hglt⟩
      obtain ⟨hg'occ, hg'lt⟩ := Nat.find_spec hex
      have hc : Consecutive (OccursAt u S) g (Nat.find hex) :=
        ⟨hg.1, hg'occ, hg'lt, fun t h1 h2 ht => Nat.find_min hex h2 ⟨ht, h1⟩⟩
      have hfar : s * (j + 3) ≤ Nat.find hex := by
        by_contra hnear
        have := hlast _ ⟨hg'occ, by have := hg.2.1; exact ⟨by omega, by omega⟩⟩
        omega
      have := hgap _ _ hc
      have h2 := hblock.2
      have e1 : s * (j + 3) = s * (j + 1) + 2 * s := by ring
      omega
  · intro hno g g' hc
    by_contra hd
    have hd' : g + u.length < g' := by omega
    obtain ⟨hg, hg', hlt, hcons⟩ := hc
    -- the block of `g`
    set j := g / s with hj
    have hj1 : s * j ≤ g := Nat.mul_div_le g s
    have hj2 : g < s * (j + 1) := by
      rw [hj]; exact Nat.lt_mul_div_succ g hs
    have e1 : s * (j + 3) = s * (j + 1) + 2 * s := by ring
    have hgW : InWindow s j g := ⟨hj1, by omega⟩
    apply hno j
    by_cases hin : g' < s * (j + 3)
    · left
      refine ⟨g, g', ⟨⟨hg, hgW⟩, ⟨hg', ⟨by omega, hin⟩⟩, hlt, fun t h1 h2 ht => hcons t h1 h2 ht.1⟩, hd'⟩
    · right
      refine ⟨g, ⟨hg, hgW⟩, fun t ht => ?_, ⟨hj1, hj2⟩, ?_⟩
      · by_contra hgt
        have hlt' : g < t := by omega
        have : t < g' := by have := ht.2.2; omega
        exact hcons t hlt' this ht.1
      · have := hg'.1
        omega

/-- **Lemma 5.** For a nonempty border `u` of `S`, `u` covers `S` iff no block of size `⌈ℓ/2⌉` satisfies the predicate. -/
theorem lemma5 {u S : List α} (hb : IsBorder u S) (hu : u ≠ []) :
    Covers u S ↔ ∀ j, ¬ GapPred u S j :=
  lemma5_at hb hu (blockSize_pos (List.length_pos_iff.2 hu)) (le_two_mul_blockSize _)

/-- If the predicate holds at `j`, then block `j` is a block of actual starts: it begins at most at `n - ℓ`. -/
theorem GapPred.start_le {u S : List α} {j : ℕ} (hp : GapPred u S j) :
    blockSize u.length * j ≤ S.length - u.length := by
  rcases hp with ⟨g, g', ⟨hg, -⟩, -⟩ | ⟨g, hg, -⟩
  · have := hg.1.1
    have := hg.2.1
    omega
  · have := hg.1.1
    have := hg.2.1
    omega

/-- The number of blocks of starts in `[0, n - ℓ]`. -/
def numBlocks (n ℓ : ℕ) : ℕ := (n - ℓ) / blockSize ℓ + 1

/-- **Lemma 5, over the actual blocks.** -/
theorem lemma5_blocks {u S : List α} (hb : IsBorder u S) (hu : u ≠ []) :
    Covers u S ↔ ∀ j, j < numBlocks S.length u.length → ¬ GapPred u S j := by
  rw [lemma5 hb hu]
  refine ⟨fun h j _ => h j, fun h j hp => h j ?_ hp⟩
  have hℓ : 0 < u.length := List.length_pos_iff.2 hu
  have := hp.start_le
  have hj : j ≤ (S.length - u.length) / blockSize u.length :=
    (Nat.le_div_iff_mul_le (blockSize_pos hℓ)).2 (by rwa [Nat.mul_comm])
  unfold numBlocks
  omega

/-- There are at most `2n/ℓ + 1` blocks, as Lemma 6 uses. -/
theorem numBlocks_le {n ℓ : ℕ} (hℓ : 0 < ℓ) : numBlocks n ℓ ≤ 2 * n / ℓ + 1 := by
  unfold numBlocks
  have hs := blockSize_pos hℓ
  have htwo := le_two_mul_blockSize ℓ
  have hk : (n - ℓ) / blockSize ℓ * blockSize ℓ ≤ n - ℓ := Nat.div_mul_le_self _ _
  refine Nat.succ_le_succ ((Nat.le_div_iff_mul_le hℓ).2 ?_)
  calc (n - ℓ) / blockSize ℓ * ℓ ≤ (n - ℓ) / blockSize ℓ * (2 * blockSize ℓ) :=
        Nat.mul_le_mul_left _ htwo
    _ = 2 * ((n - ℓ) / blockSize ℓ * blockSize ℓ) := by ring
    _ ≤ 2 * n := by omega

end Strings
