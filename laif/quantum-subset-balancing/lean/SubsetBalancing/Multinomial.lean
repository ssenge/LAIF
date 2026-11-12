import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith

/-!
# Functions with exact fibre sizes

The number of functions from a set `A` to a set `B` with a prescribed fibre size over each `b ∈ B` is
a multinomial coefficient, when the sizes add up to `|A|`. For several disjoint sets `A k`, each with
its own constraint, the count is the product of the multinomials. The representations of a solution
are functions of this kind, with one set `A k` for each class.

The functions are total on the index type and frozen to a base function `g` outside the sets, so that
the bookkeeping stays within `ι → ℤ`.
-/

open Finset

namespace SubsetBalancing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The functions equal to `g` outside `A`, with values in `B` on `A` and fibre sizes `n`. -/
def typed (A : Finset ι) (B : Finset ℤ) (n : ℤ → ℕ) (g : ι → ℤ) : Finset (ι → ℤ) :=
  (Fintype.piFinset fun i => if i ∈ A then B else {g i}).filter
    fun f => ∀ b ∈ B, #{i ∈ A | f i = b} = n b

theorem mem_typed {A : Finset ι} {B : Finset ℤ} {n : ℤ → ℕ} {g f : ι → ℤ} :
    f ∈ typed A B n g ↔ (∀ i, i ∉ A → f i = g i) ∧ (∀ i ∈ A, f i ∈ B) ∧
      ∀ b ∈ B, #{i ∈ A | f i = b} = n b := by
  simp only [typed, mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_, h2⟩
    · simpa [hi] using h1 i
    · simpa [hi] using h1 i
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => ?_, h3⟩
    by_cases hi : i ∈ A
    · simpa [hi] using h2 i hi
    · simpa [hi] using h1 i hi

/-- **One class.** If the sizes `n` over `B` add up to `|A|`, there are `multinomial B n` functions
from `A` to `B` with fibre sizes `n`. -/
theorem card_typed (A : Finset ι) (B : Finset ℤ) (n : ℤ → ℕ) (g : ι → ℤ)
    (hsum : ∑ b ∈ B, n b = #A) : #(typed A B n g) = Nat.multinomial B n := by
  induction B using Finset.induction_on generalizing A g with
  | empty =>
    have hA : A = ∅ := by
      rw [← card_eq_zero, ← hsum]
      simp
    subst hA
    have : typed ∅ ∅ n g = {g} := by
      ext f
      simp only [mem_typed, notMem_empty, not_false_eq_true, forall_const, IsEmpty.forall_iff,
        implies_true, and_true, mem_singleton]
      exact ⟨fun h => funext h, fun h i => by rw [h]⟩
    rw [this]
    simp [Nat.multinomial]
  | insert b B hb ih =>
    rw [sum_insert hb] at hsum
    -- the fibres of the map sending `f` to the coordinates where it takes the value `b`
    have hmaps : ∀ f ∈ typed A (insert b B) n g,
        ({i ∈ A | f i = b} : Finset ι) ∈ powersetCard (n b) A := by
      intro f hf
      obtain ⟨-, -, h3⟩ := mem_typed.mp hf
      exact mem_powersetCard.mpr ⟨filter_subset _ _, h3 b (mem_insert_self _ _)⟩
    have hfib : ∀ S ∈ powersetCard (n b) A,
        #{f ∈ typed A (insert b B) n g | ({i ∈ A | f i = b} : Finset ι) = S}
          = Nat.multinomial B n := by
      intro S hS
      obtain ⟨hSA, hScard⟩ := mem_powersetCard.mp hS
      have hset : ({f ∈ typed A (insert b B) n g | ({i ∈ A | f i = b} : Finset ι) = S})
          = typed (A \ S) B n (fun i => if i ∈ S then b else g i) := by
        ext f
        simp only [mem_filter, mem_typed, mem_sdiff, not_and, not_not, mem_insert]
        constructor
        · rintro ⟨⟨h1, h2, h3⟩, h4⟩
          have hmemS : ∀ i, i ∈ S ↔ i ∈ A ∧ f i = b := fun i => by
            rw [← h4]
            simp
          refine ⟨fun i hi => ?_, fun i hi => ?_, fun c hc => ?_⟩
          · by_cases hiS : i ∈ S
            · simp [hiS, ((hmemS i).mp hiS).2]
            · simp only [hiS, ite_false]
              refine h1 i fun hiA => hiS (hi hiA)
          · rcases h2 i hi.1 with h | h
            · exact absurd ((hmemS i).mpr ⟨hi.1, h⟩) hi.2
            · exact h
          · rw [← h3 c (Or.inr hc)]
            congr 1
            ext i
            simp only [mem_filter, mem_sdiff]
            constructor
            · rintro ⟨⟨h5, -⟩, h6⟩
              exact ⟨h5, h6⟩
            · rintro ⟨h5, h6⟩
              refine ⟨⟨h5, fun hiS => ?_⟩, h6⟩
              have := ((hmemS i).mp hiS).2
              rw [this] at h6
              exact hb (h6 ▸ hc)
        · rintro ⟨h1, h2, h3⟩
          have hoffS : ∀ i ∈ S, f i = b := fun i hi => by
            have := h1 i (fun _ => hi)
            simpa [hi] using this
          have hfilter : ({i ∈ A | f i = b} : Finset ι) = S := by
            ext i
            simp only [mem_filter]
            constructor
            · rintro ⟨hiA, hib⟩
              by_contra hiS
              exact hb (hib ▸ h2 i ⟨hiA, hiS⟩)
            · exact fun hi => ⟨hSA hi, hoffS i hi⟩
          refine ⟨⟨fun i hi => ?_, fun i hi => ?_, fun c hc => ?_⟩, hfilter⟩
          · have hiS : i ∉ S := fun h => hi (hSA h)
            have := h1 i (fun h => absurd h hi)
            simpa [hiS] using this
          · by_cases hiS : i ∈ S
            · exact Or.inl (hoffS i hiS)
            · exact Or.inr (h2 i ⟨hi, hiS⟩)
          · rcases hc with rfl | hc'
            · rw [hfilter, hScard]
            · rw [← h3 c hc']
              congr 1
              ext i
              simp only [mem_filter, mem_sdiff]
              constructor
              · rintro ⟨h5, h6⟩
                refine ⟨⟨h5, fun hiS => ?_⟩, h6⟩
                rw [hoffS i hiS] at h6
                exact hb (h6 ▸ hc')
              · rintro ⟨⟨h5, -⟩, h6⟩
                exact ⟨h5, h6⟩
      rw [hset]
      refine ih _ _ ?_
      rw [card_sdiff_of_subset hSA, hScard]
      omega
    rw [card_eq_sum_card_fiberwise hmaps, sum_congr rfl hfib, sum_const, card_powersetCard,
      smul_eq_mul, Nat.multinomial_insert hb, ← hsum]

/-- The functions equal to `g` outside the sets `A k`, `k ∈ K`, and typed on each of them. -/
def typedAll {κ : Type*} [DecidableEq κ] (A : κ → Finset ι) (B : κ → Finset ℤ) (n : κ → ℤ → ℕ)
    (g : ι → ℤ) (K : Finset κ) : Finset (ι → ℤ) :=
  (Fintype.piFinset fun i => if i ∈ K.biUnion A then K.biUnion B else {g i}).filter
    fun f => ∀ k ∈ K, (∀ i ∈ A k, f i ∈ B k) ∧ ∀ b ∈ B k, #{i ∈ A k | f i = b} = n k b

theorem mem_typedAll {κ : Type*} [DecidableEq κ] {A : κ → Finset ι} {B : κ → Finset ℤ}
    {n : κ → ℤ → ℕ} {g f : ι → ℤ} {K : Finset κ} :
    f ∈ typedAll A B n g K ↔ (∀ i, (∀ k ∈ K, i ∉ A k) → f i = g i) ∧
      ∀ k ∈ K, (∀ i ∈ A k, f i ∈ B k) ∧ ∀ b ∈ B k, #{i ∈ A k | f i = b} = n k b := by
  simp only [typedAll, mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, h2⟩
    have hni : i ∉ K.biUnion A := by
      simp only [mem_biUnion, not_exists, not_and]
      exact hi
    simpa [hni] using h1 i
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, h2⟩
    by_cases hi : i ∈ K.biUnion A
    · obtain ⟨k, hk, hik⟩ := mem_biUnion.mp hi
      simp only [hi, ite_true]
      exact mem_biUnion.mpr ⟨k, hk, (h2 k hk).1 i hik⟩
    · have hni : ∀ k ∈ K, i ∉ A k := fun k hk hik => hi (mem_biUnion.mpr ⟨k, hk, hik⟩)
      simpa [hi] using h1 i hni

/-- **Several classes.** For pairwise disjoint sets `A k`, with sizes adding up to `|A k|` for each
`k ∈ K`, the number of functions typed on every `A k` is the product of the multinomials. -/
theorem card_typedAll {κ : Type*} [DecidableEq κ] (A : κ → Finset ι) (B : κ → Finset ℤ)
    (n : κ → ℤ → ℕ) (g : ι → ℤ) (K : Finset κ)
    (hdisj : ∀ k k', k ≠ k' → Disjoint (A k) (A k'))
    (hsum : ∀ k ∈ K, ∑ b ∈ B k, n k b = #(A k)) :
    #(typedAll A B n g K) = ∏ k ∈ K, Nat.multinomial (B k) (n k) := by
  induction K using Finset.induction_on with
  | empty =>
    have : typedAll A B n g ∅ = {g} := by
      ext f
      simp only [mem_typedAll, notMem_empty, IsEmpty.forall_iff, implies_true, and_true,
        mem_singleton]
      exact ⟨fun h => funext fun i => h i trivial, fun h i _ => by rw [h]⟩
    rw [this]
    simp
  | insert k K hk ih =>
    have hsum' : ∀ k' ∈ K, ∑ b ∈ B k', n k' b = #(A k') := fun k' hk' =>
      hsum k' (mem_insert_of_mem hk')
    rw [prod_insert hk, mul_comm, ← ih hsum']
    set Φ : (ι → ℤ) → (ι → ℤ) := fun f i => if i ∈ A k then g i else f i with hΦ
    have hnotin : ∀ k' ∈ K, ∀ i ∈ A k, i ∉ A k' := fun k' hk' i hi hi' =>
      disjoint_left.mp (hdisj k k' fun h => hk (h ▸ hk')) hi hi'
    have hmaps : ∀ f ∈ typedAll A B n g (insert k K), Φ f ∈ typedAll A B n g K := by
      intro f hf
      obtain ⟨h1, h2⟩ := mem_typedAll.mp hf
      refine mem_typedAll.mpr ⟨fun i hi => ?_, fun k' hk' => ?_⟩
      · by_cases hik : i ∈ A k
        · simp [hΦ, hik]
        · simp only [hΦ, hik, ite_false]
          refine h1 i fun k'' hk'' => ?_
          rcases mem_insert.mp hk'' with rfl | hk''
          · exact hik
          · exact hi k'' hk''
      · have hA : ∀ i ∈ A k', Φ f i = f i := fun i hi => by
          have : i ∉ A k := fun h => hnotin k' hk' i h hi
          simp [hΦ, this]
        obtain ⟨h3, h4⟩ := h2 k' (mem_insert_of_mem hk')
        refine ⟨fun i hi => ?_, fun b hb => ?_⟩
        · rw [hA i hi]
          exact h3 i hi
        · rw [← h4 b hb]
          congr 1
          ext i
          simp only [mem_filter]
          constructor
          · rintro ⟨h5, h6⟩
            exact ⟨h5, by rwa [hA i h5] at h6⟩
          · rintro ⟨h5, h6⟩
            exact ⟨h5, by rwa [hA i h5]⟩
    have hfib : ∀ h ∈ typedAll A B n g K,
        #{f ∈ typedAll A B n g (insert k K) | Φ f = h} = Nat.multinomial (B k) (n k) := by
      intro h hh
      obtain ⟨hh1, hh2⟩ := mem_typedAll.mp hh
      have hset : ({f ∈ typedAll A B n g (insert k K) | Φ f = h})
          = typed (A k) (B k) (n k) h := by
        ext f
        simp only [mem_filter, mem_typedAll, mem_typed]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          obtain ⟨h4, h5⟩ := h2 k (mem_insert_self _ _)
          refine ⟨fun i hi => ?_, h4, h5⟩
          rw [← h3]
          simp [hΦ, hi]
        · rintro ⟨h1, h2, h3⟩
          refine ⟨⟨fun i hi => ?_, fun k' hk' => ?_⟩, ?_⟩
          · have hik : i ∉ A k := hi k (mem_insert_self _ _)
            rw [h1 i hik]
            exact hh1 i fun k'' hk'' => hi k'' (mem_insert_of_mem hk'')
          · rcases mem_insert.mp hk' with rfl | hk'
            · exact ⟨h2, h3⟩
            · obtain ⟨h4, h5⟩ := hh2 k' hk'
              have hA : ∀ i ∈ A k', f i = h i := fun i hi =>
                h1 i fun h => hnotin k' hk' i h hi
              refine ⟨fun i hi => ?_, fun b hb => ?_⟩
              · rw [hA i hi]
                exact h4 i hi
              · rw [← h5 b hb]
                congr 1
                ext i
                simp only [mem_filter]
                constructor
                · rintro ⟨h6, h7⟩
                  exact ⟨h6, by rwa [hA i h6] at h7⟩
                · rintro ⟨h6, h7⟩
                  exact ⟨h6, by rwa [hA i h6]⟩
          · funext i
            by_cases hik : i ∈ A k
            · simp only [hΦ, hik, ite_true]
              exact (hh1 i fun k' hk' => hnotin k' hk' i hik).symm
            · simp only [hΦ, hik, ite_false]
              exact h1 i hik
      rw [hset]
      exact card_typed _ _ _ _ (hsum k (mem_insert_self _ _))
    rw [card_eq_sum_card_fiberwise hmaps, sum_congr rfl hfib, sum_const, smul_eq_mul]

end SubsetBalancing
