import Arborescence.WeakDuality

/-!
# Lemma 1 and Lemma 3 (the lists answer correctly)

`ListShape` is what a call `Build(G, K)` in container `C₀` with offsets `y₀` produces from an output `I` of
TopK, with no assumption on `I` except that it consists of items with distinct types: `L` is the set of
finite entries, sorted by `f`, and the flag says `|I| < K` or some entry has `f = ∞`.

Lemma 3 then speaks about a later container `C ⊇ C₀` and later offsets `y`, shifted by one constant on `G`.
Parts (a) and (b) need `IsTopK`. Part (c), the growth bound, needs only `ListShape`, which is the claim of
the proof of Theorem 1 that the accounting does not depend on TopK being correct.
-/

set_option linter.unusedSectionVars false

open Finset

namespace Arborescence

section TopK

variable {ι T : Type*} [DecidableEq T] {items : Finset ι} {f : ι → WithTop ℤ} {ty : ι → T} {d' : ℕ}
  {I : Finset ι}

/-- **Lemma 1(a).** Each entry is the minimum of its type. -/
theorem IsTopK.min_of_type (h : IsTopK items f ty d' I) {i j : ι} (hi : i ∈ I) (hj : j ∈ items)
    (hty : ty j = ty i) : f i ≤ f j := by
  by_contra hlt
  push Not at hlt
  have hji : j ∉ I := by
    intro hjI
    have : j = i := h.inj hjI hi hty
    subst this
    exact lt_irrefl _ hlt
  obtain ⟨i', hi', hty', hle⟩ := h.spec j hj hji i hi hlt
  have : i' = i := h.inj hi' hi (hty'.trans hty)
  subst this
  exact absurd hle (not_le.mpr hlt)

/-- **Lemma 1(b).** If `|I| < d'` or some entry has `f = ∞`, then every type with a finite value has a finite
entry in `I`. -/
theorem IsTopK.finite_entry (h : IsTopK items f ty d' I) (hc : I.card < d' ∨ ∃ i ∈ I, f i = ⊤) {j : ι}
    (hj : j ∈ items) (hf : f j ≠ ⊤) : ∃ i ∈ I, ty i = ty j ∧ f i ≠ ⊤ := by
  rcases hc with hc | ⟨i, hi, hfi⟩
  · have hcard : I.card = (items.image ty).card := by
      have := h.card_eq
      omega
    classical
    have hsub : I.image ty ⊆ items.image ty := Finset.image_subset_image h.subset
    have hcardI : (I.image ty).card = I.card := Finset.card_image_of_injOn h.inj
    have heq : I.image ty = items.image ty :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hmem : ty j ∈ I.image ty := heq ▸ Finset.mem_image_of_mem ty hj
    obtain ⟨i, hi, hti⟩ := Finset.mem_image.mp hmem
    refine ⟨i, hi, hti, fun hfi => hf ?_⟩
    have := h.min_of_type hi hj hti.symm
    rw [hfi] at this
    exact top_le_iff.mp this
  · by_cases hjI : j ∈ I
    · exact ⟨j, hjI, rfl, hf⟩
    · have hlt : f j < f i := by
        rw [hfi]
        exact lt_top_iff_ne_top.mpr hf
      obtain ⟨i', hi', hty', hle⟩ := h.spec j hj hjI i hi hlt
      refine ⟨i', hi', hty', fun htop => hf ?_⟩
      rw [htop] at hle
      exact top_le_iff.mp hle

end TopK

variable {V : Type*} [Fintype V] [DecidableEq V] {g : Graph V}

theorem buildF_ne_top {C : Finset V} {y : V → ℤ} {e : V × V} :
    buildF g C y e ≠ ⊤ ↔ g.adj e.1 e.2 = true ∧ e.1 ∉ C := by
  unfold buildF
  split_ifs with h
  · simp [h]
  · simp [h]

theorem buildF_of_ne_top {C : Finset V} {y : V → ℤ} {e : V × V} (h : g.adj e.1 e.2 = true ∧ e.1 ∉ C) :
    buildF g C y e = ((g.w e.1 e.2 - y e.2 : ℤ) : WithTop ℤ) := by
  simp [buildF, h]

theorem mem_inEdges {G : Finset V} {e : V × V} : e ∈ inEdges g G ↔ g.adj e.1 e.2 = true ∧ e.2 ∈ G := by
  simp [inEdges]

/-- The data that `Build` derives from a TopK output `I`, with no assumption on `I` beyond the items and
the distinct types. -/
structure ListShape (g : Graph V) (G C₀ : Finset V) (y₀ : V → ℤ) (K : ℕ) (I : Finset (V × V))
    (L : List (V × V)) (complete : Bool) : Prop where
  subset : I ⊆ inEdges g G
  inj : Set.InjOn Prod.fst (I : Set (V × V))
  sorted : L.Pairwise fun a b => buildF g C₀ y₀ a ≤ buildF g C₀ y₀ b
  mem_iff : ∀ e, e ∈ L ↔ e ∈ I ∧ buildF g C₀ y₀ e ≠ ⊤
  complete_iff : complete = true ↔ I.card < K ∨ ∃ i ∈ I, buildF g C₀ y₀ i = ⊤

/-- The first entry with source outside `C`. Discarding the leading entries with source in `C` and then
taking the head of the list comes to this. -/
def headOut (C : Finset V) (L : List (V × V)) : Option (V × V) := L.find? fun e => decide (e.1 ∉ C)

theorem headOut_mem {C : Finset V} {L : List (V × V)} {e : V × V} (h : headOut C L = some e) :
    e ∈ L ∧ e.1 ∉ C := by
  have := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using this⟩

theorem headOut_none {C : Finset V} {L : List (V × V)} (h : headOut C L = none) {e : V × V} (he : e ∈ L) :
    e.1 ∈ C := by
  have := List.find?_eq_none.mp h e he
  simpa using this

theorem find?_le_of_pairwise {α : Type*} {r : α → α → Prop} (hr : ∀ a, r a a) {p : α → Bool} :
    ∀ {L : List α} {e : α}, L.Pairwise r → L.find? p = some e → ∀ e' ∈ L, p e' = true → r e e'
  | [], _, _, h, _, _, _ => by simp at h
  | a :: l, e, hL, h, e', he', hp => by
    rw [List.pairwise_cons] at hL
    by_cases hpa : p a = true
    · rw [List.find?_cons_of_pos hpa] at h
      obtain rfl : a = e := by simpa using h
      rcases List.mem_cons.mp he' with rfl | he'
      · exact hr _
      · exact hL.1 _ he'
    · rw [List.find?_cons_of_neg hpa] at h
      rcases List.mem_cons.mp he' with rfl | he'
      · exact absurd hp hpa
      · exact find?_le_of_pairwise hr hL.2 h e' he' hp

/-- An entry of the list is an edge with head in `G`, and its source was outside `C₀`. -/
theorem ListShape.entry {G C₀ : Finset V} {y₀ : V → ℤ} {K : ℕ} {I : Finset (V × V)} {L : List (V × V)}
    {complete : Bool} (hs : ListShape g G C₀ y₀ K I L complete) {e : V × V} (he : e ∈ L) :
    g.adj e.1 e.2 = true ∧ e.2 ∈ G ∧ e.1 ∉ C₀ := by
  obtain ⟨hI, hf⟩ := (hs.mem_iff e).mp he
  have h1 := mem_inEdges.mp (hs.subset hI)
  exact ⟨h1.1, h1.2, (buildF_ne_top.mp hf).2⟩

/-- **Lemma 3(a).** If `L` has an entry with source outside `C`, the first such entry minimizes the reduced
cost over the edges entering `C` with head in `G`, for offsets shifted by one constant on `G`. -/
theorem lemma3a {G C₀ C : Finset V} {y₀ y : V → ℤ} {t : ℤ} {K : ℕ} {I : Finset (V × V)}
    {L : List (V × V)} {complete : Bool} (hs : ListShape g G C₀ y₀ K I L complete)
    (ht : IsTopK (inEdges g G) (buildF g C₀ y₀) Prod.fst K I) (hC : C₀ ⊆ C)
    (hshift : ∀ v ∈ G, y v = y₀ v + t) {e : V × V} (he : headOut C L = some e) :
    g.adj e.1 e.2 = true ∧ e.2 ∈ G ∧ e.1 ∉ C ∧
      ∀ u v, g.adj u v = true → v ∈ G → u ∉ C → g.w e.1 e.2 - y e.2 ≤ g.w u v - y v := by
  obtain ⟨heL, heC⟩ := headOut_mem he
  obtain ⟨h1, h2, h3⟩ := hs.entry heL
  refine ⟨h1, h2, heC, fun u v huv hv hu => ?_⟩
  by_contra hlt
  push Not at hlt
  have hu0 : u ∉ C₀ := fun h => hu (hC h)
  have hfe : buildF g C₀ y₀ e = ((g.w e.1 e.2 - y₀ e.2 : ℤ) : WithTop ℤ) := buildF_of_ne_top ⟨h1, h3⟩
  have hfj : buildF g C₀ y₀ (u, v) = ((g.w u v - y₀ v : ℤ) : WithTop ℤ) :=
    buildF_of_ne_top (e := (u, v)) ⟨huv, hu0⟩
  have hlt' : buildF g C₀ y₀ (u, v) < buildF g C₀ y₀ e := by
    rw [hfe, hfj, WithTop.coe_lt_coe]
    have h4 := hshift _ h2
    have h5 := hshift _ hv
    omega
  have hle : ∀ e' ∈ L, e'.1 ∉ C → buildF g C₀ y₀ e ≤ buildF g C₀ y₀ e' := fun e' he' hC' =>
    find?_le_of_pairwise (r := fun a b => buildF g C₀ y₀ a ≤ buildF g C₀ y₀ b) (fun _ => le_rfl) hs.sorted he e' he' (by simpa using hC')
  have hitem : (u, v) ∈ inEdges g G := mem_inEdges.mpr ⟨huv, hv⟩
  by_cases hI : (u, v) ∈ I
  · have := hle (u, v) ((hs.mem_iff _).mpr ⟨hI, buildF_ne_top.mpr ⟨huv, hu0⟩⟩) hu
    exact absurd hlt' (not_lt.mpr this)
  · obtain ⟨i', hi', hty, hle'⟩ := ht.spec (u, v) hitem hI e (hs.mem_iff e |>.mp heL).1 hlt'
    have hty' : i'.1 = u := hty
    have hfin : buildF g C₀ y₀ i' ≠ ⊤ := by
      intro htop
      rw [htop, hfj] at hle'
      simp at hle'
    have := hle i' ((hs.mem_iff _).mpr ⟨hi', hfin⟩) (hty' ▸ hu)
    exact absurd (lt_of_le_of_lt (this.trans hle') hlt') (lt_irrefl _)

/-- **Lemma 3(b).** If `L` is complete and has no entry with source outside `C`, no edge enters `C` with
head in `G`. -/
theorem lemma3b {G C₀ C : Finset V} {y₀ : V → ℤ} {K : ℕ} {I : Finset (V × V)}
    {L : List (V × V)} {complete : Bool} (hs : ListShape g G C₀ y₀ K I L complete)
    (ht : IsTopK (inEdges g G) (buildF g C₀ y₀) Prod.fst K I) (hC : C₀ ⊆ C)
    (hc : complete = true) (he : headOut C L = none) :
    ∀ u v, g.adj u v = true → v ∈ G → u ∈ C := by
  intro u v huv hv
  by_contra hu
  have hu0 : u ∉ C₀ := fun h => hu (hC h)
  obtain ⟨i, hi, hty, hfin⟩ := ht.finite_entry ((hs.complete_iff).mp hc)
    ((mem_inEdges (e := (u, v))).mpr ⟨huv, hv⟩) ((buildF_ne_top (e := (u, v))).mpr ⟨huv, hu0⟩)
  have hty' : i.1 = u := hty
  exact hu (hty' ▸ headOut_none he ((hs.mem_iff i).mpr ⟨hi, hfin⟩))

/-- **Lemma 3(c).** If `L` is not complete and has no entry with source outside `C`, the container has grown
by at least `K` since the build. This uses only the shape of the list, not that TopK was correct. -/
theorem lemma3c {G C₀ C : Finset V} {y₀ : V → ℤ} {K : ℕ} {I : Finset (V × V)}
    {L : List (V × V)} {complete : Bool} (hs : ListShape g G C₀ y₀ K I L complete) (hC : C₀ ⊆ C)
    (hc : complete = false) (he : headOut C L = none) :
    K + C₀.card ≤ C.card := by
  have hnc : ¬ (I.card < K ∨ ∃ i ∈ I, buildF g C₀ y₀ i = ⊤) := fun h => by
    have := (hs.complete_iff).mpr h
    rw [hc] at this
    exact Bool.false_ne_true this
  push Not at hnc
  obtain ⟨hK, hfin⟩ := hnc
  have hsub : I.image Prod.fst ⊆ C \ C₀ := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    have hiL : i ∈ L := (hs.mem_iff i).mpr ⟨hi, hfin i hi⟩
    exact Finset.mem_sdiff.mpr ⟨headOut_none he hiL, (hs.entry hiL).2.2⟩
  have hcard : (I.image Prod.fst).card = I.card := Finset.card_image_of_injOn hs.inj
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_sdiff_add_card_eq_card hC
  omega

/-- After a fresh build in `C`, the first entry is the head, and a list without a head is complete. -/
theorem ListShape.complete_of_fresh {G C : Finset V} {y : V → ℤ} {K : ℕ} {I : Finset (V × V)}
    {L : List (V × V)} {complete : Bool} (hs : ListShape g G C y K I L complete) (hK : 1 ≤ K)
    (he : headOut C L = none) : complete = true := by
  cases hc : complete with
  | true => rfl
  | false =>
    have := lemma3c hs (Finset.Subset.refl C) hc he
    omega

end Arborescence
