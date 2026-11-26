import GHMatrix.Arith

/-! Lemma 4 of `laif/quantum-gomory-hu`: in the hard family of Theorem 2, every cut with at least
two vertices on each side has at least `Δ = 2h + s − 1` crossing edges. -/

namespace GHMatrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Crossing pairs of a cut `(S, V ∖ S)`: ordered pairs `(x, y)` with `x ∈ S`, `y ∉ S` and `adj x y`.
Each crossing edge of a graph is counted once. -/
def crossing (adj : V → V → Prop) [DecidableRel adj] (S : Finset V) : Finset (V × V) :=
  (S ×ˢ (Finset.univ \ S)).filter (fun p => adj p.1 p.2)

/-- **Lemma 4.** `L` and `R` partition the vertices, have `h + s` vertices each and are cliques;
`L₂ ⊆ L` and `R₂ ⊆ R` have `h` vertices each and are completely joined. Any further edges (the set
`B`) are allowed. Then every cut with at least two vertices on each side has at least `2h + s − 1`
crossing edges, provided `3 ≤ s < h`. -/
theorem lemma4 (adj : V → V → Prop) [DecidableRel adj] (L R L₂ R₂ : Finset V) (h s : ℕ)
    (hs : 3 ≤ s) (hsh : s < h) (hL2 : L₂ ⊆ L) (hR2 : R₂ ⊆ R)
    (hLc : L.card = h + s) (hRc : R.card = h + s) (hL2c : L₂.card = h) (hR2c : R₂.card = h)
    (hdisj : Disjoint L R) (hcov : L ∪ R = Finset.univ)
    (hLL : ∀ x ∈ L, ∀ y ∈ L, x ≠ y → adj x y) (hRR : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → adj x y)
    (hLR : ∀ x ∈ L₂, ∀ y ∈ R₂, adj x y ∧ adj y x)
    (S : Finset V) (hS : 2 ≤ S.card) (hT : 2 ≤ (Finset.univ \ S).card) :
    2 * h + s - 1 ≤ (crossing adj S).card := by
  classical
  set P1 := (S ∩ L) ×ˢ (L \ S)
  set P2 := (S ∩ R) ×ˢ (R \ S)
  set P3 := (S ∩ L₂) ×ˢ (R₂ \ S)
  set P4 := (S ∩ R₂) ×ˢ (L₂ \ S)
  have nLR : ∀ x, x ∈ L → x ∉ R := fun x hx hr => Finset.disjoint_left.1 hdisj hx hr
  have sub : P1 ∪ P2 ∪ P3 ∪ P4 ⊆ crossing adj S := by
    intro p hp
    simp only [P1, P2, P3, P4, Finset.mem_union, Finset.mem_product, Finset.mem_inter,
      Finset.mem_sdiff] at hp
    simp only [crossing, Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ,
      true_and]
    rcases hp with ((⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩) | ⟨⟨h1, h2⟩, h3, h4⟩) |
      ⟨⟨h1, h2⟩, h3, h4⟩
    · exact ⟨⟨h1, h4⟩, hLL _ h2 _ h3 (fun e => h4 (e ▸ h1))⟩
    · exact ⟨⟨h1, h4⟩, hRR _ h2 _ h3 (fun e => h4 (e ▸ h1))⟩
    · exact ⟨⟨h1, h4⟩, (hLR _ h2 _ h3).1⟩
    · exact ⟨⟨h1, h4⟩, (hLR _ h3 _ h2).2⟩
  have d12 : Disjoint P1 P2 := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [P1, P2, Finset.mem_product, Finset.mem_inter] at h1 h2
    exact nLR _ h1.1.2 h2.1.2
  have d123 : Disjoint (P1 ∪ P2) P3 := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [P1, P2, P3, Finset.mem_union, Finset.mem_product, Finset.mem_inter,
      Finset.mem_sdiff] at h1 h2
    rcases h1 with h1 | h1
    · exact nLR _ h1.2.1 (hR2 h2.2.1)
    · exact nLR _ (hL2 h2.1.2) h1.1.2
  have d1234 : Disjoint (P1 ∪ P2 ∪ P3) P4 := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [P1, P2, P3, P4, Finset.mem_union, Finset.mem_product, Finset.mem_inter,
      Finset.mem_sdiff] at h1 h2
    rcases h1 with (h1 | h1) | h1
    · exact nLR _ h1.1.2 (hR2 h2.1.2)
    · exact nLR _ (hL2 h2.2.1) h1.2.1
    · exact nLR _ (hL2 h1.1.2) (hR2 h2.1.2)
  have hcard := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint d1234, Finset.card_union_of_disjoint d123,
    Finset.card_union_of_disjoint d12] at hcard
  simp only [P1, P2, P3, P4, Finset.card_product] at hcard
  -- side counts
  have eL := Finset.card_sdiff_add_card_inter L S
  have eR := Finset.card_sdiff_add_card_inter R S
  have eL2 := Finset.card_sdiff_add_card_inter L₂ S
  have eR2 := Finset.card_sdiff_add_card_inter R₂ S
  rw [Finset.inter_comm] at eL eR eL2 eR2
  have a2a : (S ∩ L₂).card ≤ (S ∩ L).card :=
    Finset.card_le_card (Finset.inter_subset_inter_left hL2)
  have b2b : (S ∩ R₂).card ≤ (S ∩ R).card :=
    Finset.card_le_card (Finset.inter_subset_inter_left hR2)
  have aa2 : (S ∩ L).card ≤ (S ∩ L₂).card + s := by
    have h1 : S ∩ L ⊆ (S ∩ L₂) ∪ (L \ L₂) := by
      intro x hx; by_cases hx2 : x ∈ L₂
      · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hx).1, hx2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨(Finset.mem_inter.1 hx).2, hx2⟩)
    have h2 := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
    rw [Finset.card_sdiff_of_subset hL2] at h2; omega
  have bb2 : (S ∩ R).card ≤ (S ∩ R₂).card + s := by
    have h1 : S ∩ R ⊆ (S ∩ R₂) ∪ (R \ R₂) := by
      intro x hx; by_cases hx2 : x ∈ R₂
      · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hx).1, hx2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨(Finset.mem_inter.1 hx).2, hx2⟩)
    have h2 := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
    rw [Finset.card_sdiff_of_subset hR2] at h2; omega
  have a2h : (S ∩ L₂).card ≤ h := hL2c ▸ Finset.card_le_card Finset.inter_subset_right
  have b2h : (S ∩ R₂).card ≤ h := hR2c ▸ Finset.card_le_card Finset.inter_subset_right
  have hSab : S.card = (S ∩ L).card + (S ∩ R).card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hdisj)), ← Finset.inter_union_distrib_left,
      hcov, Finset.inter_univ]
  have huniv : (Finset.univ : Finset V).card = 2 * (h + s) := by
    rw [← hcov, Finset.card_union_of_disjoint hdisj, hLc, hRc]; ring
  have hTc : (Finset.univ \ S).card + S.card = 2 * (h + s) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), huniv.symm]
    have := Finset.card_le_univ S; omega
  have key := arith (h : ℤ) s (S ∩ L).card (S ∩ R).card (S ∩ L₂).card (S ∩ R₂).card
    (by exact_mod_cast hs) (by exact_mod_cast hsh) (by positivity) (by positivity)
    (by exact_mod_cast a2a) (by exact_mod_cast b2b) (by exact_mod_cast a2h) (by exact_mod_cast b2h)
    (by exact_mod_cast aa2) (by exact_mod_cast bb2) (by omega) (by omega)
  have cL : ((L \ S).card : ℤ) = h + s - (S ∩ L).card := by omega
  have cR : ((R \ S).card : ℤ) = h + s - (S ∩ R).card := by omega
  have cL2 : ((L₂ \ S).card : ℤ) = h - (S ∩ L₂).card := by omega
  have cR2 : ((R₂ \ S).card : ℤ) = h - (S ∩ R₂).card := by omega
  have : ((2 * h + s - 1 : ℕ) : ℤ) ≤ ((crossing adj S).card : ℤ) := by
    have hc : ((((S ∩ L).card * (L \ S).card + (S ∩ R).card * (R \ S).card +
        (S ∩ L₂).card * (R₂ \ S).card + (S ∩ R₂).card * (L₂ \ S).card : ℕ)) : ℤ) ≤
        (crossing adj S).card := by exact_mod_cast hcard
    push_cast at hc
    rw [cL, cR, cL2, cR2] at hc
    have : ((2 * h + s - 1 : ℕ) : ℤ) = 2 * h + s - 1 := by omega
    rw [this]; linarith
  exact_mod_cast this

end GHMatrix
