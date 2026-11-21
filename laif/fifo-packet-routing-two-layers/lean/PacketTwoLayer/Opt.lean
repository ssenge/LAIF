import PacketTwoLayer.Loading

/-!
# The cut bound for every state

`cutVal nA aF nB bF T Y = ∑_e (Y - a_e)⁺ + ∑_f (T + 1 - Y - b_f)⁺`. In every state with makespan `T`, a packet
either reaches `v₁` before time `Y`, at most `(Y - a_e)⁺` of them over edge `e`, or reaches `v₁` at time `Y` or
later and then leaves `v₁` over some edge `f` at a time in `[Y, T - b_f]`, at most `(T + 1 - Y - b_f)⁺` of them.
So the number of players is at most `cutVal` for every `Y` (`opt_cut`).
-/

namespace PacketTwoLayer

open Finset

/-- The cut value. -/
def cutVal (nA : ℕ) (aF : ℕ → ℕ) (nB : ℕ) (bF : ℕ → ℕ) (T Y : ℕ) : ℕ :=
  ∑ x ∈ range nA, (Y - aF x) + ∑ g ∈ range nB, (T + 1 - Y - bF g)

theorem valid_getD {a b : List ℕ} {ps : List (ℕ × ℕ)} (hps : ∀ p ∈ ps, p.1 < a.length ∧ p.2 < b.length)
    {i : ℕ} (hi : i < ps.length) :
    (ps.map Prod.fst).getD i 0 < a.length ∧ (ps.map Prod.snd).getD i 0 < b.length := by
  rw [getD_of_lt _ (by simpa using hi), getD_of_lt _ (by simpa using hi)]
  simp only [List.getElem_map]
  exact hps _ (List.getElem_mem hi)

/-- The number of players is at most the cut value of the makespan, for every `Y`. -/
theorem opt_cut (a b : List ℕ) (qs : List (ℕ × ℕ)) (hqs : ∀ p ∈ qs, p.1 < a.length ∧ p.2 < b.length)
    (Y : ℕ) :
    qs.length ≤ cutVal a.length (fun x => a.getD x 0) b.length (fun g => b.getD g 0) (makespan a b qs) Y := by
  set n := qs.length with hn
  set ch1 := qs.map Prod.fst with hch1
  set ch2 := qs.map Prod.snd with hch2
  set arr0 := List.replicate n 0 with harr0
  set t1 := layer a arr0 ch1 with ht1
  set t2 := layer b t1 ch2 with ht2
  set T := makespan a b qs with hT
  have hT' : T = t2.foldl max 0 := rfl
  have harr0l : arr0.length = n := by simp [harr0]
  have hc1 : ∀ i < arr0.length, ch1.getD i 0 < a.length := fun i hi =>
    (valid_getD hqs (by omega)).1
  have hlen1 : t1.length = n := by rw [ht1, layer_length a arr0 ch1 hc1, harr0l]
  have hc2 : ∀ i < t1.length, ch2.getD i 0 < b.length := fun i hi =>
    (valid_getD hqs (by omega)).2
  have hA : ∀ i < n, a.getD (ch1.getD i 0) 0 ≤ t1.getD i 0 := by
    intro i hi
    have := layer_lower hc1 (show i < arr0.length by omega)
    rw [harr0, getD_replicate_zero, zero_add] at this
    exact this
  have hAne : ∀ i < n, ∀ j < n, i ≠ j → ch1.getD i 0 = ch1.getD j 0 → t1.getD i 0 ≠ t1.getD j 0 :=
    fun i hi j hj hij he => layer_ne hc1 (by omega) (by omega) hij he
  have hB : ∀ i < n, t1.getD i 0 + b.getD (ch2.getD i 0) 0 ≤ t2.getD i 0 :=
    fun i hi => layer_lower hc2 (by omega)
  have hBne : ∀ i < n, ∀ j < n, i ≠ j → ch2.getD i 0 = ch2.getD j 0 → t2.getD i 0 ≠ t2.getD j 0 :=
    fun i hi j hj hij he => layer_ne hc2 (by omega) (by omega) hij he
  have hBT : ∀ i, t2.getD i 0 ≤ T := fun i => by rw [hT']; exact getD_le_foldl_max t2 i
  unfold cutVal
  have hsplit := Finset.card_filter_add_card_filter_not (s := range n) (fun i => t1.getD i 0 < Y)
  rw [Finset.card_range] at hsplit
  rw [← hsplit]
  apply add_le_add
  · rw [Finset.card_eq_sum_card_fiberwise (f := fun i => ch1.getD i 0) (t := range a.length) ?_]
    · apply Finset.sum_le_sum
      intro x _
      rw [Finset.filter_filter]
      calc _ ≤ (Ico (a.getD x 0) Y).card := by
            apply Finset.card_le_card_of_injOn (fun i => t1.getD i 0)
            · intro i hi
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
              simp only [Finset.mem_coe, Finset.mem_Ico]
              have := hA i hi.1
              rw [hi.2.2] at this
              exact ⟨this, hi.2.1⟩
            · intro i hi j hj hij
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi hj
              by_contra hne
              exact hAne i hi.1 j hj.1 hne (by rw [hi.2.2, hj.2.2]) hij
        _ = Y - a.getD x 0 := Nat.card_Ico _ _
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi ⊢
      exact (valid_getD hqs hi.1).1
  · rw [Finset.card_eq_sum_card_fiberwise (f := fun i => ch2.getD i 0) (t := range b.length) ?_]
    · apply Finset.sum_le_sum
      intro g _
      rw [Finset.filter_filter]
      calc _ ≤ (Ico (Y + b.getD g 0) (T + 1)).card := by
            apply Finset.card_le_card_of_injOn (fun i => t2.getD i 0)
            · intro i hi
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
              simp only [Finset.mem_coe, Finset.mem_Ico]
              have h1 := hB i hi.1
              rw [hi.2.2] at h1
              have h2 := hBT i
              constructor <;> omega
            · intro i hi j hj hij
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi hj
              by_contra hne
              exact hBne i hi.1 j hj.1 hne (by rw [hi.2.2, hj.2.2]) hij
        _ = T + 1 - Y - b.getD g 0 := by rw [Nat.card_Ico]; omega
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi ⊢
      exact (valid_getD hqs hi.1).2

end PacketTwoLayer
