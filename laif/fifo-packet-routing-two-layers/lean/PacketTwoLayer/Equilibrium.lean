import PacketTwoLayer.Opt
import PacketTwoLayer.Backlog

/-!
# Equilibria are sequential best responses

For a UFR equilibrium `ps` (`eqm_of_UFR`):

* layer 1 is loaded in index order, player `i` reaches `v₁` at `α i = a_{e_i} + #{j < i : e_j = e_i}`, and no edge
  gives her an earlier arrival, so `α i ≤ a_e + #{j < i : e_j = e}` for every edge `e`;
* hence `α` is nondecreasing, layer 2 is loaded in index order, player `i` departs at `max (α i) (NF i f_i)` and
  no edge `f` gives an earlier arrival at the sink, `max (α i) (NF i f_i) + b_{f_i} ≤ max (α i) (NF i f) + b_f`.
-/

namespace PacketTwoLayer

open Finset

theorem times_fst (a b : List ℕ) (ps : List (ℕ × ℕ)) :
    (times a b ps).1 = layer a (List.replicate ps.length 0) (ps.map Prod.fst) := rfl

theorem times_snd (a b : List ℕ) (ps : List (ℕ × ℕ)) :
    (times a b ps).2 = layer b (times a b ps).1 (ps.map Prod.snd) := rfl

theorem replicate_mono (n : ℕ) :
    ∀ i j, i ≤ j → j < (List.replicate n 0).length →
      (List.replicate n 0).getD i 0 ≤ (List.replicate n 0).getD j 0 := by
  intro i j _ _; rw [getD_replicate_zero, getD_replicate_zero]

/-- In layer 1 the next free time of edge `g` after `i` players is the number of them on `g`. -/
theorem NF_layer1 (τ ch : List ℕ) (n : ℕ) (hch : ∀ i < n, ch.getD i 0 < τ.length) :
    ∀ i ≤ n, ∀ g, NF τ (List.replicate n 0) ch i g = cnt (fun j => ch.getD j 0) i g := by
  intro i
  induction i with
  | zero => intro _ g; rw [NF_zero]; simp [cnt]
  | succ i ih =>
    intro hi g
    rw [NF_succ _ _ _ _ _ (hch i (by omega)), cnt_succ, ih (by omega), getD_replicate_zero]
    by_cases h : g = ch.getD i 0
    · rw [if_pos h, if_pos h.symm]; simp
    · rw [if_neg h, if_neg (Ne.symm h)]; simp

/-- Layer-1 arrival of player `i` in any state, when the edges of the players `j < i` are those of `ch`. -/
theorem layer1_getD (τ ch : List ℕ) (n : ℕ) (hch : ∀ j < n, ch.getD j 0 < τ.length) (i : ℕ) (hi : i < n)
    (ch' : List ℕ) (h' : ∀ j < i, ch'.getD j 0 = ch.getD j 0) :
    (layer τ (List.replicate n 0) ch').getD i 0 =
      τ.getD (ch'.getD i 0) 0 + cnt (fun j => ch.getD j 0) i (ch'.getD i 0) := by
  rw [layer_eq_st (replicate_mono n), out_st _ _ _ _ (by simpa using hi),
    getD_replicate_zero]
  unfold NF
  rw [st_congr τ _ ch' ch i h']
  have := NF_layer1 τ ch n hch i hi.le (ch'.getD i 0)
  unfold NF at this
  rw [this]
  simp only [Nat.zero_max]
  omega

theorem map_fst_set (ps : List (ℕ × ℕ)) (i x y : ℕ) :
    (ps.set i (x, y)).map Prod.fst = (ps.map Prod.fst).set i x := by
  rw [List.map_set]

theorem map_snd_set (ps : List (ℕ × ℕ)) (i x y : ℕ) :
    (ps.set i (x, y)).map Prod.snd = (ps.map Prod.snd).set i y := by
  rw [List.map_set]

theorem set_getD_self (l : List ℕ) (i : ℕ) (hi : i < l.length) : l.set i (l.getD i 0) = l := by
  rw [getD_of_lt _ hi, List.set_getElem_self]

/-- A UFR equilibrium has the structure `Eqm`, and the arrival at the sink of player `i` is `βv i`. -/
theorem eqm_of_UFR (a b : List ℕ) (ps : List (ℕ × ℕ)) (hps : ∀ p ∈ ps, p.1 < a.length ∧ p.2 < b.length)
    (h : UFR a b ps) (D : BData) (hDn : D.n = b.length) (hDw : D.w = fun g => b.getD g 0) :
    Eqm ps.length a.length (fun x => a.getD x 0) D (fun i => (ps.map Prod.fst).getD i 0)
        (fun i => (ps.map Prod.snd).getD i 0) (fun i => (times a b ps).1.getD i 0)
        (NF b (times a b ps).1 (ps.map Prod.snd)) ∧
      (times a b ps).1.length = ps.length ∧ (times a b ps).2.length = ps.length ∧
      ∀ i < ps.length, (times a b ps).2.getD i 0 =
        βv D (fun i => (ps.map Prod.snd).getD i 0) (fun i => (times a b ps).1.getD i 0)
          (NF b (times a b ps).1 (ps.map Prod.snd)) i := by
  have hc1 : ∀ i < ps.length, (ps.map Prod.fst).getD i 0 < a.length := fun i hi => (valid_getD hps hi).1
  have hc2 : ∀ i < ps.length, (ps.map Prod.snd).getD i 0 < b.length := fun i hi => (valid_getD hps hi).2
  have hlm : ∀ i < ps.length, i < (ps.map Prod.fst).length := fun i hi => by rw [List.length_map]; exact hi
  have hlm2 : ∀ i < ps.length, i < (ps.map Prod.snd).length := fun i hi => by rw [List.length_map]; exact hi
  -- layer 1
  have hα : ∀ i < ps.length, (times a b ps).1.getD i 0 =
      a.getD ((ps.map Prod.fst).getD i 0) 0 +
        cnt (fun j => (ps.map Prod.fst).getD j 0) i ((ps.map Prod.fst).getD i 0) := by
    intro i hi
    rw [times_fst]
    exact layer1_getD a _ ps.length hc1 i hi _ (fun _ _ => rfl)
  have hαle : ∀ i < ps.length, ∀ x < a.length,
      (times a b ps).1.getD i 0 ≤ a.getD x 0 + cnt (fun j => (ps.map Prod.fst).getD j 0) i x := by
    intro i hi x hx
    have hu := (h i hi x hx ((ps.map Prod.snd).getD i 0) (hc2 i hi)).1
    rw [times_fst a b (ps.set i _), map_fst_set, List.length_set] at hu
    rw [layer1_getD a _ ps.length hc1 i hi ((ps.map Prod.fst).set i x) (fun j hj => by
      rw [getD_set_eq _ _ _ _ (hlm i hi), if_neg (by omega)])] at hu
    rw [getD_set_eq _ _ _ _ (hlm i hi), if_pos rfl] at hu
    exact hu
  have hmono : ∀ i j, i ≤ j → j < ps.length → (times a b ps).1.getD i 0 ≤ (times a b ps).1.getD j 0 :=
    fun i j hij hj => alpha_mono_of (n := ps.length) (nA := a.length) (aF := fun x => a.getD x 0)
      (e := fun i => (ps.map Prod.fst).getD i 0) (α := fun i => (times a b ps).1.getD i 0) hc1 hα hαle hij hj
  have hlt1 : (times a b ps).1.length = ps.length := by
    rw [times_fst, layer_eq_st (replicate_mono _), (st_length _ _ _ _).2, List.length_replicate]
  have hmono' : ∀ i j, i ≤ j → j < (times a b ps).1.length →
      (times a b ps).1.getD i 0 ≤ (times a b ps).1.getD j 0 :=
    fun i j hij hj => hmono i j hij (by omega)
  -- layer 2
  have ht2 : (times a b ps).2 = (st b (times a b ps).1 (ps.map Prod.snd) ps.length).2 := by
    rw [times_snd, layer_eq_st hmono', hlt1]
  have hlt2 : (times a b ps).2.length = ps.length := by rw [ht2, (st_length _ _ _ _).2, hlt1]
  have hβ : ∀ i < ps.length, (times a b ps).2.getD i 0 =
      max ((times a b ps).1.getD i 0)
        (NF b (times a b ps).1 (ps.map Prod.snd) i ((ps.map Prod.snd).getD i 0)) +
        b.getD ((ps.map Prod.snd).getD i 0) 0 := by
    intro i hi
    rw [ht2, show ps.length = (times a b ps).1.length from hlt1.symm, out_st _ _ _ _ (by omega)]
  refine ⟨⟨hc1, ?_, hα, hαle, fun g => NF_zero _ _ _ g, ?_, ?_⟩, hlt1, hlt2, ?_⟩
  · intro i hi; rw [hDn]; exact hc2 i hi
  · intro i hi g
    exact NF_succ _ _ _ _ _ (hc2 i hi)
  · intro i hi g hg
    simp only [hDw]
    rw [hDn] at hg
    have hu := (h i hi ((ps.map Prod.fst).getD i 0) (hc1 i hi) g hg).2
    rw [← hβ i hi]
    have hset : (ps.set i ((ps.map Prod.fst).getD i 0, g)).map Prod.fst = ps.map Prod.fst := by
      rw [map_fst_set, set_getD_self _ _ (hlm i hi)]
    have ht1' : (times a b (ps.set i ((ps.map Prod.fst).getD i 0, g))).1 = (times a b ps).1 := by
      rw [times_fst, times_fst, hset, List.length_set]
    rw [times_snd a b (ps.set i _), ht1', map_snd_set, layer_eq_st hmono', out_st _ _ _ _ (by omega)] at hu
    rw [getD_set_eq _ _ _ _ (hlm2 i hi), if_pos rfl] at hu
    unfold NF at hu
    rw [st_congr b (times a b ps).1 ((ps.map Prod.snd).set i g) (ps.map Prod.snd) i (fun j hj => by
      rw [getD_set_eq _ _ _ _ (hlm2 i hi), if_neg (by omega)])] at hu
    exact hu
  · intro i hi
    rw [hβ i hi]
    unfold βv
    simp only [hDw]

end PacketTwoLayer
