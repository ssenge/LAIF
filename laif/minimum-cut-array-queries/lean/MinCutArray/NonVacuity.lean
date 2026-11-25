import MinCutArray.Main

/-!
# Content of the hypothesis `CountDegree`

`CountDegreeWith c` is a real constraint: it fails for `c = 2`. The witness is the function
`x ↦ [x ≠ 0]` on three bits, a single junta of degree `3`, which separates Hamming weight `2` from
Hamming weight `0`, while `2 √3 > 3`. That `CountDegree` holds for some `c > 0` is the classical
degree bound for exact counting, taken as the hypothesis of `minCut_bound`.
-/

open Finset

namespace MinCutArray

theorem not_countDegreeWith_two : ¬ CountDegreeWith 2 := by
  intro h
  have hJ : IsJuntaSum 3 (fun x : Fin 3 → Bool => if (∑ e, ind (x e)) = 0 then (0 : ℝ) else 1) :=
    ⟨Unit, inferInstance, fun _ => univ, fun _ x => if (∑ e, ind (x e)) = 0 then (0 : ℝ) else 1,
      fun _ => ⟨by simp, fun x y hxy => by
        have : x = y := funext fun i => hxy i (mem_univ i)
        rw [this]⟩, fun x => by simp⟩
  have := h (Fin 3) 1 3 _ le_rfl (by simp) hJ
    (fun x => by split_ifs <;> norm_num)
    (fun x hx => by rw [hx]; norm_num)
    (fun x hx => by
      have : (∑ e, ind (x e)) = 0 := by omega
      rw [this]; norm_num)
  have h3 : Real.sqrt ((Fintype.card (Fin 3) : ℝ) * (1 : ℕ)) = Real.sqrt 3 := by simp
  rw [h3] at this
  have hs : (3 : ℝ) / 2 < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  push_cast at this
  linarith

end MinCutArray
