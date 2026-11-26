import VertexConn.Basic

/-!
# Content of the statements

* On the path 0 - 1 - 2 - 3 with `U = L = {0, 1}`, the hypotheses of `twin_bound` hold: `L` has the
  smallest neighbourhood among the nonempty subsets of `U`.
* In the star with centre 0 and leaves 1, ..., 5, the set `{0, 1}` is not minimal (`{1}` has a smaller
  neighbourhood) and `|N 0 △ N 1| = 6 > 2 · |{0, 1}|`, so the conclusion fails without the minimality
  hypothesis.
* In `cluster_card` the term `a_C` can be positive.
-/

namespace VertexConn

/-- The path 0 - 1 - 2 - 3. -/
def pathN : Fin 4 → Finset (Fin 4)
  | 0 => {1} | 1 => {0, 2} | 2 => {1, 3} | 3 => {2}

/-- The hypotheses of `twin_bound` are satisfiable: on the path, `L = {0, 1} ⊆ U = {0, 1}` has the
smallest neighbourhood among the nonempty subsets of `U`. -/
example : (∀ v, v ∉ pathN v) ∧
    (∀ L' ∈ ({0, 1} : Finset (Fin 4)).powerset, L'.Nonempty →
      (nbhd pathN {0, 1}).card ≤ (nbhd pathN L').card) ∧
    (sdiffs (pathN 0) (pathN 1)).card = 3 := by
  refine ⟨by decide, by decide, by decide⟩

/-- The star with centre 0 and leaves 1, ..., 5. -/
def starN : Fin 6 → Finset (Fin 6)
  | 0 => {1, 2, 3, 4, 5} | _ => {0}

/-- Without minimality the twin bound fails: `|N 0 △ N 1| = 6 > 2 · |{0, 1}|`, while `{1}` has a
smaller neighbourhood than `{0, 1}`. -/
example : (sdiffs (starN 0) (starN 1)).card > 2 * ({0, 1} : Finset (Fin 6)).card ∧ (nbhd starN {1}).card < (nbhd starN {0, 1}).card := by
  decide

/-- The triangle 0 - 1 - 2 with the edge 1 - 3. -/
def triN : Fin 4 → Finset (Fin 4)
  | 0 => {1, 2} | 1 => {0, 2, 3} | 2 => {0, 1} | 3 => {1}

/-- With `C = {0}` the set `D` is empty and `a_C = |{1, 2}| = 2`. -/
example : (triN 0 \ (({0} : Finset (Fin 4)).biUnion (fun v => sdiffs (triN 0) (triN v)) ∪ {0})).card = 2 := by
  decide

end VertexConn
