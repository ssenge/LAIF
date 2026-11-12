import SsspFlow.OracleTree
import SsspFlow.OracleChoice
import SsspFlow.GHatLevelLen

/-!
# Marking shortest walks with three calls

On a planar network, the algorithm `markAlg` runs the exact shortest-path oracle, then one round in
which every node tells its parent that it is its child, then the oracle again with length `0` on the
arc from each node to its parent and offset `0` at the targets. A node is a target if its input flag
is set.

* `Net.ExactSpec.dsrcTop_markB`: in the second run, the distance is `0` exactly on the parent chains of
  the targets and `⊤` elsewhere.
* `markAlg_spec`: assuming the Exact SSSP bound, after `2 C log^c n · D + 1` rounds the outputs of
  both runs meet the specification of the oracle. So every node knows its distance, its parent, and
  whether it lies on the parent chain of a target.
-/

set_option autoImplicit false

namespace SsspFlow

namespace Congest

open Cslib.Congest Cslib.Congest.Algorithm
open scoped ENNReal

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The offsets of the marking run for a set of targets: `0` at a target, `⊤` elsewhere. -/
def Net.markOffB (isT : V → Bool) (a : V) : ℕ∞ := if isT a then 0 else ⊤

open Classical in
/-- **The marking run, several targets.** The distance is `0` on the parent chains of the targets and
`⊤` elsewhere. -/
theorem Net.ExactSpec.dsrcTop_markB {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) (isT : V → Bool) (x : V) :
    N.dsrcTop (Net.markLen r) (Net.markOffB isT) x =
      if ∃ t i, isT t = true ∧ (Net.parOf r)^[i] t = x then (0 : ℝ≥0∞) else ⊤ := by
  unfold Net.dsrcTop dsrc
  split_ifs with hx
  · obtain ⟨t, i, ht, rfl⟩ := hx
    obtain ⟨p, hp⟩ := h.walk_par i t
    refine le_antisymm (iInf_le_of_le t ?_) zero_le
    have h0 : offTop (Net.markOffB isT) t = 0 := by simp [offTop, Net.markOffB, ht]
    rw [h0, zero_add]
    unfold dist
    exact iInf₂_le_of_le p (fun _ _ => Set.mem_univ _) hp.le
  · refine top_le_iff.1 (le_iInf fun a => ?_)
    by_cases ha : isT a = true
    · unfold dist
      refine le_trans (le_iInf₂ fun p _ => ?_) le_add_self
      by_contra hc
      obtain ⟨i, hi⟩ := Net.mark_closed (t := a) p (ne_top_of_lt (not_le.1 hc)) ⟨0, rfl⟩
      exact hx ⟨a, i, ha, hi⟩
    · simp [offTop, Net.markOffB, ha]

/-- The input of the marking run at `v`, from its input, its output of the first run and the numbers
received from its neighbours. -/
def markIn (j : OracleIn V × Bool) (par : Option V) (rc : V → Option ℕ) : OracleIn V where
  nbrs := j.1.nbrs
  lenOut u := if u ∈ j.1.nbrs then (if par = some u then 0 else ⊤) else ⊤
  lenIn u := if u ∈ j.1.nbrs then (if rc u = some 1 then 0 else ⊤) else ⊤
  offset := if j.2 then 0 else ⊤

/-- The number a node with parent `par` sends to `b`: `1` if `b` is its parent. -/
def childMsg (par : Option V) (b : V) : ℕ := if par = some b then 1 else 0

/-- The marking algorithm: the oracle `A`, one round of child messages, and the oracle again. -/
noncomputable def markAlg {σ : Type} {B : ℕ} (A : Algorithm V (OracleIn V) σ B) (out : V → σ → ℕ∞ × Option V)
    (T : ℕ) :
    Algorithm V (OracleIn V × Bool)
      ((ℕ × ((OracleIn V × Bool) × σ)) ⊕ ((ℕ × (((OracleIn V × Bool) × σ) × ((V → ℕ) × (V → Option ℕ)))) ⊕
        ((((OracleIn V × Bool) × σ) × ((V → ℕ) × (V → Option ℕ))) × σ))) (B + 1) :=
  ((A.widen (Nat.le_add_right B 1)).keep (fun _ (j : OracleIn V × Bool) => j.1)).seq T (fun _ s => s)
    (((exchTo V (B + 1)).keep (fun v (p : (OracleIn V × Bool) × σ) => childMsg (out v p.2).2)).seq 1
      (fun _ s => s)
      ((A.widen (Nat.le_add_right B 1)).keep
        (fun v (q : ((OracleIn V × Bool) × σ) × ((V → ℕ) × (V → Option ℕ))) =>
          markIn q.1.1 (out v q.1.2).2 q.2.2)))

/-- The output of the first run, read from a state of `markAlg`. -/
def markFirst {σ : Type} (out : V → σ → ℕ∞ × Option V) (v : V) :
    ((ℕ × ((OracleIn V × Bool) × σ)) ⊕ ((ℕ × (((OracleIn V × Bool) × σ) × ((V → ℕ) × (V → Option ℕ)))) ⊕
      ((((OracleIn V × Bool) × σ) × ((V → ℕ) × (V → Option ℕ))) × σ))) → ℕ∞ × Option V
  | .inr (.inr (q, _)) => out v q.1.2
  | _ => (⊤, none)

/-- The output of the marking run, read from a state of `markAlg`. -/
def markSecond {σ : Type} (out : V → σ → ℕ∞ × Option V) (v : V) :
    ((ℕ × ((OracleIn V × Bool) × σ)) ⊕ ((ℕ × (((OracleIn V × Bool) × σ) × ((V → ℕ) × (V → Option ℕ)))) ⊕
      ((((OracleIn V × Bool) × σ) × ((V → ℕ) × (V → Option ℕ))) × σ))) → ℕ∞ × Option V
  | .inr (.inr (_, s)) => out v s
  | _ => (⊤, none)

theorem markIn_eq (N : Net V) (ℓ : V → V → ℕ∞) (φ : V → ℕ∞) (isT : V → Bool) (r : V → ℕ∞ × Option V)
    (v : V) :
    markIn (N.oracleIn ℓ φ v, isT v) (r v).2
        (fun u => if N.G.Adj u v then some (childMsg (r u).2 v) else none) =
      N.oracleIn (Net.markLen r) (Net.markOffB isT) v := by
  unfold markIn Net.oracleIn Net.markLen Net.markOffB childMsg
  congr 1
  · funext u
    simp only [N.mem_rotList]
  · funext u
    simp only [N.mem_rotList]
    by_cases h : N.G.Adj v u
    · have h' : N.G.Adj u v := h.symm
      by_cases hp : (r u).2 = some v <;> simp [h, h', hp]
    · simp [h]

/-- **Marking with three calls.** Assuming the Exact SSSP bound, after `2 C log^c n · D + 1` rounds the
outputs of the first run and of the marking run meet the specification of the oracle, for the chosen
oracle of the bound. The first run gives the outputs of that oracle. -/
theorem markAlg_spec (hE : ExactSsspBound) (K n D : ℕ) (hD : 1 ≤ D)
    (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ∞) (φ : Fin n → ℕ∞) (isT : Fin n → Bool)
    (hP : N.toRot.Planar) (hDi : N.DiamLE D) (hval : OracleValid N 0 ((n + 2) ^ K) ℓ φ) :
    let st := (markAlg (hE.alg K n D hD) (hE.out K n D hD) (hE.cC K * logN n ^ hE.cc K * D)).run N.G
      (fun v => (N.oracleIn ℓ φ v, isT v)) (hE.cC K * logN n ^ hE.cc K * D + (1 + hE.cC K * logN n ^ hE.cc K * D))
    N.ExactSpec ℓ φ (fun v => markFirst (hE.out K n D hD) v (st v)) ∧
      N.ExactSpec (Net.markLen fun v => markFirst (hE.out K n D hD) v (st v)) (Net.markOffB isT)
        (fun v => markSecond (hE.out K n D hD) v (st v)) ∧
      (fun v => markFirst (hE.out K n D hD) v (st v)) = hE.oracleRun K D hD N ℓ φ := by
  set C := hE.cC K
  set c := hE.cc K
  set A := hE.alg K n D hD
  set out := hE.out K n D hD
  have hA : ∀ (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ∞) (φ : Fin n → ℕ∞),
      N.toRot.Planar → N.DiamLE D → OracleValid N 0 ((n + 2) ^ K) ℓ φ →
      N.ExactSpec ℓ φ (fun v => out v (A.run N.G (N.oracleIn ℓ φ) (C * logN n ^ c * D) v)) :=
    fun N ℓ φ hP hDi hval => hE.alg_spec K n D hD N ℓ φ hP hDi hval
  set T := C * logN n ^ c * D
  set r : Fin n → ℕ∞ × Option (Fin n) := fun v => out v (A.run N.G (N.oracleIn ℓ φ) T v) with hr
  have hmsg : ∀ u w, childMsg (r u).2 w < 2 ^ (C * logN n ^ c + 1) := fun u w => by
    have : childMsg (r u).2 w ≤ 1 := by unfold childMsg; split_ifs <;> omega
    have : 2 ≤ 2 ^ (C * logN n ^ c + 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hrun : (markAlg A out T).run N.G (fun v => (N.oracleIn ℓ φ v, isT v)) (T + (1 + T)) = fun v =>
      .inr (.inr ((((N.oracleIn ℓ φ v, isT v), A.run N.G (N.oracleIn ℓ φ) T v),
        (fun b => childMsg (r v).2 b, fun u => if N.G.Adj u v then some (childMsg (r u).2 v) else none)),
        A.run N.G (N.oracleIn (Net.markLen r) (Net.markOffB isT)) T v)) := by
    funext v
    unfold markAlg
    rw [run_seq, run_seq]
    simp only [run_keep, run_widen]
    have hex : ∀ w, (exchTo (Fin n) (hE.cC K * logN n ^ hE.cc K + 1)).run N.G
        (fun w => childMsg (out w (A.run N.G (fun v => (N.oracleIn ℓ φ v, isT v).1) T w)).2) 1 w =
        (fun b => childMsg (r w).2 b, fun u => if N.G.Adj u w then some (childMsg (r u).2 w) else none) :=
      fun w => run_exchTo N.G _ hmsg w
    simp only [hex]
    congr 3
    congr 1
    funext w
    exact markIn_eq N ℓ φ isT r w
  simp only [hrun, markFirst, markSecond]
  have h1 := hA N ℓ φ hP hDi hval
  refine ⟨h1, hA N (Net.markLen r) (Net.markOffB isT) hP hDi ⟨fun u v _ => ?_, fun z => ?_⟩, rfl⟩
  · unfold Net.markLen
    split_ifs
    · exact .inr ⟨le_rfl, zero_le⟩
    · exact .inl rfl
  · unfold Net.markOffB
    split_ifs
    · exact .inr zero_le
    · exact .inl rfl

end Congest

end SsspFlow
