import SsspFlow.GHatLevelLocal

/-!
# The lists of Table R from local data

Every dart `d` of the network carries a record of five bits (`RData.dinfo`): whether it is incised,
whether its corner is cut, the mode of that corner, the host bit, and whether the tail corner of `d` is
a cut corner in mode R. The tail of `d` computes the record of `d` from its own data. The lists of
Table R at the copies of a corner `c = (w, u)`, read as names, depend only on the rotation list of
`w`, the records of the darts at `w` and the records of the darts into `w` (`RData.dList_raw` and the
others). So a node knows these lists after one round in which every node sends every neighbour the
record of the dart to it.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest

namespace RotSystem

/-- The record of a dart. -/
structure DInfo where
  inc : Bool
  cut : Bool
  modeL : Bool
  hostT : Bool
  optR : Bool
  deriving DecidableEq, Inhabited

namespace DInfo

/-- The corner is cut in mode L. -/
def movA (i : DInfo) : Bool := i.cut && i.modeL

/-- The corner is cut in mode R. -/
def movB (i : DInfo) : Bool := i.cut && !i.modeL

end DInfo

/-- The kind of the forward name of a token. -/
def kF : Lab → Fin 21
  | .zero => 5
  | .one => 6
  | .two => 7

/-- The kind of the backward name of a token. -/
def kB : Lab → Fin 21
  | .zero => 8
  | .one => 9
  | .two => 10

section Raw

variable {n : ℕ}

/-- The raw entry of the in-token at `D(c)`. -/
def rawEntA (f : Fin n → DInfo) (w u : Fin n) (l : Lab) : Fin n × Fin n × Fin 21 :=
  if (f u).movA then (w, u, 19) else (w, u, kB l)

/-- The raw entry of the out-token at `D(c)`. -/
def rawEntB (f : Fin n → DInfo) (w u nx : Fin n) (l : Lab) : Fin n × Fin n × Fin 21 :=
  if (f u).movB then (w, u, 19) else (w, nx, kF l)

def rawSegA (f g : Fin n → DInfo) (w u : Fin n) : List (Fin n × Fin n × Fin 21) :=
  if (f u).inc then
    if (g u).optR then [(w, u, 15), rawEntA f w u .two] else [rawEntA f w u .two, (w, u, 15)]
  else [rawEntA f w u .zero]

def rawSegB (f : Fin n → DInfo) (w u nx : Fin n) : List (Fin n × Fin n × Fin 21) :=
  if (f nx).inc then
    if (f u).movB then [(w, nx, 17), rawEntB f w u nx .one] else [rawEntB f w u nx .one, (w, nx, 17)]
  else [rawEntB f w u nx .zero]

/-- The raw list at `D(c)` for the corner `c = (w, u)` with next neighbour `nx`. -/
def rawDList (f g : Fin n → DInfo) (w u nx : Fin n) : List (Fin n × Fin n × Fin 21) :=
  [(w, u, 12)] ++ (if (f u).movA then [] else [(w, u, 14)]) ++ rawSegA f g w u ++ rawSegB f w u nx ++
    (if (f u).movB then [] else [(w, nx, 13)])

/-- The raw list at `L(c)`. -/
def rawLList (f : Fin n → DInfo) (w u : Fin n) : List (Fin n × Fin n × Fin 21) :=
  if (f u).inc then [(w, u, 16), (w, u, 9)] else []

/-- The raw list at `R(c)`. -/
def rawRList (f : Fin n → DInfo) (w nx : Fin n) : List (Fin n × Fin n × Fin 21) :=
  if (f nx).inc then [(w, nx, 18), (w, nx, 7)] else []

/-- The raw list at `X(c)`. -/
def rawXList (f : Fin n → DInfo) (w u nx : Fin n) : List (Fin n × Fin n × Fin 21) :=
  if (f u).cut then
    if (f u).modeL then [(w, u, 20), (w, u, 14), (w, u, if (f u).inc then 10 else 8)]
    else [(w, u, 20), (w, nx, if (f nx).inc then 6 else 5), (w, nx, 13)]
  else []

end Raw

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData)

/-- The record of a dart. -/
def dinfo (d : N.G.Dart) : DInfo :=
  ⟨decide (d ∈ S.inc), decide (d ∈ S.cut), S.modeL d, S.hostT d, decide (S.MovB (N.toRot.tailCorner d))⟩

/-- The record of the dart `(w, u)`, default if there is none. -/
def dinfoAt (w u : Fin n) : DInfo := if h : N.G.Adj w u then S.dinfo ⟨(w, u), h⟩ else default

theorem dinfoAt_dart (d : N.G.Dart) : S.dinfoAt d.fst d.snd = S.dinfo d := by
  unfold dinfoAt
  rw [dite_cond_eq_true (eq_true d.adj)]

theorem dinfoAt_symm (d : N.G.Dart) : S.dinfoAt d.snd d.fst = S.dinfo d.symm := S.dinfoAt_dart d.symm

theorem movA_dinfo (d : N.G.Dart) : (S.dinfo d).movA = decide (S.MovA d) := by
  simp [dinfo, DInfo.movA, MovA]

theorem movB_dinfo (d : N.G.Dart) : (S.dinfo d).movB = decide (S.MovB d) := by
  simp [dinfo, DInfo.movB, MovB]

/-- **The list at `D(c)` from local data.** The next neighbour `(rot c).snd` is the successor of
`c.snd` in the rotation list of `c.fst`. -/
theorem dList_raw (c : N.G.Dart) :
    (S.dList c).map S.nameD =
      rawDList (S.dinfoAt c.fst) (fun u => S.dinfoAt u c.fst) c.fst c.snd (N.toRot.rot c).snd := by
  have hr : S.dinfoAt c.fst (N.toRot.rot c).snd = S.dinfo (N.toRot.rot c) :=
    S.dinfoAt_dart (N.toRot.rot c)
  have hs := S.dinfoAt_symm c
  have hc := S.dinfoAt_dart c
  have hinc : N.toRot.rev c ∈ S.inc ↔ c ∈ S.inc := S.inc_rev c
  unfold dList segA segB entA entB rawDList rawSegA rawSegB rawEntA rawEntB
  simp only [hr, hs, hc, movA_dinfo, movB_dinfo]
  by_cases h1 : c ∈ S.inc <;> by_cases h2 : S.MovA c <;> by_cases h3 : S.MovB c <;>
    by_cases h4 : N.toRot.rot c ∈ S.inc <;> by_cases h5 : S.Opt (N.toRot.rev c) <;>
    simp_all [dinfo, Opt, nameD, kB, kF, fw, bw]

/-- **The list at `L(c)` from local data.** -/
theorem lList_raw (c : N.G.Dart) : (S.lList c).map S.nameD = rawLList (S.dinfoAt c.fst) c.fst c.snd := by
  have hc := S.dinfoAt_dart c
  have hinc : N.toRot.rev c ∈ S.inc ↔ c ∈ S.inc := S.inc_rev c
  unfold lList rawLList
  simp only [hc]
  by_cases h1 : c ∈ S.inc <;> simp_all [dinfo, nameD, fw, bw]

/-- **The list at `R(c)` from local data.** -/
theorem rList_raw (c : N.G.Dart) :
    (S.rList c).map S.nameD = rawRList (S.dinfoAt c.fst) c.fst (N.toRot.rot c).snd := by
  have hr : S.dinfoAt c.fst (N.toRot.rot c).snd = S.dinfo (N.toRot.rot c) :=
    S.dinfoAt_dart (N.toRot.rot c)
  unfold rList rawRList
  simp only [hr]
  by_cases h4 : N.toRot.rot c ∈ S.inc <;> simp_all [dinfo, nameD, fw, bw]

/-- **The list at `X(c)` from local data.** -/
theorem xList_raw (c : N.G.Dart) :
    (S.xList c).map S.nameD = rawXList (S.dinfoAt c.fst) c.fst c.snd (N.toRot.rot c).snd := by
  have hr : S.dinfoAt c.fst (N.toRot.rot c).snd = S.dinfo (N.toRot.rot c) :=
    S.dinfoAt_dart (N.toRot.rot c)
  have hc := S.dinfoAt_dart c
  have hinc : N.toRot.rev c ∈ S.inc ↔ c ∈ S.inc := S.inc_rev c
  unfold xList rawXList
  simp only [hr, hc]
  by_cases h0 : c ∈ S.cut <;> by_cases hm : S.modeL c = true <;> by_cases h1 : c ∈ S.inc <;>
    by_cases h4 : N.toRot.rot c ∈ S.inc <;>
    simp_all [dinfo, nameD, fw, bw, lastLab, firstLab]

/-- Lists without repeats, with the same entries and the same cycle, are rotations of each other. -/
theorem _root_.List.isRotated_of_formPerm {α : Type*} [DecidableEq α] {l l' : List α} (hl : l.Nodup)
    (hl' : l'.Nodup) (hm : ∀ x, x ∈ l ↔ x ∈ l') (hf : l.formPerm = l'.formPerm) : l ~r l' := by
  have hp : l.Perm l' := (List.perm_ext_iff_of_nodup hl hl').2 hm
  rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
  · rw [← hp.nil_eq]
  · rw [List.singleton_perm.1 hp]
  · rcases l' with _ | ⟨x', _ | ⟨y', t'⟩⟩
    · exact absurd hp.length_eq (by simp)
    · exact absurd hp.length_eq (by simp)
    · exact (List.formPerm_ext_iff hl hl').1 hf

/-- **The list at a star centre from local data**, up to rotation: the darts at the node in rotation
order. -/
theorem starList_raw (d : N.G.Dart) :
    (N.toRot.starList (N.toRot.tail d)).map (fun c : N.G.Dart => c.toProd) ~r
      (N.rotList d.fst).map (Prod.mk d.fst) := by
  have hinj : Function.Injective (fun c : N.G.Dart => c.toProd) := fun a b h => SimpleGraph.Dart.ext _ _ h
  have hmem : ∀ c : N.G.Dart, c ∈ N.toRot.starList (N.toRot.tail d) ↔ c.fst = d.fst := fun c =>
    mem_starList.trans N.tail_eq_iff
  have hmem' : ∀ p : Fin n × Fin n, p ∈ (N.toRot.starList (N.toRot.tail d)).map (fun c => c.toProd) ↔
      p ∈ (N.rotList d.fst).map (Prod.mk d.fst) := by
    intro p
    constructor
    · intro h
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
      have hcf := (hmem c).1 hc
      exact List.mem_map.2 ⟨c.snd, by rw [← hcf]; exact (N.mem_rotList _ _).2 c.adj, Prod.ext hcf.symm rfl⟩
    · intro h
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 h
      exact List.mem_map.2 ⟨⟨(d.fst, u), (N.mem_rotList _ _).1 hu⟩, (hmem _).2 rfl, rfl⟩
  refine List.isRotated_of_formPerm ((starList_nodup _).map hinj)
    ((N.nodup _).map (Prod.mk_right_injective d.fst)) hmem' (Equiv.ext fun p => ?_)
  by_cases hp : p ∈ (N.toRot.starList (N.toRot.tail d)).map (fun c => c.toProd)
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
    have hcf : c.fst = d.fst := (hmem c).1 hc
    rw [formPerm_map_apply hinj (starList_nodup _) hc, formPerm_starList hc]
    have hcs : c.snd ∈ N.rotList d.fst := hcf ▸ (N.mem_rotList _ _).2 c.adj
    have e : c.toProd = (d.fst, c.snd) := Prod.ext hcf rfl
    rw [e, formPerm_map_apply (Prod.mk_right_injective d.fst) (N.nodup _) hcs]
    exact Prod.ext hcf (by rw [← hcf]; rfl)
  · rw [List.formPerm_apply_of_notMem hp, List.formPerm_apply_of_notMem (fun h => hp ((hmem' p).2 h))]

end RData

end RotSystem

end SsspFlow
