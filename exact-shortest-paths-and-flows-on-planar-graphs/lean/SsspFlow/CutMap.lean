import Mathlib.GroupTheory.Perm.Cycle.Basic
import SsspFlow.Separation
import SsspFlow.Disks

/-!
# The cut of a planar map along a path

The level-one annulus `A_1` of Theorem D as a planar map. `R` is the dual map `G*`, and a
`CutPath` is a path `P = p_0 … p_m` of `R` through pairwise distinct vertices, with darts
`e t` from `p_t` to `p_{t+1}`, together with a corner `cs` at `p_0` and a corner `ct` at `p_m`
on two different faces: the slit of the cut enters through them.

The cut doubles every edge (`RotSystem.double`) and splits the doubled map at the set `Γ` of
`2(m + 1)` corners `k σ t`: the digon corners `(e t, false)` and `(rev (e t), false)` of the edges
of `P`, and the two end corners `(cs, true)` and `(ct, true)`. At each `p_t` there are exactly two
corners of `Γ`, `k 0 t` and `k 1 t`, so the split separates `p_t` into the two copies `p_t^0` and
`p_t^1`.

* `nodeReturn_k`: the first return of the rotation swaps `k 0 t` and `k 1 t`.
* `faceReturn_k0`, `faceReturn_k1`: the first return of the faces swaps the two corners of each
  digon and fixes the two end corners.
* `psi_eq`: so `ψ` is the cycle `p_0^0, …, p_m^0, p_m^1, …, p_0^1` of `copyCorners`.
* `faceDrawn`: for planar connected `R`, the cut `R.double.split Γ` is planar, and the copies are
  corners of one face in this cyclic order, at distinct vertices.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor

/-- The first return of `f` to `S` from `x` is `y` when `x` and `y` are the only points of `S` on
their orbit. -/
theorem firstReturn_eq_of_pair {α : Type*} [Fintype α] [DecidableEq α] {f : Equiv.Perm α}
    {S : Finset α} {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) (hc : fconnect f x y)
    (h : ∀ z ∈ S, fconnect f x z → z = x ∨ z = y) : firstReturn f S x = y := by
  rcases h _ ((firstReturn_mem_iff f S x).2 hx) (fconnect_firstReturn f S x) with e | e
  · have hc' := (fconnect_firstReturn_iff f hx hy).2 hc
    obtain ⟨n, hn⟩ := fconnect_iff_iterate.1 hc'
    rw [Function.iterate_fixed e] at hn
    exact absurd hn hxy
  · exact e

/-- The first return of `f` to `S` fixes `x` when `x` is the only point of `S` on its orbit. -/
theorem firstReturn_eq_self_of {α : Type*} [Fintype α] [DecidableEq α] {f : Equiv.Perm α}
    {S : Finset α} {x : α} (hx : x ∈ S) (h : ∀ z ∈ S, fconnect f x z → z = x) :
    firstReturn f S x = x :=
  h _ ((firstReturn_mem_iff f S x).2 hx) (fconnect_firstReturn f S x)

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] (R : RotSystem D)

/-- Darts at one vertex of the doubled map come from darts at one vertex. -/
theorem fconnect_of_double {z z' : D × Bool} (h : fconnect R.double.rot z z') :
    fconnect R.rot z.1 z'.1 := by
  induction h with
  | refl => exact connect_refl _
  | @tail a c _ hac ih =>
    obtain rfl : R.double.rot a = c := hac
    obtain ⟨d, _ | _⟩ := a
    · exact ih
    · exact connect_trans ih (fconnect1 _ d)

/-- The face of a corner `(d, false)` of the doubled map is the digon of the edge of `d`. -/
theorem mem_digon {d : D} {z : D × Bool} (h : fconnect R.double.facePerm (d, false) z) :
    z = (d, false) ∨ z = (R.rev d, false) := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail a c _ hac ih =>
    obtain rfl : R.double.facePerm a = c := hac
    rcases ih with rfl | rfl
    · exact Or.inr (R.double_face_false d)
    · left
      rw [R.double_face_false, R.rev_rev]

/-- The face of a corner `(d, true)` of the doubled map is a copy of the face of `d`. -/
theorem mem_face_true {d : D} {z : D × Bool} (h : fconnect R.double.facePerm (d, true) z) :
    z.2 = true ∧ fconnect R.facePerm d z.1 := by
  induction h with
  | refl => exact ⟨rfl, connect_refl _⟩
  | @tail a c _ hac ih =>
    obtain rfl : R.double.facePerm a = c := hac
    obtain ⟨d', b'⟩ := a
    obtain ⟨h2, h1⟩ := ih
    obtain rfl : b' = true := h2
    exact ⟨rfl, connect_trans h1 (fconnect1 _ d')⟩

/-- A path of `R` through pairwise distinct vertices, with two corners at its ends on two different
faces. -/
structure CutPath where
  /-- The last index. -/
  m : ℕ
  /-- The vertices `p_0, …, p_m`. -/
  v : ℕ → R.Vertex
  /-- The dart from `p_t` to `p_{t+1}`. -/
  e : ℕ → D
  /-- The corner of the cut at `p_0`. -/
  cs : D
  /-- The corner of the cut at `p_m`. -/
  ct : D
  tail_e : ∀ t, t < m → R.tail (e t) = v t
  head_e : ∀ t, t < m → R.head (e t) = v (t + 1)
  tail_cs : R.tail cs = v 0
  tail_ct : R.tail ct = v m
  inj : ∀ s t, s ≤ m → t ≤ m → v s = v t → s = t
  faces : ¬ fconnect R.facePerm cs ct

namespace CutPath

variable {R} (C : R.CutPath)

/-- The corner of `p_t^0`: the digon corner of `e t`, or `ct` at the end. -/
def k0 (t : ℕ) : D × Bool := if t < C.m then (C.e t, false) else (C.ct, true)

/-- The corner of `p_t^1`: the digon corner of `e (t - 1)` at `p_t`, or `cs` at the start. -/
def k1 (t : ℕ) : D × Bool := if t = 0 then (C.cs, true) else (R.rev (C.e (t - 1)), false)

/-- The corner of the copy `p_t^σ`. -/
def k (σ : Fin 2) (t : ℕ) : D × Bool := if σ = 0 then C.k0 t else C.k1 t

@[simp] theorem k_zero (t : ℕ) : C.k 0 t = C.k0 t := rfl

@[simp] theorem k_one (t : ℕ) : C.k 1 t = C.k1 t := rfl

/-- The corners of the cut. -/
def Γ : Finset (D × Bool) := (Recursion.copyCorners C.k C.m).toFinset

theorem tail_k0 {t : ℕ} (ht : t ≤ C.m) : R.tail (C.k0 t).1 = C.v t := by
  unfold k0
  split_ifs with h
  · exact C.tail_e t h
  · obtain rfl : t = C.m := by omega
    exact C.tail_ct

theorem tail_k1 {t : ℕ} (ht : t ≤ C.m) : R.tail (C.k1 t).1 = C.v t := by
  unfold k1
  split_ifs with h
  · subst h
    exact C.tail_cs
  · have := C.head_e (t - 1) (by omega)
    rw [show t - 1 + 1 = t by omega] at this
    exact this

theorem tail_k {σ : Fin 2} {t : ℕ} (ht : t ≤ C.m) : R.tail (C.k σ t).1 = C.v t := by
  unfold k
  split_ifs
  · exact C.tail_k0 ht
  · exact C.tail_k1 ht

theorem k0_ne_k1 (t : ℕ) : C.k0 t ≠ C.k1 t := by
  unfold k0 k1
  split_ifs with h1 h2 h2
  · simp
  · intro h
    have he : C.e t = R.rev (C.e (t - 1)) := congrArg Prod.fst h
    have h3 := C.head_e t h1
    have h4 := C.tail_e (t - 1) (by omega)
    rw [he, R.head_rev, h4] at h3
    have := C.inj _ _ (by omega) (by omega) h3
    omega
  · intro h
    have hc : C.ct = C.cs := congrArg Prod.fst h
    exact C.faces (hc ▸ connect_refl _)
  · simp

theorem k_eq_iff {σ τ : Fin 2} {s t : ℕ} (hs : s ≤ C.m) (ht : t ≤ C.m) :
    C.k σ s = C.k τ t ↔ σ = τ ∧ s = t := by
  constructor
  · intro h
    have hst : s = t := C.inj _ _ hs ht (by rw [← C.tail_k hs, ← C.tail_k ht, h])
    subst hst
    refine ⟨?_, rfl⟩
    fin_cases σ <;> fin_cases τ
    · rfl
    · exact absurd h (C.k0_ne_k1 s)
    · exact absurd h.symm (C.k0_ne_k1 s)
    · rfl
  · rintro ⟨rfl, rfl⟩
    rfl

theorem mem_Γ {z : D × Bool} : z ∈ C.Γ ↔ ∃ σ t, t ≤ C.m ∧ z = C.k σ t := by
  simp only [Γ, Recursion.copyCorners, List.mem_toFinset, List.mem_append, List.mem_map,
    List.mem_reverse, List.mem_range]
  constructor
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨0, t, by omega, rfl⟩
    · exact ⟨1, t, by omega, rfl⟩
  · rintro ⟨σ, t, ht, rfl⟩
    fin_cases σ
    · exact Or.inl ⟨t, by omega, rfl⟩
    · exact Or.inr ⟨t, by omega, rfl⟩

theorem k_mem {σ : Fin 2} {t : ℕ} (ht : t ≤ C.m) : C.k σ t ∈ C.Γ :=
  C.mem_Γ.2 ⟨σ, t, ht, rfl⟩

theorem nodup : (Recursion.copyCorners C.k C.m).Nodup := by
  unfold Recursion.copyCorners
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · refine List.Nodup.map_on (fun s hs t ht h => ?_) List.nodup_range
    exact ((C.k_eq_iff (by simpa [Nat.lt_succ_iff] using hs)
      (by simpa [Nat.lt_succ_iff] using ht)).1 h).2
  · refine List.Nodup.map_on (fun s hs t ht h => ?_) (List.nodup_reverse.2 List.nodup_range)
    exact ((C.k_eq_iff (by simpa [Nat.lt_succ_iff] using hs)
      (by simpa [Nat.lt_succ_iff] using ht)).1 h).2
  · intro a ha b hb hab
    simp only [List.mem_map, List.mem_range, List.mem_reverse] at ha hb
    obtain ⟨s, hs, rfl⟩ := ha
    obtain ⟨t, ht, rfl⟩ := hb
    have := ((C.k_eq_iff (σ := 0) (τ := 1) (by omega) (by omega)).1 hab).1
    exact absurd this (by decide)

/-- At `p_t`, the corners of `Γ` are `k 0 t` and `k 1 t`. -/
theorem mem_Γ_of_fconnect {σ : Fin 2} {t : ℕ} (ht : t ≤ C.m) {z : D × Bool} (hz : z ∈ C.Γ)
    (h : fconnect R.double.rot (C.k σ t) z) : z = C.k 0 t ∨ z = C.k 1 t := by
  obtain ⟨τ, s, hs, rfl⟩ := C.mem_Γ.1 hz
  have h1 := R.fconnect_of_double h
  have h2 : R.tail (C.k σ t).1 = R.tail (C.k τ s).1 := (R.tail_eq_iff _ _).2 h1
  rw [C.tail_k ht, C.tail_k hs] at h2
  obtain rfl := C.inj _ _ hs ht h2.symm
  fin_cases τ
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem fconnect_k {σ τ : Fin 2} {t : ℕ} (ht : t ≤ C.m) :
    fconnect R.double.rot (C.k σ t) (C.k τ t) := by
  have h : fconnect R.rot (C.k σ t).1 (C.k τ t).1 :=
    (R.tail_eq_iff _ _).1 (by rw [C.tail_k ht, C.tail_k ht])
  have := R.fconnect_double h (C.k σ t).2 (C.k τ t).2
  simpa using this

/-- The first return of the rotation swaps the two corners at `p_t`. -/
theorem nodeReturn_k0 {t : ℕ} (ht : t ≤ C.m) : R.double.nodeReturn C.Γ (C.k 0 t) = C.k 1 t :=
  firstReturn_eq_of_pair (C.k_mem ht) (C.k_mem ht) (C.k0_ne_k1 t) (C.fconnect_k ht)
    (fun _ hz h => C.mem_Γ_of_fconnect ht hz h)

theorem nodeReturn_k1 {t : ℕ} (ht : t ≤ C.m) : R.double.nodeReturn C.Γ (C.k 1 t) = C.k 0 t :=
  firstReturn_eq_of_pair (C.k_mem ht) (C.k_mem ht) (C.k0_ne_k1 t).symm (C.fconnect_k ht)
    (fun _ hz h => (C.mem_Γ_of_fconnect ht hz h).symm)

theorem k1_succ {t : ℕ} : C.k1 (t + 1) = (R.rev (C.e t), false) := by
  simp [k1]

/-- The first return of the faces swaps the two corners of the digon of `e t`. -/
theorem faceReturn_k0_lt {t : ℕ} (ht : t < C.m) :
    R.double.faceReturn C.Γ (C.k 0 t) = C.k 1 (t + 1) := by
  have h0 : C.k 0 t = (C.e t, false) := by simp [k0, ht]
  have h1 : C.k 1 (t + 1) = (R.rev (C.e t), false) := C.k1_succ
  refine firstReturn_eq_of_pair (C.k_mem ht.le) (C.k_mem (by omega)) ?_ ?_ ?_
  · rw [h0, h1]
    intro h
    exact R.rev_ne (C.e t) (congrArg Prod.fst h).symm
  · rw [h0, h1]
    exact fconnect1 _ _
  · intro z _ hz
    rw [h0] at hz
    rw [h0, h1]
    exact R.mem_digon hz

theorem faceReturn_k1_succ {t : ℕ} (ht : t < C.m) :
    R.double.faceReturn C.Γ (C.k 1 (t + 1)) = C.k 0 t := by
  have h0 : C.k 0 t = (C.e t, false) := by simp [k0, ht]
  have h1 : C.k 1 (t + 1) = (R.rev (C.e t), false) := C.k1_succ
  refine firstReturn_eq_of_pair (C.k_mem (by omega)) (C.k_mem ht.le) ?_ ?_ ?_
  · rw [h0, h1]
    intro h
    exact R.rev_ne (C.e t) (congrArg Prod.fst h)
  · rw [h0, h1]
    have := fconnect1 R.double.facePerm (R.rev (C.e t), false)
    rwa [R.double_face_false, R.rev_rev] at this
  · intro z _ hz
    rw [h1] at hz
    rw [h0, h1]
    rcases R.mem_digon hz with h | h
    · exact Or.inl h
    · rw [R.rev_rev] at h
      exact Or.inr h

/-- The corners of `Γ` on a face of the second copy are the two end corners. -/
theorem k_snd {σ : Fin 2} {t : ℕ} (ht : t ≤ C.m) (h : (C.k σ t).2 = true) :
    (σ = 0 ∧ t = C.m ∧ C.k σ t = (C.ct, true)) ∨ (σ = 1 ∧ t = 0 ∧ C.k σ t = (C.cs, true)) := by
  fin_cases σ
  · left
    change (C.k0 t).2 = true at h
    refine ⟨rfl, ?_⟩
    change t = C.m ∧ C.k0 t = (C.ct, true)
    unfold k0 at h ⊢
    split_ifs at h ⊢ with h'
    exact ⟨by omega, rfl⟩
  · right
    change (C.k1 t).2 = true at h
    refine ⟨rfl, ?_⟩
    change t = 0 ∧ C.k1 t = (C.cs, true)
    unfold k1 at h ⊢
    split_ifs at h ⊢ with h'
    exact ⟨h', rfl⟩

/-- The two end corners are the only corners of `Γ` of their faces. -/
theorem faceReturn_end {σ : Fin 2} {t : ℕ} (ht : t ≤ C.m) (hb : (C.k σ t).2 = true) :
    R.double.faceReturn C.Γ (C.k σ t) = C.k σ t := by
  refine firstReturn_eq_self_of (C.k_mem ht) fun z hz h => ?_
  have hk : C.k σ t = ((C.k σ t).1, true) := by rw [← hb]
  rw [hk] at h
  obtain ⟨hz2, hz1⟩ := R.mem_face_true h
  obtain ⟨τ, s, hs, rfl⟩ := C.mem_Γ.1 hz
  rcases C.k_snd ht hb with ⟨rfl, rfl, h1⟩ | ⟨rfl, rfl, h1⟩ <;>
    rcases C.k_snd hs hz2 with ⟨rfl, rfl, h2⟩ | ⟨rfl, rfl, h2⟩
  · rfl
  · rw [h1, h2] at hz1
    exact absurd (fconnect_symm hz1) C.faces
  · rw [h1, h2] at hz1
    exact absurd hz1 C.faces
  · rfl

theorem k0_last_true : (C.k 0 C.m).2 = true := by simp [k0]

theorem k1_zero_true : (C.k 1 0).2 = true := by simp [k1]

/-- `ψ` on the copies: the successor along `p_0^0, …, p_m^0, p_m^1, …, p_0^1`, cyclically. -/
theorem psi_k0_lt {t : ℕ} (ht : t < C.m) : R.double.psi C.Γ (C.k 0 t) = C.k 0 (t + 1) := by
  rw [psi, Equiv.Perm.mul_apply, C.faceReturn_k0_lt ht, C.nodeReturn_k1 (by omega)]

theorem psi_k0_last : R.double.psi C.Γ (C.k 0 C.m) = C.k 1 C.m := by
  rw [psi, Equiv.Perm.mul_apply, C.faceReturn_end le_rfl C.k0_last_true, C.nodeReturn_k0 le_rfl]

theorem psi_k1_succ {t : ℕ} (ht : t < C.m) : R.double.psi C.Γ (C.k 1 (t + 1)) = C.k 1 t := by
  rw [psi, Equiv.Perm.mul_apply, C.faceReturn_k1_succ ht, C.nodeReturn_k0 ht.le]

theorem psi_k1_zero : R.double.psi C.Γ (C.k 1 0) = C.k 0 0 := by
  rw [psi, Equiv.Perm.mul_apply, C.faceReturn_end (Nat.zero_le _) C.k1_zero_true,
    C.nodeReturn_k1 (Nat.zero_le _)]

theorem length_copyCorners : (Recursion.copyCorners C.k C.m).length = 2 * C.m + 2 := by
  simp [Recursion.copyCorners]
  omega

theorem getElem_copyCorners {i : ℕ} (hi : i < (Recursion.copyCorners C.k C.m).length) :
    (Recursion.copyCorners C.k C.m)[i] =
      if i ≤ C.m then C.k 0 i else C.k 1 (2 * C.m + 1 - i) := by
  simp only [Recursion.copyCorners, List.getElem_append, List.length_map, List.length_range,
    List.getElem_map, List.getElem_range, List.getElem_reverse]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- **`ψ` is the cycle of the copies.** -/
theorem psi_eq : R.double.psi C.Γ = (Recursion.copyCorners C.k C.m).formPerm := by
  refine Equiv.ext fun z => ?_
  by_cases hz : z ∈ Recursion.copyCorners C.k C.m
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hz
    rw [List.formPerm_apply_getElem _ C.nodup i hi]
    have hl := C.length_copyCorners
    rw [C.getElem_copyCorners hi, C.getElem_copyCorners]
    simp only [hl]
    rcases Nat.lt_or_ge i C.m with h | h
    · rw [ite_eq_left h.le, Nat.mod_eq_of_lt (by omega), ite_eq_left (by omega), C.psi_k0_lt h]
    rcases Nat.eq_or_lt_of_le h with h | h
    · subst h
      rw [ite_eq_left le_rfl, Nat.mod_eq_of_lt (by omega), ite_eq_right (by omega),
        show 2 * C.m + 1 - (C.m + 1) = C.m by omega, C.psi_k0_last]
    · rw [ite_eq_right (by omega)]
      rcases Nat.lt_or_ge (i + 1) (2 * C.m + 2) with h' | h'
      · rw [Nat.mod_eq_of_lt h', ite_eq_right (by omega)]
        have e1 : 2 * C.m + 1 - i = (2 * C.m + 1 - (i + 1)) + 1 := by omega
        rw [e1, C.psi_k1_succ (by omega)]
      · have hi2 : i = 2 * C.m + 1 := by rw [hl] at hi; omega
        subst hi2
        rw [show 2 * C.m + 1 + 1 = 2 * C.m + 2 by omega, Nat.mod_self, ite_eq_left (Nat.zero_le _),
          show 2 * C.m + 1 - (2 * C.m + 1) = 0 by omega, C.psi_k1_zero]
  · have hz' : z ∉ C.Γ := by simpa [Γ] using hz
    rw [List.formPerm_apply_of_notMem hz, (R.double.fixesOff_psi C.Γ) z hz']

theorem Γ_nonempty : C.Γ.Nonempty := ⟨_, C.k_mem (σ := 0) (Nat.zero_le C.m)⟩

/-- `Γ` is connected: `ψ` is one cycle on it, and each of its steps is a face step followed by a
vertex step of the skeleton. -/
theorem skeletonConnected : R.double.SkeletonConnected C.Γ := by
  intro x hx y hy
  have hxl : x ∈ Recursion.copyCorners C.k C.m := by simpa [Γ] using hx
  have hyl : y ∈ Recursion.copyCorners C.k C.m := by simpa [Γ] using hy
  have hc := (C.nodup.isCycleOn_formPerm).2 (show x ∈ {a | a ∈ _} from hxl)
    (show y ∈ {a | a ∈ _} from hyl)
  rw [← C.psi_eq] at hc
  have hf : fconnect (R.double.psi C.Γ) x y := (sameCycle_iff_fconnect _).1 hc
  refine connect_sub (fun a _ hab => ?_) hf
  obtain rfl : R.double.psi C.Γ a = _ := hab
  refine connect_trans (connect_of_rel (Or.inr (Or.inr rfl))) (connect_of_rel (Or.inr (Or.inl ?_)))
  rfl

/-- The cut of `R` along the path. -/
noncomputable abbrev cut : RotSystem (D × Bool) := R.double.split C.Γ

/-- Each vertex of the cut has at most one corner of `Γ`. -/
theorem cut_tail_inj {x y : D × Bool} (hx : x ∈ C.Γ) (hy : y ∈ C.Γ)
    (h : C.cut.tail x = C.cut.tail y) : x = y := by
  have h1 := (fconnect_firstReturn_iff (C.cut.rot) hx hy).2 ((C.cut.tail_eq_iff x y).1 h)
  rw [show firstReturn C.cut.rot C.Γ = 1 from R.double.nodeReturn_split C.Γ] at h1
  obtain ⟨n, hn⟩ := fconnect_iff_iterate.1 h1
  simpa using hn

/-- **The cut is drawn.** For a planar connected map, the copies of the path are corners of one
face of the cut, at pairwise distinct vertices, in the cyclic order `p_0^0, …, p_m^0, p_m^1, …,
p_0^1`. -/
theorem faceDrawn (hR : R.Planar) (hc : R.Connected) :
    C.cut.FaceDrawn (Recursion.copyCorners C.k C.m) where
  planar := (R.double.split_planar (R.double_planar hR hc) (R.double_connected hc) C.Γ_nonempty
    C.skeletonConnected).1
  tails_nodup := List.Nodup.map_on (fun x hx y hy h =>
    C.cut_tail_inj (List.mem_toFinset.2 hx) (List.mem_toFinset.2 hy) h) C.nodup
  order := by
    show C.cut.faceReturn C.Γ = _
    rw [R.double.faceReturn_split, C.psi_eq]

theorem nodeReturn_inv_k0 {t : ℕ} (ht : t ≤ C.m) :
    (R.double.nodeReturn C.Γ)⁻¹ (C.k 0 t) = C.k 1 t :=
  Equiv.Perm.inv_eq_iff_eq.2 (C.nodeReturn_k1 ht).symm

theorem nodeReturn_inv_k1 {t : ℕ} (ht : t ≤ C.m) :
    (R.double.nodeReturn C.Γ)⁻¹ (C.k 1 t) = C.k 0 t :=
  Equiv.Perm.inv_eq_iff_eq.2 (C.nodeReturn_k0 ht).symm

/-- The copies of `e t` are darts of the cut from `p_t^σ` to `p_{t+1}^σ`. -/
theorem exists_copyDart (σ : Fin 2) {t : ℕ} (ht : t < C.m) : ∃ x : D × Bool, x.1 = C.e t ∧
    C.cut.tail x = C.cut.tail (C.k σ t) ∧ C.cut.head x = C.cut.tail (C.k σ (t + 1)) := by
  have h0 : C.k 0 t = (C.e t, false) := by simp [k0, ht]
  fin_cases σ
  · refine ⟨(C.e t, false), rfl, by rw [show C.k ⟨0, by omega⟩ t = C.k 0 t from rfl, h0], ?_⟩
    show _ = C.cut.tail (C.k 0 (t + 1))
    rw [← C.cut.tail_rot (C.k 0 (t + 1)), R.double.split_rot_apply, C.nodeReturn_inv_k0 (by omega),
      k_one, k1_succ]
    rfl
  · refine ⟨(C.e t, true), rfl, ?_, ?_⟩
    · show _ = C.cut.tail (C.k 1 t)
      rw [← C.cut.tail_rot (C.k 1 t), R.double.split_rot_apply, C.nodeReturn_inv_k1 ht.le, h0]
      rfl
    · show _ = C.cut.tail (C.k 1 (t + 1))
      rw [k_one, k1_succ]
      rfl

/-- The vertices of the cut lie in vertices of the doubled map. -/
theorem fconnect_double_of_cut {x y : D × Bool} (h : fconnect C.cut.rot x y) :
    fconnect R.double.rot x y := by
  refine connect_sub (fun a _ hab => ?_) h
  obtain rfl : C.cut.rot a = _ := hab
  rw [R.double.split_rot_apply]
  have h1 := fconnect_firstReturn R.double.rot C.Γ ((R.double.nodeReturn C.Γ)⁻¹ a)
  rw [show firstReturn R.double.rot C.Γ ((R.double.nodeReturn C.Γ)⁻¹ a) = a from
    Equiv.apply_symm_apply _ a] at h1
  exact connect_trans (fconnect_symm h1) (fconnect1 _ _)

theorem tail_fst_of_cut {x y : D × Bool} (h : C.cut.tail x = C.cut.tail y) :
    R.tail x.1 = R.tail y.1 :=
  (R.tail_eq_iff _ _).2 (R.fconnect_of_double (C.fconnect_double_of_cut ((C.cut.tail_eq_iff x y).1 h)))

/-- A walk of the cut is a walk of `R`. -/
theorem isWalk_fst {ws : List (D × Bool)} {z z' : D × Bool}
    (h : C.cut.IsWalk (C.cut.tail z) ws (C.cut.tail z')) :
    R.IsWalk (R.tail z.1) (ws.map Prod.fst) (R.tail z'.1) := by
  induction ws generalizing z with
  | nil => exact C.tail_fst_of_cut h
  | cons y ws ih =>
    obtain ⟨h1, h2⟩ := h
    rw [List.map_cons]
    exact ⟨C.tail_fst_of_cut h1, ih (z := C.cut.rev y) h2⟩

end CutPath

end RotSystem

end SsspFlow
