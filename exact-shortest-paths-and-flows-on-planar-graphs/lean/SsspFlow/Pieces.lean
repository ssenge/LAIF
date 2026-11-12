import SsspFlow.Live
import Mathlib.Data.List.GetD

/-!
# The pieces of a live annulus

The vertex `p_t` of the path splits in the cut into its two copies `p_t^0` and `p_t^1`: a dart of
the doubled map at `p_t` lies at one of them (`CutPath.sector`) and not at both
(`CutPath.not_sector_both`). A dart of an edge of the path joins two copies of one side
(`CutPath.side_eq`), so a dart from a copy `p_s^0` to a copy `p_{s'}^1` is no dart of an edge of the
path (`CutPath.not_mem_Γ_of_sides`).

A live annulus has at most one vertex at each copy: a dart of its component at the copy `p_t^0` lies
at the vertex of `κ0(t)`, and then `x_a ≤ t ≤ x_b`; at the copy `p_t^1` it lies at the vertex of
`κ1(t)`, and then `y_a ≤ t ≤ y_b` (`CutPath.Live.piece`). This is (I3) of Lemma O.

A simple shortest walk of a live annulus from the vertex of `κ0(i)` to the vertex of `κ1(i)` contains
a step (`CutPath.Live.exists_step`): its part from its last vertex at a copy `p_x^0` to the first
vertex at a copy `p_y^1` after it. `CutPath.Live.exists_step_sel` also keeps these two choices.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor
open scoped ENNReal

namespace RotSystem

section Split

variable {E : Type*} [Fintype E] [DecidableEq E] (M : RotSystem E)

/-- A dart at a vertex with a corner of `Γ` lies at a vertex of the split with a corner of `Γ`. -/
theorem exists_corner_split {Γ : Finset E} {c : E} (hc : c ∈ Γ) {z : E}
    (h : fconnect M.rot z c) : ∃ c' ∈ Γ, fconnect (M.split Γ).rot z c' := by
  obtain ⟨k, hk⟩ := fconnect_iff_iterate.1 h
  clear h
  induction k generalizing z with
  | zero => exact ⟨z, by rw [show z = c from hk]; exact hc, connect_refl _⟩
  | succ k ih =>
    by_cases hz : z ∈ Γ
    · exact ⟨z, hz, connect_refl _⟩
    · have e : (M.split Γ).rot z = M.rot z := by
        rw [M.split_rot_apply, Equiv.Perm.inv_eq_iff_eq.2 (M.fixesOff_nodeReturn Γ z hz).symm]
      rw [Function.iterate_succ_apply] at hk
      obtain ⟨c', hc', h'⟩ := ih hk
      exact ⟨c', hc', connect_trans (by rw [← e]; exact fconnect1 _ z) h'⟩

end Split

section Walks

variable {E : Type*} [Fintype E] [DecidableEq E] {M : RotSystem E}

/-- The darts of a walk from the vertex of `a`, and their reverses, lie in the component of `a`. -/
theorem IsWalk.gcomp {a : E} : ∀ {p : List E} {v : M.Vertex}, M.IsWalk (M.tail a) p v →
    ∀ x ∈ p, M.toHypermap.gcomp a x ∧ M.toHypermap.gcomp a (M.rev x)
  | [], _, _ => by simp
  | x :: p, _, h => by
    have hx : M.toHypermap.gcomp a x :=
      M.toHypermap.gcomp_of_cnode ((M.tail_eq_iff _ _).1 h.1.symm)
    have hr : M.toHypermap.gcomp a (M.rev x) :=
      connect_trans hx (connect_of_rel (M.toHypermap.glinkE _))
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨hx, hr⟩
    · obtain ⟨h1, h2⟩ := IsWalk.gcomp (a := M.rev x) h.2 y hy
      exact ⟨connect_trans hr h1, connect_trans hr h2⟩

theorem IsWalk.tail_getElem_zero {u v : M.Vertex} {p : List E} (h : M.IsWalk u p v)
    (hp : 0 < p.length) : M.tail p[0] = u := by
  cases p with
  | nil => simp at hp
  | cons x p => exact h.1

theorem IsWalk.head_getElem : ∀ {u v : M.Vertex} {p : List E}, M.IsWalk u p v →
    ∀ j (hj : j + 1 < p.length), M.head p[j] = M.tail p[j + 1]
  | _, _, [], _, _, hj => by simp at hj
  | _, _, [_], _, _, hj => by simp at hj
  | _, _, _ :: _ :: _, h, 0, _ => h.2.1.symm
  | _, _, _ :: y :: p, h, j + 1, hj => IsWalk.head_getElem (p := y :: p) h.2 j (by simpa using hj)

theorem IsWalk.head_getElem_last {u v : M.Vertex} {p : List E} (h : M.IsWalk u p v)
    (hp : 0 < p.length) : M.head p[p.length - 1] = v := by
  have e := List.dropLast_append_getLast (List.ne_nil_of_length_pos hp)
  rw [← e] at h
  obtain ⟨t, -, ht⟩ := isWalk_append_iff.1 h
  rw [← List.getLast_eq_getElem]
  exact ht.2

end Walks

theorem range_map_getD {α : Type*} (l : List α) (d : α) :
    (List.range l.length).map (fun j => l.getD j d) = l :=
  List.ext_getElem (by simp) fun j h1 h2 => by
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem _ _ h2

variable {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace CutPath

variable (C : R.CutPath)

/-- **The two copies of a vertex of the path.** A dart of the doubled map at `p_t` lies in the cut
at the copy `p_t^0` or at the copy `p_t^1`. -/
theorem sector {z : D × Bool} {t : ℕ} (ht : t ≤ C.m) (hz : R.tail z.1 = C.v t) :
    fconnect C.cut.rot z (C.k 0 t) ∨ fconnect C.cut.rot z (C.k 1 t) := by
  have h0 : fconnect R.double.rot z (C.k 0 t) := by
    simpa using R.fconnect_double ((R.tail_eq_iff _ _).1 (hz.trans (C.tail_k (σ := 0) ht).symm))
      z.2 (C.k 0 t).2
  obtain ⟨c, hc, hzc⟩ := R.double.exists_corner_split (C.k_mem ht) h0
  rcases C.mem_Γ_of_fconnect ht hc
      (connect_trans (fconnect_symm h0) (C.fconnect_double_of_cut hzc)) with rfl | rfl
  · exact Or.inl hzc
  · exact Or.inr hzc

/-- No dart lies at both copies of `p_t`. -/
theorem not_sector_both {z : D × Bool} {t : ℕ} (ht : t ≤ C.m)
    (h0 : fconnect C.cut.rot z (C.k 0 t)) (h1 : fconnect C.cut.rot z (C.k 1 t)) : False := by
  have := C.cut_tail_inj (C.k_mem ht) (C.k_mem ht)
    ((C.cut.tail_eq_iff _ _).2 (connect_trans (fconnect_symm h0) h1))
  exact absurd ((C.k_eq_iff ht ht).1 this).1 (by decide)

/-- **A dart of an edge of the path joins two copies of one side.** -/
theorem side_eq {w : D × Bool} {t : ℕ} (ht : t < C.m) (hw : w.1 = C.e t) {σ τ : Fin 2}
    {s s' : ℕ} (hs : s ≤ C.m) (hs' : s' ≤ C.m) (h0 : C.cut.tail w = C.cut.tail (C.k σ s))
    (h1 : C.cut.head w = C.cut.tail (C.k τ s')) : σ = τ := by
  have inj : ∀ {a b : Fin 2} {u u' : ℕ}, u ≤ C.m → u' ≤ C.m →
      C.cut.tail (C.k a u) = C.cut.tail (C.k b u') → a = b := fun hu hu' h =>
    ((C.k_eq_iff hu hu').1 (C.cut_tail_inj (C.k_mem hu) (C.k_mem hu') h)).1
  obtain ⟨x₀, e₀, t₀, h₀⟩ := C.exists_copyDart 0 ht
  obtain ⟨x₁, e₁, t₁, h₁⟩ := C.exists_copyDart 1 ht
  have hne : x₀.2 ≠ x₁.2 := fun h => by
    have hx : x₀ = x₁ := Prod.ext (e₀.trans e₁.symm) h
    rw [hx] at t₀
    exact absurd (inj ht.le ht.le (t₀.symm.trans t₁)) (by decide)
  have key : ∀ a b c : Bool, b ≠ c → a = b ∨ a = c := by decide
  rcases key w.2 x₀.2 x₁.2 hne with hb | hb
  · obtain rfl : w = x₀ := Prod.ext (hw.trans e₀.symm) hb
    exact (inj hs ht.le (h0.symm.trans t₀)).trans (inj (by omega) hs' (h₀.symm.trans h1))
  · obtain rfl : w = x₁ := Prod.ext (hw.trans e₁.symm) hb
    exact (inj hs ht.le (h0.symm.trans t₁)).trans (inj (by omega) hs' (h₁.symm.trans h1))

/-- A dart from a vertex at a copy `p_s^0` to a vertex at a copy `p_{s'}^1` is no dart of an edge
of the path. -/
theorem not_mem_Γ_of_sides {z : D × Bool} {s s' : ℕ} (hs : s ≤ C.m) (hs' : s' ≤ C.m)
    (h0 : C.cut.tail z = C.cut.tail (C.k 0 s)) (h1 : C.cut.head z = C.cut.tail (C.k 1 s')) :
    (z.1, false) ∉ C.Γ := by
  intro hz
  obtain ⟨τ, t, ht, he⟩ := C.mem_Γ.1 hz
  fin_cases τ
  · have he' : (z.1, false) = C.k0 t := he
    unfold k0 at he'
    split_ifs at he' with h2
    · exact absurd (C.side_eq (w := z) h2 (congrArg Prod.fst he') hs hs' h0 h1) (by decide)
    · simp at he'
  · have he' : (z.1, false) = C.k1 t := he
    unfold k1 at he'
    split_ifs at he' with h2
    · simp at he'
    · have e1 : z.1 = R.rev (C.e (t - 1)) := congrArg Prod.fst he'
      have hw : (R.double.rev z).1 = C.e (t - 1) := by
        show R.rev z.1 = _
        rw [e1, R.rev_rev]
      have h0' : C.cut.tail (R.double.rev z) = C.cut.tail (C.k 1 s') := h1
      have h1' : C.cut.head (R.double.rev z) = C.cut.tail (C.k 0 s) := by
        show C.cut.tail (R.double.rev (R.double.rev z)) = _
        rw [R.double.rev_rev]
        exact h0
      exact absurd (C.side_eq (show t - 1 < C.m by omega) hw hs' hs h0' h1') (by decide)

/-- No dart lies at a copy `p_t^0` and at a copy `p_{t'}^1`. -/
theorem not_copy_both {z : D × Bool} {t t' : ℕ} (ht : t ≤ C.m) (ht' : t' ≤ C.m)
    (h0 : fconnect C.cut.rot z (C.k 0 t)) (h1 : fconnect C.cut.rot z (C.k 1 t')) : False := by
  have e0 := (C.tail_fst_of_cut ((C.cut.tail_eq_iff _ _).2 h0)).trans (C.tail_k ht)
  have e1 := (C.tail_fst_of_cut ((C.cut.tail_eq_iff _ _).2 h1)).trans (C.tail_k ht')
  obtain rfl := C.inj _ _ ht ht' (e0.symm.trans e1)
  exact C.not_sector_both ht h0 h1

/-- A vertex of the split at a copy `p_t^σ` for some `t`. -/
def atCopy (Γ : Finset (D × Bool)) (σ : Fin 2) (u : (R.double.split Γ).Vertex) : Prop :=
  ∃ z, (R.double.split Γ).tail z = u ∧ ∃ t, t ≤ C.m ∧ fconnect C.cut.rot z (C.k σ t)

theorem atCopy_tail {Γ : Finset (D × Bool)} (hΓ : C.Γ ⊆ Γ) {σ : Fin 2} {z : D × Bool} :
    C.atCopy Γ σ ((R.double.split Γ).tail z) ↔ ∃ t, t ≤ C.m ∧ fconnect C.cut.rot z (C.k σ t) := by
  constructor
  · rintro ⟨z', hz', t, ht, h⟩
    exact ⟨t, ht, connect_trans (fconnect_of_split_subset hΓ
      (((R.double.split Γ).tail_eq_iff _ _).1 hz'.symm)) h⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨z, rfl, t, ht, h⟩

namespace Live

variable {C} {g : D → ℝ≥0∞} {Γ : Finset (D × Bool)} (L : C.Live g Γ)

/-- **(I3) for a live annulus.** A dart of the component at the copy `p_t^0` lies at the vertex of
`κ0(t)`, and `x_a ≤ t ≤ x_b`; a dart of the component at the copy `p_t^1` lies at the vertex of
`κ1(t)`, and `y_a ≤ t ≤ y_b`. -/
theorem piece (hR : R.Planar) (hC : R.Connected) {c0 z : D × Bool}
    (hc0 : c0 ∈ liveBoundary L.κ0 L.κ1 L.xa L.xb L.ya L.yb L.La L.Lb)
    (hz : (R.double.split Γ).toHypermap.gcomp c0 z) {σ : Fin 2} {t : ℕ} (ht : t ≤ C.m)
    (hσ : fconnect C.cut.rot z (C.k σ t)) :
    (σ = 0 ∧ L.xa ≤ t ∧ t ≤ L.xb ∧ fconnect (R.double.split Γ).rot z (L.κ0 t)) ∨
      (σ = 1 ∧ L.ya ≤ t ∧ t ≤ L.yb ∧ fconnect (R.double.split Γ).rot z (L.κ1 t)) := by
  have hv : R.tail z.1 = C.v t :=
    (C.tail_fst_of_cut ((C.cut.tail_eq_iff _ _).2 hσ)).trans (C.tail_k ht)
  obtain ⟨c, hc, hzc⟩ := R.double.exists_corner_split (L.sub (C.k_mem ht))
    (C.fconnect_double_of_cut hσ)
  have hcb : c ∈ liveBoundary L.κ0 L.κ1 L.xa L.xb L.ya L.yb L.La L.Lb :=
    (L.bound.gcomp_iff (R.double_planar hR hC) (R.double_connected hC) ⟨c0, L.bound.sub _ hc0⟩
      L.skel hc0 hc).1 (connect_trans hz ((R.double.split Γ).toHypermap.gcomp_of_cnode hzc))
  have hcv : R.tail c.1 = C.v t := (DiskChord.tail_fst hzc).symm.trans hv
  have hcσ : fconnect C.cut.rot c (C.k σ t) :=
    connect_trans (fconnect_symm (fconnect_of_split_subset L.sub hzc)) hσ
  have hσ' : ∀ τ, fconnect C.cut.rot c (C.k τ t) → σ = τ := fun τ h =>
    ((C.k_eq_iff ht ht).1 (C.cut_tail_inj (C.k_mem ht) (C.k_mem ht)
      ((C.cut.tail_eq_iff _ _).2 (connect_trans (fconnect_symm hcσ) h)))).1
  unfold liveBoundary at hcb
  simp only [List.mem_append, List.mem_reverse, or_assoc] at hcb
  rcases hcb with hcb | hcb | hcb | hcb
  · obtain ⟨t', h1, h2, rfl⟩ := mem_cornerSeg.1 hcb
    obtain rfl : t' = t := C.inj _ _ (h2.trans L.xb_le) ht ((L.tail_κ0 h1 h2).symm.trans hcv)
    exact Or.inl ⟨hσ' 0 (L.piece0 t' h1 h2), h1, h2, hzc⟩
  · exact absurd hcv (L.off c (List.mem_append_left _ hcb) t ht)
  · obtain ⟨t', h1, h2, rfl⟩ := mem_cornerSeg.1 hcb
    obtain rfl : t' = t := C.inj _ _ (h2.trans L.yb_le) ht ((L.tail_κ1 h1 h2).symm.trans hcv)
    exact Or.inr ⟨hσ' 1 (L.piece1 t' h1 h2), h1, h2, hzc⟩
  · exact absurd hcv (L.off c (List.mem_append_right _ hcb) t ht)

/-- **The step of a shortest walk, with its ends.** A simple shortest walk of finite length from the
vertex of `κ0(i)` to the vertex of `κ1(i)` contains a step: its part from its last vertex at a copy
`p_x^0` to the first vertex at a copy `p_y^1` after it. No dart from the start of the step on ends at
a copy `p_t^0`, and no dart of the step starts at a copy `p_t^1`. -/
theorem exists_step_sel (hR : R.Planar) (hC : R.Connected) {i : ℕ} (h1 : L.xa ≤ i) (h2 : i ≤ L.xb)
    (h3 : L.ya ≤ i) (h4 : i ≤ L.yb) {p : List (D × Bool)}
    (hp : (R.double.split Γ).IsWalk ((R.double.split Γ).tail (L.κ0 i)) p
      ((R.double.split Γ).tail (L.κ1 i)))
    (hnd : (p.map (R.double.split Γ).tail).Nodup)
    (hne : ∀ z ∈ p, (R.double.split Γ).tail z ≠ (R.double.split Γ).tail (L.κ1 i))
    (short : ∀ p', (R.double.split Γ).IsWalk ((R.double.split Γ).tail (L.κ0 i)) p'
      ((R.double.split Γ).tail (L.κ1 i)) →
      (p.map (g ∘ Prod.fst)).sum ≤ (p'.map (g ∘ Prod.fst)).sum)
    (fin : (p.map (g ∘ Prod.fst)).sum ≠ ⊤) :
    ∃ S : L.Step, ∃ p₁ p₃, p = p₁ ++ (List.range S.n).map S.q ++ p₃ ∧
      (∀ z ∈ (List.range S.n).map S.q ++ p₃, ¬ C.atCopy Γ 0 ((R.double.split Γ).head z)) ∧
      ∀ z ∈ (List.range S.n).map S.q, ¬ C.atCopy Γ 1 ((R.double.split Γ).tail z) := by
  have hc0 : L.κ0 i ∈ liveBoundary L.κ0 L.κ1 L.xa L.xb L.ya L.yb L.La L.Lb := by
    unfold liveBoundary
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (mem_cornerSeg.2 ⟨i, h1, h2, rfl⟩)))
  have hgp := IsWalk.gcomp hp
  have hS0 : C.atCopy Γ 0 ((R.double.split Γ).tail (L.κ0 i)) :=
    (C.atCopy_tail L.sub).2 ⟨i, h2.trans L.xb_le, L.piece0 i h1 h2⟩
  have hS1 : C.atCopy Γ 1 ((R.double.split Γ).tail (L.κ1 i)) :=
    (C.atCopy_tail L.sub).2 ⟨i, h4.trans L.yb_le, L.piece1 i h3 h4⟩
  obtain ⟨pa, pb, s, rfl, hpa, hpb, hs, hnb⟩ := IsWalk.split_last (C.atCopy Γ 0) hp (Or.inl hS0)
  have hb1 : C.atCopy Γ 1 s ∨ ∃ z ∈ pb, C.atCopy Γ 1 ((R.double.split Γ).head z) := by
    rcases IsWalk.mem_heads hpb with e | e
    · exact Or.inl (by rw [← e]; exact hS1)
    · obtain ⟨z, hz, hz'⟩ := List.mem_map.1 e
      exact Or.inr ⟨z, hz, by rw [hz']; exact hS1⟩
  obtain ⟨Q, pc, s', rfl, hQ, hpc, hs', hnQ⟩ := IsWalk.split_first (C.atCopy Γ 1) hpb hb1
  have hQpos : 0 < Q.length := by
    rcases Q with _ | ⟨z, Q⟩
    · exfalso
      obtain rfl : s = s' := hQ
      obtain ⟨z0, hz0, t0, ht0, e0⟩ := hs
      rw [← hz0] at hs'
      obtain ⟨t1, ht1, e1⟩ := (C.atCopy_tail L.sub).1 hs'
      exact C.not_copy_both ht0 ht1 e0 e1
    · simp
  -- the first end
  have hq0 : Q[0] ∈ pa ++ (Q ++ pc) :=
    List.mem_append_right _ (List.mem_append_left _ (List.getElem_mem hQpos))
  have ht0 : (R.double.split Γ).tail Q[0] = s := hQ.tail_getElem_zero hQpos
  have hs0 : C.atCopy Γ 0 ((R.double.split Γ).tail Q[0]) := by rw [ht0]; exact hs
  obtain ⟨x, hxm, hx⟩ := (C.atCopy_tail L.sub).1 hs0
  have hx0 : L.xa ≤ x ∧ x ≤ L.xb ∧ fconnect (R.double.split Γ).rot Q[0] (L.κ0 x) := by
    rcases L.piece hR hC hc0 (hgp _ hq0).1 hxm hx with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (by decide)
  obtain ⟨hxa, hxb, hx'⟩ := hx0
  -- the last end
  have hlen : Q.length - 1 < Q.length := by omega
  have hql : Q[Q.length - 1] ∈ pa ++ (Q ++ pc) :=
    List.mem_append_right _ (List.mem_append_left _ (List.getElem_mem hlen))
  have htl : (R.double.split Γ).tail (R.double.rev Q[Q.length - 1]) = s' :=
    hQ.head_getElem_last hQpos
  have hs1 : C.atCopy Γ 1 ((R.double.split Γ).tail (R.double.rev Q[Q.length - 1])) := by
    rw [htl]; exact hs'
  obtain ⟨y, hym, hy⟩ := (C.atCopy_tail L.sub).1 hs1
  have hy0 : L.ya ≤ y ∧ y ≤ L.yb ∧
      fconnect (R.double.split Γ).rot (R.double.rev Q[Q.length - 1]) (L.κ1 y) := by
    rcases L.piece hR hC hc0 (hgp _ hql).2 hym hy with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h (by decide)
    · exact h
  obtain ⟨hya, hyb, hy'⟩ := hy0
  have es : (R.double.split Γ).tail (L.κ0 x) = s := by
    rw [← ht0]; exact (((R.double.split Γ).tail_eq_iff _ _).2 hx').symm
  have es' : (R.double.split Γ).tail (L.κ1 y) = s' := by
    rw [← htl]; exact (((R.double.split Γ).tail_eq_iff _ _).2 hy').symm
  -- simplicity
  have hndQ : (Q.map (R.double.split Γ).tail).Nodup :=
    (((List.sublist_append_left Q pc).trans (List.sublist_append_right pa _)).map _).nodup hnd
  have hlast : ∀ z ∈ Q, (R.double.split Γ).tail z ≠ s' := by
    intro z hz
    rcases pc with _ | ⟨w, pc⟩
    · obtain rfl : s' = (R.double.split Γ).tail (L.κ1 i) := hpc
      exact hne z (List.mem_append_right _ (List.mem_append_left _ hz))
    · have hw : (R.double.split Γ).tail w = s' := hpc.1
      have hnd' := ((List.sublist_append_right pa _).map (R.double.split Γ).tail).nodup hnd
      rw [List.map_append, List.nodup_append] at hnd'
      rw [← hw]
      exact hnd'.2.2 _ (List.mem_map_of_mem hz) _ (List.mem_map_of_mem List.mem_cons_self)
  -- the inner vertices are off the path
  have hin : ∀ j (hj : j < Q.length), 0 < j → ∀ t, t ≤ C.m → R.tail Q[j].1 ≠ C.v t := by
    intro j hj hj0 t ht hv
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rcases C.sector ht hv with h | h
    · refine hnb Q[j'] (List.mem_append_left _ (List.getElem_mem (by omega))) ?_
      rw [hQ.head_getElem j' hj]
      exact (C.atCopy_tail L.sub).2 ⟨t, ht, h⟩
    · exact hnQ Q[j' + 1] (List.getElem_mem hj) ((C.atCopy_tail L.sub).2 ⟨t, ht, h⟩)
  -- no edge of the path
  have hnoP : ∀ j (hj : j < Q.length), (Q[j].1, false) ∉ C.Γ := by
    intro j hj hmem
    obtain ⟨t, ht, hv⟩ := C.tail_of_mem_Γ hmem
    obtain ⟨t', ht', hv'⟩ := C.tail_of_mem_Γ (C.pair_Γ hmem)
    rcases Nat.lt_or_ge 1 Q.length with hn | hn
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · have e : (R.double.split Γ).tail (R.double.rev Q[0]) = (R.double.split Γ).tail Q[1] :=
          hQ.head_getElem 0 hn
        have e' : R.tail (R.rev Q[0].1) = R.tail Q[1].1 :=
          DiskChord.tail_fst (((R.double.split Γ).tail_eq_iff _ _).1 e)
        exact hin 1 hn (by omega) t' ht' (e'.symm.trans hv')
      · exact hin j hj hj0 t ht hv
    · obtain ⟨z, rfl⟩ := List.length_eq_one_iff.1 (by omega : Q.length = 1)
      obtain rfl : j = 0 := by simp at hj; omega
      have hz0 : fconnect C.cut.rot z (C.k 0 x) :=
        connect_trans (fconnect_of_split_subset L.sub (by simpa using hx')) (L.piece0 x hxa hxb)
      have hz1 : fconnect C.cut.rot (R.double.rev z) (C.k 1 y) :=
        connect_trans (fconnect_of_split_subset L.sub (by simpa using hy')) (L.piece1 y hya hyb)
      exact C.not_mem_Γ_of_sides hxm hym ((C.cut.tail_eq_iff _ _).2 hz0)
        ((C.cut.tail_eq_iff _ _).2 hz1) (by simpa using hmem)
  refine ⟨{
      x := x, y := y, hxa := hxa, hxb := hxb, hya := hya, hyb := hyb, n := Q.length
      q := fun j => Q.getD j (L.κ0 x), pos := hQpos, start := ?_, walk := ?_, stop := ?_
      simple := ?_, simple_last := ?_, inner := ?_, noP := ?_, short := ?_, fin := ?_ },
    pa, pc, ?_⟩
  · show fconnect _ (Q.getD 0 (L.κ0 x)) _
    rw [List.getD_eq_getElem (n := 0) _ _ hQpos]
    exact hx'
  · intro j hj
    show fconnect _ (R.double.rev (Q.getD j (L.κ0 x))) (Q.getD (j + 1) (L.κ0 x))
    rw [List.getD_eq_getElem (n := j) _ _ (by omega), List.getD_eq_getElem (n := j + 1) _ _ hj]
    exact ((R.double.split Γ).tail_eq_iff (R.double.rev Q[j]) Q[j + 1]).1 (hQ.head_getElem j hj)
  · show fconnect _ (R.double.rev (Q.getD (Q.length - 1) (L.κ0 x))) _
    rw [List.getD_eq_getElem (n := Q.length - 1) _ _ hlen]
    exact hy'
  · intro a b ha hb hab
    change fconnect _ (Q.getD a (L.κ0 x)) (Q.getD b (L.κ0 x)) at hab
    rw [List.getD_eq_getElem (n := a) _ _ ha, List.getD_eq_getElem (n := b) _ _ hb] at hab
    have e : (Q.map (R.double.split Γ).tail)[a]'(by simpa using ha) =
        (Q.map (R.double.split Γ).tail)[b]'(by simpa using hb) := by
      simp only [List.getElem_map]
      exact ((R.double.split Γ).tail_eq_iff _ _).2 hab
    exact hndQ.getElem_inj_iff.1 e
  · intro a ha hab
    change fconnect _ (Q.getD a (L.κ0 x)) _ at hab
    rw [List.getD_eq_getElem (n := a) _ _ ha] at hab
    exact hlast _ (List.getElem_mem ha)
      (by rw [← es']; exact ((R.double.split Γ).tail_eq_iff _ _).2 hab)
  · intro j hj0 hj t ht
    rw [List.getD_eq_getElem (n := j) _ _ hj]
    exact hin j hj hj0 t ht
  · intro j hj
    rw [List.getD_eq_getElem (n := j) _ _ hj]
    exact hnoP j hj
  · intro p' hp'
    rw [range_map_getD]
    have hp'' : (R.double.split Γ).IsWalk s p' s' := by rw [← es, ← es']; exact hp'
    have h := short _ (hpa.append (hp''.append hpc))
    simp only [List.map_append, List.sum_append] at h fin ⊢
    have ha : (pa.map (g ∘ Prod.fst)).sum ≠ ⊤ := (ENNReal.add_ne_top.1 fin).1
    have hc : (pc.map (g ∘ Prod.fst)).sum ≠ ⊤ := (ENNReal.add_ne_top.1 (ENNReal.add_ne_top.1 fin).2).2
    exact (ENNReal.add_le_add_iff_right hc).1 ((ENNReal.add_le_add_iff_left ha).1 h)
  · rw [range_map_getD]
    simp only [List.map_append, List.sum_append] at fin
    exact (ENNReal.add_ne_top.1 (ENNReal.add_ne_top.1 fin).2).1
  · refine ⟨by rw [range_map_getD, List.append_assoc], ?_, ?_⟩
    · rw [range_map_getD]; exact hnb
    · rw [range_map_getD]; exact hnQ

/-- **The step of a shortest walk.** A simple shortest walk of finite length from the vertex of
`κ0(i)` to the vertex of `κ1(i)` contains a step: its part from its last vertex at a copy `p_x^0` to
the first vertex at a copy `p_y^1` after it. -/
theorem exists_step (hR : R.Planar) (hC : R.Connected) {i : ℕ} (h1 : L.xa ≤ i) (h2 : i ≤ L.xb)
    (h3 : L.ya ≤ i) (h4 : i ≤ L.yb) {p : List (D × Bool)}
    (hp : (R.double.split Γ).IsWalk ((R.double.split Γ).tail (L.κ0 i)) p
      ((R.double.split Γ).tail (L.κ1 i)))
    (hnd : (p.map (R.double.split Γ).tail).Nodup)
    (hne : ∀ z ∈ p, (R.double.split Γ).tail z ≠ (R.double.split Γ).tail (L.κ1 i))
    (short : ∀ p', (R.double.split Γ).IsWalk ((R.double.split Γ).tail (L.κ0 i)) p'
      ((R.double.split Γ).tail (L.κ1 i)) →
      (p.map (g ∘ Prod.fst)).sum ≤ (p'.map (g ∘ Prod.fst)).sum)
    (fin : (p.map (g ∘ Prod.fst)).sum ≠ ⊤) :
    ∃ S : L.Step, ∃ p₁ p₃, p = p₁ ++ (List.range S.n).map S.q ++ p₃ := by
  obtain ⟨S, p₁, p₃, h, -⟩ := L.exists_step_sel hR hC h1 h2 h3 h4 hp hnd hne short fin
  exact ⟨S, p₁, p₃, h⟩

end Live

end CutPath

end RotSystem

end SsspFlow
