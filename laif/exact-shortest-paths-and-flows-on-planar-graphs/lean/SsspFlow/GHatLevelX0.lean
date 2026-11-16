import SsspFlow.GHatTheoremD

/-!
# The stored state of level `0` from local data

A node knows its name, its rotation list, the costs, modes and hosts of its darts, the bound `M`, the
number `m`, the name of the source node, and for each corner of each of its darts the indices `t`
with `z = κ0(t)` or `z = κ1(t)`, and the base values of the corner. From these it computes its stored
state of level `0` with no communication: whether a corner is a corner of the cut, the records and
token lengths of its darts, and the state of each corner for the top annulus, with the source corner
`κ0(m/2)` and the target corner `κ1(m/2)` when `m ≥ 2`.

* `X0In`: the local data of a node.
* `X0In.x0`: its stored state of level `0`.
* `RData.lvInv0_of_local`: this is the stored state of level `0` of every run on the cut.
* `RData.theoremD_from_local`: Theorem D as one algorithm of the message model from the local data.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

/-- The local data of a node for level `0`. -/
structure X0In (n : ℕ) where
  /-- The name of the node. -/
  me : Fin n
  /-- Its rotation list. -/
  rot : List (Fin n)
  /-- The costs of its darts. -/
  cw : Fin n → ℕ
  /-- The modes of its darts. -/
  mL : Fin n → Bool
  /-- The hosts of its darts. -/
  hT : Fin n → Bool
  /-- The bound `M`. -/
  bnd : ℕ
  /-- The number `m`. -/
  m : ℕ
  /-- The name of the source node. -/
  src : Fin n
  /-- The base values of the corners of its darts. -/
  gs : ℕ → (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞)
  /-- The indices of the corners of the darts into the node. -/
  kapI : Fin n → Bool → (ℕ → Bool) × (ℕ → Bool)
  /-- The indices of the corners of the darts out of the node. -/
  kapO : Fin n → Bool → (ℕ → Bool) × (ℕ → Bool)

namespace X0In

variable {n : ℕ}

open Classical in
/-- A corner with these indices is a corner of the cut. -/
noncomputable def inΓ (m : ℕ) (k : (ℕ → Bool) × (ℕ → Bool)) : Bool :=
  decide (∃ t, t ≤ m ∧ (k.1 t = true ∨ k.2 t = true))

/-- The record of the dart to `u`. -/
noncomputable def own (x : X0In n) (u : Fin n) : DInfo :=
  if u ∈ x.rot then
    ⟨inΓ x.m (x.kapO u false), inΓ x.m (x.kapO u true), x.mL u, x.hT u,
      inΓ x.m (x.kapO (x.rot.formPerm.symm u) true) && !x.mL (x.rot.formPerm.symm u)⟩
  else default

/-- The input of the node for the network of level `0`. -/
noncomputable def lvIn (x : X0In n) : LevelIn n :=
  ⟨x.me, x.rot, x.own,
    fun u l => if u ∈ x.rot then (if (l = .zero ↔ inΓ x.m (x.kapO u false) = false) then x.cw u else 0) else 0,
    x.bnd, RData.idEquiv (x.src, x.src, 0)⟩

open Classical in
/-- The state of a corner at level `0` and its code of a range, from its indices. -/
noncomputable def cst0 (m : ℕ) (k : (ℕ → Bool) × (ℕ → Bool)) : RData.CSt × ℕ∞ :=
  ({ inΓ := inΓ m k
     cA := decide (2 ≤ m) && (k.1 0 || k.2 0)
     cB := decide (2 ≤ m) && (k.1 m || k.2 m)
     src := decide (2 ≤ m) && k.1 (m / 2)
     tgt := decide (2 ≤ m) && k.2 (m / 2) },
    if 2 ≤ m ∧ k.2 (m / 2) = true then ((Nat.pair 0 m : ℕ) : ℕ∞) else ⊤)

/-- The stored state of level `0`. -/
noncomputable def x0 (x : X0In n) : LvX n :=
  (x.lvIn, x.m, x.gs, x.kapI, fun u b => cst0 x.m (x.kapO u b), fun u b => cst0 x.m (x.kapI u b))

end X0In

namespace RData

variable {n : ℕ} {N : Net (Fin n)} {Cp : N.toRot.dual.CutPath} {cc : N.G.Dart → ℕ}
  {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
  {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}

/-- The bit of a corner of the cut from its indices. -/
theorem inΓ_iff {z : N.G.Dart × Bool} {k : (ℕ → Bool) × (ℕ → Bool)}
    (hk : ∀ t, (k.1 t = true ↔ z = Cp.k 0 t) ∧ (k.2 t = true ↔ z = Cp.k 1 t)) :
    X0In.inΓ Cp.m k = decide (z ∈ Cp.Γ) := by
  unfold X0In.inΓ
  refine decide_eq_decide.2 ?_
  rw [Cp.mem_Γ]
  constructor
  · rintro ⟨t, ht, h | h⟩
    · exact ⟨0, t, ht, (hk t).1.1 h⟩
    · exact ⟨1, t, ht, (hk t).2.1 h⟩
  · rintro ⟨σ, t, ht, h⟩
    fin_cases σ
    · exact ⟨t, ht, .inl ((hk t).1.2 h)⟩
    · exact ⟨t, ht, .inr ((hk t).2.2 h)⟩

/-- The list of level `0` of a run on the cut: the top annulus with its middle, when `m ≥ 2`. -/
theorem levelQ_zero (r : CutPath.Run hR hC hgc Cp.Γ (Cp.liveOne (Nat.cast ∘ cc)) 0 Cp.m) :
    r.levelQ 0 = if 2 ≤ Cp.m then [(⟨Cp.Γ, Cp.liveOne (Nat.cast ∘ cc)⟩, Cp.m / 2)] else [] := by
  unfold CutPath.Run.levelQ
  rw [CutPath.Run.subs_zero]
  by_cases h : 2 ≤ Cp.m
  · simp [h]
  · simp [h]

/-- **The state of a corner at level `0`** from its indices. -/
theorem cst0_eq (r : CutPath.Run hR hC hgc Cp.Γ (Cp.liveOne (Nat.cast ∘ cc)) 0 Cp.m)
    {z : N.G.Dart × Bool} {k : (ℕ → Bool) × (ℕ → Bool)}
    (hk : ∀ t, (k.1 t = true ↔ z = Cp.k 0 t) ∧ (k.2 t = true ↔ z = Cp.k 1 t)) :
    X0In.cst0 Cp.m k = (lvCSt r 0 z, lvV8 r 0 z) := by
  have hrng : rngA r 0 ⟨Cp.Γ, Cp.liveOne (Nat.cast ∘ cc)⟩ = (0, Cp.m) :=
    rngA_sub r 0 (s := ⟨⟨Cp.Γ, Cp.liveOne (Nat.cast ∘ cc)⟩, (0, Cp.m), r⟩)
      (by rw [CutPath.Run.subs_zero]; exact List.mem_singleton_self _)
  have b1 : ∀ t, k.1 t = decide (z = Cp.k 0 t) := fun t => by
    rw [Bool.eq_iff_iff, decide_eq_true_iff]; exact (hk t).1
  have b2 : ∀ t, k.2 t = decide (z = Cp.k 1 t) := fun t => by
    rw [Bool.eq_iff_iff, decide_eq_true_iff]; exact (hk t).2
  unfold X0In.cst0 lvCSt lvV8
  rw [levelQ_zero r, inΓ_iff hk, CutPath.Run.steps_zero, Finset.union_empty]
  by_cases h : 2 ≤ Cp.m
  · simp only [h, ite_true, List.mem_singleton, exists_eq_left, List.map_cons, List.map_nil,
      CutPath.Live.CornerA, CutPath.Live.CornerB, CutPath.liveOne, List.not_mem_nil, or_false, false_or, b1, b2,
      decide_true, Bool.true_and, qEnd, hrng]
    refine Prod.ext (CSt.ext' rfl ?_ ?_ rfl rfl) ?_
    · by_cases h1 : z = Cp.k0 0 <;> by_cases h2 : z = Cp.k1 0 <;> simp [h1, h2]
    · by_cases h1 : z = Cp.k0 Cp.m <;> by_cases h2 : z = Cp.k1 Cp.m <;> simp [h1, h2]
    · simp only [iInf_iInf_eq_left, ite_true]
      simp only [CutPath.liveOne] at hrng
      by_cases hz : z = Cp.k1 (Cp.m / 2) <;> simp [hz, hrng]
  · simp only [h, ite_false, List.not_mem_nil, false_and, exists_false, decide_false, Bool.false_and,
      iInf_false, iInf_top, false_and]
    rfl

variable (hN : ∀ u, ∃ w, N.G.Adj u w) (modeL hostT : N.G.Dart → Bool)
  (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d) (hE : ExactSsspBound) (K D M : ℕ)

/-- **The stored state of level `0` from local data.** If every node holds its local data, then the
stored states it computes are the stored state of level `0` of every run on the cut. -/
theorem lvInv0_of_local (r₀ : CutPath.Run hR hC hgc Cp.Γ (Cp.liveOne (Nat.cast ∘ cc)) 0 Cp.m) (w₀ : Fin n)
    (x : Fin n → X0In n) (hme : ∀ w, (x w).me = w) (hrot : ∀ w, (x w).rot = N.rotList w)
    (hcw : ∀ d : N.G.Dart, (x d.fst).cw d.snd = cc d) (hmL : ∀ d : N.G.Dart, (x d.fst).mL d.snd = modeL d)
    (hhT : ∀ d : N.G.Dart, (x d.fst).hT d.snd = hostT d) (hb : ∀ w, (x w).bnd = M)
    (hm : ∀ w, (x w).m = Cp.m) (hsrc : ∀ w, (x w).src = w₀)
    (hgs : ∀ k, k ≤ 3 → ∀ (d : N.G.Dart) b, ((x d.fst).gs k).1 d.snd b = gsBase Cp k (d, b) ∧
      ((x d.snd).gs k).2 d.fst b = gsBase Cp k (d, b))
    (hkI : ∀ (d : N.G.Dart) b t, ((((x d.snd).kapI d.fst b).1 t = true ↔ (d, b) = Cp.k 0 t) ∧
      (((x d.snd).kapI d.fst b).2 t = true ↔ (d, b) = Cp.k 1 t)))
    (hkO : ∀ (d : N.G.Dart) b t, ((((x d.fst).kapO d.snd b).1 t = true ↔ (d, b) = Cp.k 0 t) ∧
      (((x d.fst).kapO d.snd b).2 t = true ↔ (d, b) = Cp.k 1 t))) :
    LvInv hN modeL hostT hhost hE K D M r₀ w₀ 0 (fun w => (x w).x0) := by
  have hincS : ∀ d, d ∈ (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0).inc ↔ (d, false) ∈ Cp.Γ := fun d => by
    simp [lvS, CutPath.Run.data, RData.ofCorners, CutPath.Run.steps_zero]
  have hcutS : ∀ c, c ∈ (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0).cut ↔ (c, true) ∈ Cp.Γ := fun c => by
    simp [lvS, CutPath.Run.data, RData.ofCorners, CutPath.Run.steps_zero]
  have hmodeS : ∀ d, (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0).modeL d = modeL d := fun d => by
    simp [lvS, CutPath.Run.data, RData.ofCorners]
  have hhostS : ∀ d, (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0).hostT d = hostT d := fun d => by
    simp [lvS, CutPath.Run.data, RData.ofCorners]
  have hO : ∀ (d : N.G.Dart) b, X0In.inΓ (x d.fst).m ((x d.fst).kapO d.snd b) = decide ((d, b) ∈ Cp.Γ) :=
    fun d b => by rw [hm]; exact inΓ_iff (hkO d b)
  have hown : ∀ d : N.G.Dart, (x d.fst).own d.snd = (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0).dinfo d := by
    intro d
    have hmem : d.snd ∈ (x d.fst).rot := by rw [hrot]; exact (N.mem_rotList _ _).2 d.adj
    unfold X0In.own
    rw [ite_cond_eq_true _ _ (eq_true hmem)]
    have e1 : (x d.fst).rot.formPerm.symm d.snd = (N.rotPerm.symm d).snd := by rw [hrot]; rfl
    rw [e1]
    have h1 : X0In.inΓ (x d.fst).m ((x d.fst).kapO (N.rotPerm.symm d).snd true) =
        decide ((N.rotPerm.symm d, true) ∈ Cp.Γ) := hO (N.rotPerm.symm d) true
    have h2 : (x d.fst).mL (N.rotPerm.symm d).snd = modeL (N.rotPerm.symm d) := hmL (N.rotPerm.symm d)
    rw [h1, h2, hO d false, hO d true, hmL d, hhT d]
    unfold dinfo MovB
    have ht : N.toRot.tailCorner d = N.rotPerm.symm d := rfl
    rw [ht]
    simp only [DInfo.mk.injEq, hincS, hcutS, hmodeS, hhostS]
    simp only [true_and]
    cases modeL (N.rotPerm.symm d) <;> simp
  have hL1 : ∀ w, (x w).x0.1 = (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0).levelIn hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0)) M ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0).starV hN w₀) w := by
    intro w
    show (x w).lvIn = _
    unfold X0In.lvIn levelIn
    rw [starV_name, hsrc]
    simp only [LevelIn.mk.injEq]
    refine ⟨hme w, hrot w, ?_, ?_, hb w, trivial⟩
    · funext u
      by_cases h : N.G.Adj w u
      · rw [show (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0).dinfoAt w u = (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0).dinfo ⟨(w, u), h⟩ from (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0).dinfoAt_dart ⟨(w, u), h⟩]
        exact hown ⟨(w, u), h⟩
      · have hu : u ∉ (x w).rot := by rw [hrot]; exact fun hm => h ((N.mem_rotList _ _).1 hm)
        unfold X0In.own dinfoAt
        rw [ite_cond_eq_false _ _ (eq_false hu), dite_eq_right_of_eq_false (eq_false h)]
    · funext u l
      rw [(lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0).lamAt_cc cc (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0)) (fun _ => rfl)]
      by_cases h : N.G.Adj w u
      · have hu : u ∈ (x w).rot := by rw [hrot]; exact (N.mem_rotList _ _).2 h
        rw [ite_cond_eq_true _ _ (eq_true hu), dite_eq_left_of_eq_true (eq_true h)]
        have hw : X0In.inΓ (x w).m ((x w).kapO u false) = decide (((⟨(w, u), h⟩ : N.G.Dart), false) ∈ Cp.Γ) :=
          hO ⟨(w, u), h⟩ false
        have hc : (x w).cw u = cc ⟨(w, u), h⟩ := hcw ⟨(w, u), h⟩
        rw [hw, hc]
        unfold IsTok
        refine if_congr ?_ rfl rfl
        rw [hincS]
        simp
      · have hu : u ∉ (x w).rot := by rw [hrot]; exact fun hm => h ((N.mem_rotList _ _).1 hm)
        rw [ite_cond_eq_false _ _ (eq_false hu), dite_eq_right_of_eq_false (eq_false h)]
  refine ⟨hL1, hm, fun k hk d b => hgs k hk d b, fun d b => ⟨?_, ?_⟩, fun d b t => hkI d b t⟩
  · show X0In.cst0 (x d.fst).m ((x d.fst).kapO d.snd b) = _
    rw [hm]
    exact cst0_eq _ (hkO d b)
  · show X0In.cst0 (x d.snd).m ((x d.snd).kapI d.fst b) = _
    rw [hm]
    exact cst0_eq _ (hkI d b)

end RData

open Classical Cslib.Congest.Algorithm in
/-- **Theorem D as one algorithm of the message model, from local data.** Let the network be planar
and connected with symmetric capacities `c₀`, `K₀` exceed the number of darts, and the cut path be
shortest for the lengths `K₀ c₀ + 1`. Every node starts with its
local data: its name, rotation list, the costs `K₀ c₀ + 1`, modes and hosts of its darts, the bound `M`,
the number `m`, the name of a source node, and the indices and base values of the corners of its darts
on a shortest cut path. After `T` rounds every node holds a number `v` with `v / K₀` the minimum
`st`-cut for the capacities `c₀`. -/
theorem RData.theoremD_from_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (X0In n) σ
        (4 * (C * logN (n * (n * 21)) ^ c + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (out : Fin n → σ → ℕ),
    T ≤ (2 * logN n + 1) * (110 + 68 * (C * logN (n * (n * 21)) ^ c * (12 * D + 16))) + D ∧
    ∀ (N : Net (Fin n)) (hN : ∀ u, ∃ w, N.G.Adj u w) (Cp : N.toRot.dual.CutPath) (c₀ : N.G.Dart → ℕ)
      (K₀ : ℕ) (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d) (M : ℕ)
      (x : Fin n → X0In n) (w₀ : Fin n),
      N.toRot.Planar → N.toRot.Connected → N.DiamLE D → CutDuality N.G.Dart →
      (∀ d, c₀ (N.toRot.rev d) = c₀ d) → Fintype.card N.G.Dart < K₀ →
      (∀ q, N.toRot.dual.IsWalk (Cp.v 0) q (Cp.v Cp.m) →
        Cp.pos (fun x => K₀ * c₀ x + 1) Cp.m ≤ (q.map fun x => K₀ * c₀ x + 1).sum) →
      (∀ d, K₀ * c₀ d + 1 ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ t, t ≤ Cp.m → Cp.lamD (Nat.cast ∘ fun x => K₀ * c₀ x + 1) t < M) → (Cp.m + 2) ^ 8 ≤ M →
      (∀ w, (x w).me = w) → (∀ w, (x w).rot = N.rotList w) →
      (∀ d : N.G.Dart, (x d.fst).cw d.snd = K₀ * c₀ d + 1) → (∀ d : N.G.Dart, (x d.fst).mL d.snd = modeL d) →
      (∀ d : N.G.Dart, (x d.fst).hT d.snd = hostT d) → (∀ w, (x w).bnd = M) →
      (∀ w, (x w).m = Cp.m) → (∀ w, (x w).src = w₀) →
      (∀ k, k ≤ 3 → ∀ (d : N.G.Dart) b, ((x d.fst).gs k).1 d.snd b = RData.gsBase Cp k (d, b) ∧
        ((x d.snd).gs k).2 d.fst b = RData.gsBase Cp k (d, b)) →
      (∀ (d : N.G.Dart) b t, ((((x d.snd).kapI d.fst b).1 t = true ↔ (d, b) = Cp.k 0 t) ∧
        (((x d.snd).kapI d.fst b).2 t = true ↔ (d, b) = Cp.k 1 t))) →
      (∀ (d : N.G.Dart) b t, ((((x d.fst).kapO d.snd b).1 t = true ↔ (d, b) = Cp.k 0 t) ∧
        (((x d.fst).kapO d.snd b).2 t = true ↔ (d, b) = Cp.k 1 t))) →
      ∀ w, IsLeast (N.toRot.cutVals c₀ (N.toRot.tail Cp.cs) (N.toRot.tail Cp.ct))
        (out w (A.run N.G x T w) / K₀) := by
  obtain ⟨C, c, h⟩ := RData.theoremD_local hE K
  refine ⟨C, c, fun n D => ?_⟩
  obtain ⟨σ, A, T, out, hT, hA⟩ := h n D
  refine ⟨_, A.keep (fun _ (y : X0In n) => y.x0), T, fun w s => out w s.2, hT, ?_⟩
  intro N hN Cp c₀ K₀ modeL hostT hhost M x w₀ hP hc hD hDual hcr₀ hK hPath hcb hM hMl hM8
    hme hrot hcw hmL hhT hb hm hsrc hgs hkI hkO w
  have hR : N.toRot.dual.Planar := N.toRot.planar_dual.2 hP
  have hC : N.toRot.dual.Connected := N.toRot.connected_dual.2 hc
  have hgc : ∀ x, (Nat.cast ∘ (fun x => K₀ * c₀ x + 1) : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) =
      (Nat.cast ∘ (fun x => K₀ * c₀ x + 1)) x := fun x => by
    simp only [Function.comp_apply, dual_rev, hcr₀]
  have hg₀ : ∀ x, K₀ * c₀ (N.toRot.dual.rev x) + 1 = K₀ * c₀ x + 1 := fun x => by rw [dual_rev, hcr₀]
  have hpos : ∀ t, t < Cp.m → 1 ≤ K₀ * c₀ (Cp.e t) + 1 := fun _ _ => Nat.le_add_left 1 _
  obtain ⟨⟨r₀⟩, -⟩ := CutPath.recursion_cut (C := Cp) hR hC hgc hg₀ hpos hPath
  simp only [run_keep]
  exact hA N hN Cp c₀ K₀ hR hC hgc modeL hostT hhost M (fun w => (x w).x0) w₀ hP hc hD hDual hcr₀ hK hPath
    hcb hM hMl hM8 ⟨r₀, RData.lvInv0_of_local hN modeL hostT hhost hE K D M r₀ w₀ x hme hrot hcw hmL hhT hb
      hm hsrc hgs hkI hkO⟩ w

end RotSystem

end SsspFlow
