import SsspFlow.Glue

/-!
# Composing disks

A family of disks on the components of the split of a planar connected map at `Γ'`, in place of those
components. The hub walks over the distances of the disks satisfy the condition (M) on each cycle of
`ψ` at a smaller set `Γ ⊆ Γ'` (`hubDist_monge`). The proof glues the disks along the rotation of the
map, by `replace_planar`, and splits the result at `Γ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal

namespace SsspFlow

open FourColor

/-! ### Components of a disjoint family -/

section NCompSigma

variable {ι : Type*} {E : ι → Type*}

theorem connect_sigma_fst {e : (Σ i, E i) → (Σ i, E i) → Prop} (hf : ∀ z z', e z z' → z.1 = z'.1)
    {z z' : Σ i, E i} (h : connect e z z') : z.1 = z'.1 := by
  induction h with
  | refl => rfl
  | tail _ h2 ih => exact ih.trans (hf _ _ h2)

theorem connect_sigma_iff {e : (Σ i, E i) → (Σ i, E i) → Prop} {e' : ∀ i, E i → E i → Prop}
    (h : ∀ i a b, e ⟨i, a⟩ ⟨i, b⟩ ↔ e' i a b) (hf : ∀ z z', e z z' → z.1 = z'.1) (i : ι)
    (a b : E i) : connect e ⟨i, a⟩ ⟨i, b⟩ ↔ connect (e' i) a b := by
  constructor
  · intro h1
    have key : ∀ z, connect e ⟨i, a⟩ z → ∃ c, z = ⟨i, c⟩ ∧ connect (e' i) a c := by
      intro z hz
      induction hz with
      | refl => exact ⟨a, rfl, connect_refl a⟩
      | @tail x y _ hxy ih =>
        obtain ⟨c, rfl, hc⟩ := ih
        obtain ⟨j, d⟩ := y
        obtain rfl : i = j := hf _ _ hxy
        exact ⟨d, rfl, connect_trans hc (connect_of_rel ((h _ _ _).1 hxy))⟩
    obtain ⟨c, hc, h2⟩ := key _ h1
    obtain rfl : b = c := sigma_mk_injective hc
    exact h2
  · intro h1
    induction h1 with
    | refl => exact connect_refl _
    | tail _ h2 ih => exact connect_trans ih (connect_of_rel ((h _ _ _).2 h2))

variable [Fintype ι] [∀ i, Finite (E i)]

/-- The components of a disjoint family are those of its parts. -/
theorem nComp_sigma {e : (Σ i, E i) → (Σ i, E i) → Prop} {e' : ∀ i, E i → E i → Prop}
    (hs : ConnectSym e) (h : ∀ i a b, e ⟨i, a⟩ ⟨i, b⟩ ↔ e' i a b)
    (hf : ∀ z z', e z z' → z.1 = z'.1) :
    nComp e Set.univ = ∑ i, nComp (e' i) Set.univ := by
  classical
  have hk := connect_sigma_iff h hf
  have hs' : ∀ i, ConnectSym (e' i) := fun i a b hab =>
    (hk i b a).1 (hs _ _ ((hk i a b).2 hab))
  have h1 : nComp e Set.univ =
      ((fun z : Σ i, E i => (⟨z.1, comp (e' z.1) z.2⟩ : Σ i, Set (E i))) '' Set.univ).ncard := by
    refine ncard_image_eq_of_ker _ _ ?_
    rintro ⟨i, a⟩ _ ⟨j, b⟩ _
    rw [comp_eq_iff hs]
    constructor
    · intro hab
      obtain rfl : i = j := connect_sigma_fst hf hab
      have h2 : comp (e' i) a = comp (e' i) b := (comp_eq_iff (hs' i)).2 ((hk i a b).1 hab)
      exact congrArg (Sigma.mk i) h2
    · intro hab
      have h2 := (Sigma.mk.inj_iff.1 hab)
      obtain ⟨rfl, h3⟩ := h2
      exact (hk i a b).2 ((comp_eq_iff (hs' i)).1 (eq_of_heq h3))
  have hfin : ∀ i, (comp (e' i) '' (Set.univ : Set (E i))).Finite := fun i =>
    Set.Finite.image _ Set.finite_univ
  have h2 : ((fun z : Σ i, E i => (⟨z.1, comp (e' z.1) z.2⟩ : Σ i, Set (E i))) '' Set.univ) =
      ↑(Finset.univ.sigma fun i => (hfin i).toFinset) := by
    ext ⟨i, S⟩
    simp only [Set.image_univ, Set.mem_range, Finset.coe_sigma, Finset.coe_univ, Set.mem_sigma_iff,
      Set.mem_univ, true_and, Set.Finite.coe_toFinset, Set.mem_image]
    constructor
    · rintro ⟨⟨j, a⟩, h3⟩
      obtain ⟨rfl, h4⟩ := Sigma.mk.inj_iff.1 h3
      exact ⟨a, eq_of_heq h4⟩
    · rintro ⟨a, rfl⟩
      exact ⟨⟨i, a⟩, rfl⟩
  rw [h1, h2, Set.ncard_coe_finset, Finset.card_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Set.ncard_eq_toFinset_card _ (hfin i)]
  rfl

end NCompSigma

/-! ### Transport of hub walks -/

section HubCorr

variable {D : Type*} [DecidableEq D] {D' : Type*} [DecidableEq D'] {Γ : Finset D} {Γ' : Finset D'}

private theorem hubDist_le_of_walk {β : Γ' ≃ Γ} {w' : D' → D' → ℝ≥0∞} {w : D → D → ℝ≥0∞}
    (hw : ∀ a' a b' b, Corr β a' a → Corr β b' b → w a b ≤ w' a' b') :
    ∀ {a' b' : D'} (c : Walk (fun _ _ => True) a' b'), (∀ z ∈ c.support, z ∈ (Γ' : Set D')) →
      ∀ a b, Corr β a' a → Corr β b' b → hubDist Γ w a b ≤ c.wt w'
  | _, _, .nil _, _, a, b, ha, hb => by
    obtain rfl := ha.right_unique hb
    have := ha.symm.left_unique ha.symm
    rw [hubDist_self_le (Γ := Γ) (Finset.coe_mem (β ⟨_, ha.1⟩) |> fun h => by
      obtain ⟨h1, h2⟩ := ha
      rw [← h2]
      exact h)]
    simp
  | a', _, .cons (b := m') _ c, hc, a, b, ha, hb => by
    have hm : ∀ z ∈ c.support, z ∈ (Γ' : Set D') := fun z hz => hc z (List.mem_cons_of_mem _ hz)
    have hm' : m' ∈ Γ' := hm _ c.start_mem
    have hcorr : Corr β m' (β ⟨m', hm'⟩) := ⟨hm', rfl⟩
    have h1 := hubDist_le_of_walk hw c hm _ _ hcorr hb
    have haΓ : a ∈ Γ := by
      obtain ⟨h1, h2⟩ := ha
      rw [← h2]
      exact (β ⟨a', h1⟩).2
    simp only [Walk.wt_cons]
    exact (hubDist_triangle w a _ b).trans (add_le_add
      ((hubDist_le_step haΓ (β ⟨m', hm'⟩).2).trans (hw _ _ _ _ ha hcorr)) h1)

/-- Hub walks along a bijection of the marked corners. -/
theorem hubDist_corr {β : Γ' ≃ Γ} {w' : D' → D' → ℝ≥0∞} {w : D → D → ℝ≥0∞}
    (hw : ∀ a' a b' b, Corr β a' a → Corr β b' b → w' a' b' = w a b) {a' b' : D'} {a b : D}
    (ha : Corr β a' a) (hb : Corr β b' b) : hubDist Γ' w' a' b' = hubDist Γ w a b := by
  apply le_antisymm
  · simp only [hubDist, dist, le_iInf_iff]
    intro c hc
    have := hubDist_le_of_walk (β := β.symm) (w' := w) (w := w')
      (fun x' x y' y hx hy => (hw _ _ _ _ hx.symm hy.symm).le) c hc a' b' ha.symm hb.symm
    exact this
  · simp only [hubDist, dist, le_iInf_iff]
    intro c hc
    exact hubDist_le_of_walk (fun x' x y' y hx hy => (hw _ _ _ _ hx hy).ge) c hc a b ha hb

end HubCorr

/-! ### First returns along a bijection -/

section CorrReturn

variable {D : Type*} [Fintype D] [DecidableEq D] {D' : Type*} [Fintype D'] [DecidableEq D']
  {Γ : Finset D} {Γ' : Finset D'}

private theorem trail_corr {β : Γ' ≃ Γ} {f' : Equiv.Perm D'} {f : Equiv.Perm D}
    (hc : ConjVia β f' f) {T' : Finset D'} {T : Finset D}
    (hT : ∀ x' x, Corr β x' x → (x' ∈ T' ↔ x ∈ T)) {y z : D} (h : Trail f T y z) :
    ∀ y', Corr β y' y → ∃ z', Corr β z' z ∧ Trail f' T' y' z' := by
  induction h with
  | here hy =>
    intro y' h1
    exact ⟨y', h1, Trail.here ((hT _ _ h1).2 hy)⟩
  | step hy _ ih =>
    intro y' h1
    obtain ⟨z', h2, h3⟩ := ih _ (hc _ _ h1)
    exact ⟨z', h2, Trail.step (fun h => hy ((hT _ _ h1).1 h)) h3⟩

/-- First returns of matching permutations to matching sets match. -/
theorem conjVia_firstReturn {β : Γ' ≃ Γ} {f' : Equiv.Perm D'} {f : Equiv.Perm D}
    (hc : ConjVia β f' f) {T' : Finset D'} {T : Finset D}
    (hT : ∀ x' x, Corr β x' x → (x' ∈ T' ↔ x ∈ T)) :
    ConjVia β (firstReturn f' T') (firstReturn f T) := by
  intro x' x h
  by_cases hx : x ∈ T
  · obtain ⟨z', h2, h3⟩ := trail_corr hc hT (firstReturn_trail f hx) _ (hc _ _ h)
    have hx' : x' ∈ T' := (hT _ _ h).2 hx
    rw [firstReturn_eq_of_trail _ hx' h3]
    exact h2
  · rw [firstReturn_of_not_mem _ hx, firstReturn_of_not_mem _ (fun h' => hx ((hT _ _ h).1 h'))]
    exact h

end CorrReturn

namespace RotSystem

/-! ### The disjoint union of a family of maps -/

section SigmaMap

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*} [∀ i, Fintype (E i)]
  [∀ i, DecidableEq (E i)] (K : ∀ i, RotSystem (E i))

/-- The disjoint union of a family of rotation systems. -/
def sigmaMap : RotSystem (Σ i, E i) where
  rev z := ⟨z.1, (K z.1).rev z.2⟩
  rev_rev z := by
    obtain ⟨i, x⟩ := z
    exact congrArg (Sigma.mk i) ((K i).rev_rev x)
  rev_ne z h := by
    obtain ⟨i, x⟩ := z
    exact (K i).rev_ne x (sigma_mk_injective h)
  rot := Equiv.sigmaCongrRight fun i => (K i).rot

theorem sigmaMap_rev (i : ι) (x : E i) : (sigmaMap K).rev ⟨i, x⟩ = ⟨i, (K i).rev x⟩ := rfl

theorem sigmaMap_rot (i : ι) (x : E i) : (sigmaMap K).rot ⟨i, x⟩ = ⟨i, (K i).rot x⟩ := rfl

theorem sigmaMap_face (i : ι) (x : E i) :
    (sigmaMap K).facePerm ⟨i, x⟩ = ⟨i, (K i).facePerm x⟩ := rfl

/-- The links of the union stay in one part. -/
private theorem sigma_glink_fst (z z' : Σ i, E i) (h : (sigmaMap K).toHypermap.glink z z') :
    z.1 = z'.1 := by
  obtain ⟨i, x⟩ := z
  rcases h with rfl | rfl | rfl <;> rfl

private theorem sigma_glink_iff (i : ι) (a b : E i) :
    (sigmaMap K).toHypermap.glink ⟨i, a⟩ ⟨i, b⟩ ↔ (K i).toHypermap.glink a b := by
  simp only [Hypermap.glink]
  have hinj : Function.Injective (Sigma.mk i : E i → Σ i, E i) := sigma_mk_injective
  exact or_congr hinj.eq_iff (or_congr hinj.eq_iff hinj.eq_iff)

/-- Walks through the components of the union. -/
theorem sigmaMap_gcomp_iff (i : ι) (a b : E i) :
    (sigmaMap K).toHypermap.gcomp ⟨i, a⟩ ⟨i, b⟩ ↔ (K i).toHypermap.gcomp a b :=
  connect_sigma_iff (sigma_glink_iff K) (sigma_glink_fst K) i a b

theorem sigmaMap_gcomp_fst {z z' : Σ i, E i} (h : (sigmaMap K).toHypermap.gcomp z z') :
    z.1 = z'.1 :=
  connect_sigma_fst (sigma_glink_fst K) h

private theorem fcard_sigma (f : ∀ i, Equiv.Perm (E i)) {F : (Σ i, E i) → (Σ i, E i)}
    (hF : ∀ i x, F ⟨i, x⟩ = ⟨i, f i x⟩) (hinj : Function.Injective F) :
    fcard F Set.univ = ∑ i, fcard (f i) Set.univ := by
  refine nComp_sigma (fconnect_sym hinj) (fun i a b => ?_) ?_
  · show F ⟨i, a⟩ = ⟨i, b⟩ ↔ f i a = b
    rw [hF]
    exact sigma_mk_injective.eq_iff
  · rintro ⟨i, a⟩ z' rfl
    rw [hF]

/-- The union of planar maps is planar. -/
theorem sigmaMap_planar (h : ∀ i, (K i).Planar) : (sigmaMap K).Planar := by
  have hE : ∀ i, (K i).toHypermap.eulerLhs = (K i).toHypermap.eulerRhs := by
    intro i
    have h1 := (K i).toHypermap.evenGenus
    have h2 : (K i).toHypermap.genus = 0 := h i
    unfold Hypermap.EvenGenus at h1
    omega
  have hC : nComp (sigmaMap K).toHypermap.glink Set.univ =
      ∑ i, nComp (K i).toHypermap.glink Set.univ :=
    nComp_sigma (sigmaMap K).toHypermap.glinkC (sigma_glink_iff K) (sigma_glink_fst K)
  have h1 : (sigmaMap K).toHypermap.eulerLhs = ∑ i, (K i).toHypermap.eulerLhs := by
    simp only [Hypermap.eulerLhs]
    rw [hC, Fintype.card_sigma, Finset.sum_add_distrib, Finset.mul_sum]
  have hEd : fcard (sigmaMap K).toHypermap.edge Set.univ =
      ∑ i, fcard (K i).toHypermap.edge Set.univ :=
    fcard_sigma (fun i => (K i).revPerm) (fun _ _ => rfl) (sigmaMap K).toHypermap.edgeI
  have hNo : fcard (sigmaMap K).toHypermap.node Set.univ =
      ∑ i, fcard (K i).toHypermap.node Set.univ :=
    fcard_sigma (fun i => (K i).rot) (fun _ _ => rfl) (sigmaMap K).toHypermap.nodeI
  have hFa : fcard (sigmaMap K).toHypermap.face Set.univ =
      ∑ i, fcard (K i).toHypermap.face Set.univ :=
    fcard_sigma (fun i => (K i).facePerm) (fun _ _ => rfl) (sigmaMap K).toHypermap.faceI
  have h2 : (sigmaMap K).toHypermap.eulerRhs = ∑ i, (K i).toHypermap.eulerRhs := by
    simp only [Hypermap.eulerRhs]
    rw [hEd, hNo, hFa, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  show (sigmaMap K).toHypermap.genus = 0
  simp only [Hypermap.genus]
  rw [h1, h2, Finset.sum_congr rfl fun i _ => hE i]
  simp

/-! ### Marked corners of a family of disks -/

section Family

variable {l : ∀ i, List (E i)}

/-- The marked corners of a family of disks. -/
def sigmaPorts (l : ∀ i, List (E i)) : Finset (Σ i, E i) := Finset.univ.sigma fun i => (l i).toFinset

theorem mem_sigmaPorts {i : ι} {x : E i} : (⟨i, x⟩ : Σ i, E i) ∈ sigmaPorts l ↔ x ∈ l i := by
  simp [sigmaPorts]

private theorem trail_sigma {f : ∀ i, Equiv.Perm (E i)} {F : Equiv.Perm (Σ i, E i)}
    (hF : ∀ i x, F ⟨i, x⟩ = ⟨i, f i x⟩) {i : ι} {y z : E i} (h : Trail (f i) (l i).toFinset y z) :
    Trail F (sigmaPorts l) ⟨i, y⟩ ⟨i, z⟩ := by
  induction h with
  | here hy => exact Trail.here (mem_sigmaPorts.2 (List.mem_toFinset.1 hy))
  | step hy _ ih =>
    refine Trail.step (fun h => hy (List.mem_toFinset.2 (mem_sigmaPorts.1 h))) ?_
    rw [hF]
    exact ih

theorem firstReturn_sigma {f : ∀ i, Equiv.Perm (E i)} {F : Equiv.Perm (Σ i, E i)}
    (hF : ∀ i x, F ⟨i, x⟩ = ⟨i, f i x⟩) (i : ι) (x : E i) :
    firstReturn F (sigmaPorts l) ⟨i, x⟩ = ⟨i, firstReturn (f i) (l i).toFinset x⟩ := by
  by_cases hx : x ∈ (l i).toFinset
  · refine firstReturn_eq_of_trail _ (mem_sigmaPorts.2 (List.mem_toFinset.1 hx)) ?_
    rw [hF]
    exact trail_sigma hF (firstReturn_trail (f i) hx)
  · rw [firstReturn_of_not_mem _ hx, firstReturn_of_not_mem _
      (fun h => hx (List.mem_toFinset.2 (mem_sigmaPorts.1 h)))]

private theorem fconnect_sigma {f : ∀ i, Equiv.Perm (E i)} {F : Equiv.Perm (Σ i, E i)}
    (hF : ∀ i x, F ⟨i, x⟩ = ⟨i, f i x⟩) (i : ι) (a b : E i) :
    fconnect F ⟨i, a⟩ ⟨i, b⟩ ↔ fconnect (f i) a b := by
  refine connect_sigma_iff (e := frel F) (e' := fun i => frel (f i)) (fun i a b => ?_) ?_ i a b
  · show F ⟨i, a⟩ = ⟨i, b⟩ ↔ f i a = b
    rw [hF]
    exact sigma_mk_injective.eq_iff
  · rintro ⟨i, a⟩ z' rfl
    show i = (F ⟨i, a⟩).1
    rw [hF]

private theorem fconnect_sigma_fst {f : ∀ i, Equiv.Perm (E i)} {F : Equiv.Perm (Σ i, E i)}
    (hF : ∀ i x, F ⟨i, x⟩ = ⟨i, f i x⟩) {z z' : Σ i, E i} (h : fconnect F z z') : z.1 = z'.1 := by
  refine connect_sigma_fst (e := frel F) ?_ h
  rintro ⟨i, a⟩ z' rfl
  show i = (F ⟨i, a⟩).1
  rw [hF]

/-- A family of drawn disks is a map of disks. -/
theorem sigmaMap_isDisks (hK : ∀ i, (K i).DiskDrawn (l i)) (hne : ∀ i, l i ≠ []) :
    (sigmaMap K).IsDisks (sigmaPorts l) where
  planar := sigmaMap_planar K fun i => (hK i).planar
  node_return := by
    refine Equiv.ext ?_
    rintro ⟨i, x⟩
    have h1 : firstReturn (sigmaMap K).rot (sigmaPorts l) ⟨i, x⟩ =
        ⟨i, firstReturn (K i).rot (l i).toFinset x⟩ :=
      firstReturn_sigma (f := fun i => (K i).rot) (fun _ _ => rfl) i x
    show firstReturn (sigmaMap K).rot (sigmaPorts l) ⟨i, x⟩ = ⟨i, x⟩
    rw [h1]
    by_cases hx : x ∈ (l i).toFinset
    · have hy := (firstReturn_mem_iff (K i).rot (S := (l i).toFinset) (x := x)).2 hx
      have ht : (K i).tail x = (K i).tail (firstReturn (K i).rot (l i).toFinset x) :=
        ((K i).tail_eq_iff _ _).2 (fconnect_firstReturn _ _ x)
      have := List.inj_on_of_nodup_map (hK i).tails_nodup (List.mem_toFinset.1 hx)
        (List.mem_toFinset.1 hy) ht
      rw [← this]
    · rw [firstReturn_of_not_mem _ hx]
  meets := by
    rintro ⟨i, x⟩
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ (hne i)
    refine ⟨⟨i, y⟩, mem_sigmaPorts.2 hy, (sigmaMap_gcomp_iff K i x y).2 ?_⟩
    exact connect_of_nComp_eq_one (K i).toHypermap.glinkC (hK i).connected (Set.mem_univ x)
      (Set.mem_univ y)
  one_orbit := by
    rintro ⟨i, a⟩ ha ⟨j, b⟩ hb h
    obtain rfl : i = j := sigmaMap_gcomp_fst K h
    refine (fconnect_firstReturn_iff _ ha hb).2 ?_
    exact (fconnect_sigma (f := fun i => (K i).facePerm) (fun _ _ => rfl) i a b).2
      ((hK i).one_face (mem_sigmaPorts.1 ha) (mem_sigmaPorts.1 hb))

/-! ### Walks of the union -/

theorem tail_sigma_iff (i : ι) (x y : E i) :
    (sigmaMap K).tail ⟨i, x⟩ = (sigmaMap K).tail ⟨i, y⟩ ↔ (K i).tail x = (K i).tail y := by
  rw [tail_eq_iff, tail_eq_iff]
  exact fconnect_sigma (f := fun i => (K i).rot) (fun _ _ => rfl) i x y

theorem tail_sigma_fst {z z' : Σ i, E i} (h : (sigmaMap K).tail z = (sigmaMap K).tail z') :
    z.1 = z'.1 :=
  fconnect_sigma_fst (f := fun i => (K i).rot) (fun _ _ => rfl) (((sigmaMap K).tail_eq_iff _ _).1 h)

theorem isWalk_sigma (i : ι) {ws : List (E i)} {x y : E i}
    (h : (K i).IsWalk ((K i).tail x) ws ((K i).tail y)) :
    (sigmaMap K).IsWalk ((sigmaMap K).tail ⟨i, x⟩) (ws.map (Sigma.mk i))
      ((sigmaMap K).tail ⟨i, y⟩) := by
  induction ws generalizing x with
  | nil => exact (tail_sigma_iff K i x y).2 h
  | cons d ws ih =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨(tail_sigma_iff K i d x).2 h1, ih h2⟩

/-- A walk of the union stays in one part. -/
theorem isWalk_of_sigma (i : ι) (ws : List (Σ i, E i)) (x : E i) (z : Σ i, E i)
    (h : (sigmaMap K).IsWalk ((sigmaMap K).tail ⟨i, x⟩) ws ((sigmaMap K).tail z)) :
    ∃ (y : E i) (ws' : List (E i)), z = ⟨i, y⟩ ∧ ws = ws'.map (Sigma.mk i) ∧
      (K i).IsWalk ((K i).tail x) ws' ((K i).tail y) := by
  induction ws generalizing x with
  | nil =>
    obtain ⟨j, y⟩ := z
    have h1 : (sigmaMap K).tail ⟨i, x⟩ = (sigmaMap K).tail ⟨j, y⟩ := h
    obtain rfl : i = j := tail_sigma_fst K h1
    exact ⟨y, [], rfl, rfl, (tail_sigma_iff K i x y).1 h1⟩
  | cons d ws ih =>
    obtain ⟨h1, h2⟩ := h
    obtain ⟨j, d'⟩ := d
    obtain rfl : j = i := tail_sigma_fst K h1
    obtain ⟨y, ws', rfl, rfl, h3⟩ := ih ((K j).rev d') h2
    exact ⟨y, d' :: ws', rfl, rfl, (tail_sigma_iff K j d' x).1 h1, h3⟩

variable (g : ∀ i, E i → ℝ≥0∞)

/-- The weights on the union. -/
def sigmaWeight (z : Σ i, E i) : ℝ≥0∞ := g z.1 z.2

private theorem sum_sigmaWeight (i : ι) (ws : List (E i)) :
    ((ws.map (Sigma.mk i)).map (sigmaWeight g)).sum = (ws.map (g i)).sum := by
  rw [List.map_map]
  rfl

/-- The distance in one part of the union. -/
theorem walkDist_sigma (i : ι) (x y : E i) :
    (sigmaMap K).walkDist (sigmaWeight g) ((sigmaMap K).tail ⟨i, x⟩) ((sigmaMap K).tail ⟨i, y⟩) =
      (K i).walkDist (g i) ((K i).tail x) ((K i).tail y) := by
  apply le_antisymm
  · simp only [walkDist, le_iInf_iff]
    intro ws hws
    have := iInf₂_le (f := fun (p : List (Σ i, E i))
      (_ : (sigmaMap K).IsWalk ((sigmaMap K).tail ⟨i, x⟩) p ((sigmaMap K).tail ⟨i, y⟩)) =>
        (p.map (sigmaWeight g)).sum) _ (isWalk_sigma K i hws)
    rwa [sum_sigmaWeight] at this
  · simp only [walkDist, le_iInf_iff]
    intro ws hws
    obtain ⟨y', ws', h1, rfl, h3⟩ := isWalk_of_sigma K i ws x ⟨i, y⟩ hws
    obtain rfl : y = y' := sigma_mk_injective h1
    rw [sum_sigmaWeight]
    exact iInf₂_le (f := fun (p : List (E i))
      (_ : (K i).IsWalk ((K i).tail x) p ((K i).tail y)) => (p.map (g i)).sum) ws' h3

/-- There is no walk between two parts of the union. -/
theorem walkDist_sigma_ne {i j : ι} (hij : i ≠ j) (x : E i) (y : E j) :
    (sigmaMap K).walkDist (sigmaWeight g) ((sigmaMap K).tail ⟨i, x⟩) ((sigmaMap K).tail ⟨j, y⟩) =
      ⊤ := by
  simp only [walkDist, iInf_eq_top]
  intro ws hws
  obtain ⟨y', ws', h1, -, -⟩ := isWalk_of_sigma K i ws x ⟨j, y⟩ hws
  exact absurd (congrArg Sigma.fst h1) (Ne.symm hij)

end Family

end SigmaMap

/-! ### Monge for composed disks -/

section Compose

variable {D : Type*} [Fintype D] [DecidableEq D] {M : RotSystem D}
  {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*} [∀ i, Fintype (E i)]
  [∀ i, DecidableEq (E i)]

/-- `Lst` lists the cycles of `ψ` at `Γ`, each in its order. -/
structure ListsCycles (M : RotSystem D) (Γ : Finset D) (Lst : ι → List D) : Prop where
  /-- No corner twice. -/
  nodup : ∀ i, (Lst i).Nodup
  /-- All listed darts are marked corners. -/
  mem : ∀ i, ∀ x ∈ Lst i, x ∈ Γ
  /-- All marked corners are listed. -/
  cover : ∀ x ∈ Γ, ∃ i, x ∈ Lst i
  /-- Every marked corner is on one list only. -/
  disj : ∀ i j x, x ∈ Lst i → x ∈ Lst j → i = j
  /-- Each list is a cycle of `ψ`. -/
  psi : ∀ i, ∀ x ∈ Lst i, M.psi Γ x = (Lst i).formPerm x
  /-- No list is empty. -/
  ne : ∀ i, Lst i ≠ []

variable {Γ' : Finset D} {Lst : ι → List D} {l : ∀ i, List (E i)}

/-- The index of a port, as a marked corner of the disks. -/
private def portP (hlen : ∀ i, (l i).length = (Lst i).length) (z : Σ i, Fin (Lst i).length) :
    sigmaPorts l :=
  ⟨⟨z.1, (l z.1)[z.2.1]'(by rw [hlen]; exact z.2.2)⟩, mem_sigmaPorts.2 (List.getElem_mem _)⟩

/-- The index of a port, as a marked corner of the map. -/
private def portQ (hL : ListsCycles M Γ' Lst) (z : Σ i, Fin (Lst i).length) : Γ' :=
  ⟨(Lst z.1)[z.2.1], hL.mem _ _ (List.getElem_mem _)⟩

private theorem portP_bijective (hlen : ∀ i, (l i).length = (Lst i).length)
    (hnd : ∀ i, (l i).Nodup) : Function.Bijective (portP hlen) := by
  constructor
  · rintro ⟨i, a⟩ ⟨j, b⟩ h
    have h1 := congrArg Subtype.val h
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h1
    have h3 := (List.Nodup.getElem_inj_iff (hnd i)).1 (eq_of_heq h2)
    exact congrArg (Sigma.mk i) (Fin.ext h3)
  · rintro ⟨⟨i, y⟩, hy⟩
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem (mem_sigmaPorts.1 hy)
    exact ⟨⟨i, ⟨a, by rw [← hlen]; exact ha⟩⟩, rfl⟩

private theorem portQ_bijective (hL : ListsCycles M Γ' Lst) : Function.Bijective (portQ hL) := by
  constructor
  · rintro ⟨i, a⟩ ⟨j, b⟩ h
    have h1 : (Lst i)[a.1] = (Lst j)[b.1] := congrArg Subtype.val h
    obtain rfl : i = j := hL.disj i j (Lst i)[a.1] (List.getElem_mem _) (by
      rw [h1]
      exact List.getElem_mem _)
    have h3 := (List.Nodup.getElem_inj_iff (hL.nodup i)).1 h1
    exact congrArg (Sigma.mk i) (Fin.ext h3)
  · rintro ⟨y, hy⟩
    obtain ⟨i, hi⟩ := hL.cover y hy
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hi
    exact ⟨⟨i, ⟨a, ha⟩⟩, rfl⟩

/-- The bijection between the marked corners of the disks and those of the map. -/
private noncomputable def coverEquiv (hL : ListsCycles M Γ' Lst)
    (hlen : ∀ i, (l i).length = (Lst i).length) (hnd : ∀ i, (l i).Nodup) : sigmaPorts l ≃ Γ' :=
  (Equiv.ofBijective _ (portP_bijective hlen hnd)).symm.trans
    (Equiv.ofBijective _ (portQ_bijective hL))

private theorem corr_cover (hL : ListsCycles M Γ' Lst)
    (hlen : ∀ i, (l i).length = (Lst i).length) (hnd : ∀ i, (l i).Nodup) (i : ι) {a a' : ℕ}
    (ha : a < (l i).length) (hb : a' < (Lst i).length) (h : a = a') :
    Corr (coverEquiv hL hlen hnd) ⟨i, (l i)[a]⟩ (Lst i)[a'] := by
  subst h
  refine ⟨mem_sigmaPorts.2 (List.getElem_mem _), ?_⟩
  have h1 : (⟨⟨i, (l i)[a]⟩, mem_sigmaPorts.2 (List.getElem_mem _)⟩ : sigmaPorts l) =
      portP hlen ⟨i, ⟨a, hb⟩⟩ := rfl
  rw [h1]
  show ((Equiv.ofBijective _ (portQ_bijective hL))
    ((Equiv.ofBijective _ (portP_bijective hlen hnd)).symm (portP hlen ⟨i, ⟨a, hb⟩⟩)) : D) = _
  rw [Equiv.ofBijective_symm_apply_apply]
  rfl

private theorem exists_index (hL : ListsCycles M Γ' Lst)
    (hlen : ∀ i, (l i).length = (Lst i).length) (hnd : ∀ i, (l i).Nodup)
    {x' : Σ i, E i} {x : D} (h : Corr (coverEquiv hL hlen hnd) x' x) :
    ∃ i a, ∃ (ha : a < (l i).length) (hb : a < (Lst i).length),
      x' = ⟨i, (l i)[a]⟩ ∧ x = (Lst i)[a] := by
  obtain ⟨i, y⟩ := x'
  have hy : y ∈ l i := mem_sigmaPorts.1 h.1
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hy
  have hb : a < (Lst i).length := by rw [← hlen]; exact ha
  exact ⟨i, a, ha, hb, rfl, h.right_unique (corr_cover hL hlen hnd i ha hb rfl)⟩

/-- **Monge for composed disks.** Disks in place of the components of the split at `Γ'`, with the same
cyclic order of the marked corners. On every cycle of `ψ` at `Γ ⊆ Γ'`, hub walks over the distances of
the disks, free at corners that the split at `Γ` joins, satisfy the condition (M). -/
theorem hubDist_monge (hR : M.Planar) (hc : M.Connected) {Γ : Finset D} (hsub : Γ ⊆ Γ')
    (hΓ : Γ.Nonempty) (hS : M.SkeletonConnected Γ) (hS' : M.SkeletonConnected Γ')
    (hL : ListsCycles M Γ' Lst) (K : ∀ i, RotSystem (E i)) (g : ∀ i, E i → ℝ≥0∞)
    (hK : ∀ i, (K i).DiskDrawn (l i)) (hlen : ∀ i, (l i).length = (Lst i).length)
    (μ : D → D → ℝ≥0∞)
    (hμ : ∀ i a (ha : a < (l i).length) (hb : a < (Lst i).length) n (hc1 : n < (l i).length)
      (hc2 : n < (Lst i).length),
      (K i).walkDist (g i) ((K i).tail (l i)[a]) ((K i).tail (l i)[n]) =
        μ (Lst i)[a] (Lst i)[n])
    (hμ' : ∀ i j x y, i ≠ j → x ∈ Lst i → y ∈ Lst j → μ x y = ⊤)
    {c : List D} (hcn : c.Nodup) (hcm : ∀ x ∈ c, x ∈ Γ) (hcψ : ∀ x ∈ c, M.psi Γ x = c.formPerm x)
    {a b c' f u v x z : D} (hsl : [a, b, c', f].Sublist c)
    (huv : (u = a ∧ v = c') ∨ (u = c' ∧ v = a)) (hxz : (x = b ∧ z = f) ∨ (x = f ∧ z = b)) :
    hubDist Γ' (stepOf ((M.split Γ).nodeReturn Γ') μ) u z +
        hubDist Γ' (stepOf ((M.split Γ).nodeReturn Γ') μ) x v ≤
      hubDist Γ' (stepOf ((M.split Γ).nodeReturn Γ') μ) u v +
        hubDist Γ' (stepOf ((M.split Γ).nodeReturn Γ') μ) x z := by
  classical
  have hnd : ∀ i, (l i).Nodup := fun i => (hK i).nodup
  have hne : ∀ i, l i ≠ [] := fun i h0 => hL.ne i (by
    have := hlen i
    rw [h0] at this
    exact List.length_eq_zero_iff.1 this.symm)
  set β := coverEquiv hL hlen hnd with hβ
  have hP' := sigmaMap_isDisks K hK hne
  have hΓ' : Γ'.Nonempty := hΓ.mono hsub
  have hψ' : ConjVia β ((sigmaMap K).faceReturn (sigmaPorts l)) (M.psi Γ') := by
    intro x' x hcorr
    obtain ⟨i, n, ha, hb, rfl, rfl⟩ := exists_index hL hlen hnd hcorr
    have h1 : (sigmaMap K).faceReturn (sigmaPorts l) ⟨i, (l i)[n]⟩ =
        ⟨i, firstReturn (K i).facePerm (l i).toFinset (l i)[n]⟩ :=
      firstReturn_sigma (f := fun i => (K i).facePerm) (fun _ _ => rfl) i _
    rw [h1, (hK i).order, List.formPerm_apply_getElem _ (hnd i), hL.psi i _ (List.getElem_mem _),
      List.formPerm_apply_getElem _ (hL.nodup i)]
    exact corr_cover hL hlen hnd i _ _ (by rw [hlen])
  obtain ⟨h1, h2, h3, h4⟩ := M.replace_planar hR hc hΓ' hS' hP' β hψ'
  set Q' := M.replace Γ' (sigmaMap K) β with hQ'
  have hA' : ConjVia β (Q'.nodeReturn (sigmaPorts l)) (M.nodeReturn Γ') := by
    rw [h3]
    exact conjVia_transport β _ _
  have hB' : ConjVia β (Q'.faceReturn (sigmaPorts l)) (M.faceReturn Γ') := by
    rw [h4]
    exact conjVia_transport β _ _
  set sP := (sigmaPorts l).filter (fun y' => ∃ y ∈ Γ, Corr β y' y) with hsP
  have hT : ∀ x' x, Corr β x' x → (x' ∈ sP ↔ x ∈ Γ) := by
    intro x' x h
    constructor
    · intro hx
      obtain ⟨y, hy, h5⟩ := (Finset.mem_filter.1 hx).2
      rwa [h.right_unique h5]
    · intro hx
      exact Finset.mem_filter.2 ⟨h.1, x, hx, h⟩
  have hsP' : sP ⊆ sigmaPorts l := Finset.filter_subset _ _
  have hA : ConjVia β (Q'.nodeReturn sP) (M.nodeReturn Γ) := by
    have h5 := conjVia_firstReturn hA' hT
    unfold nodeReturn at h5 ⊢
    rwa [firstReturn_firstReturn _ hsP', firstReturn_firstReturn _ hsub] at h5
  have hB : ConjVia β (Q'.faceReturn sP) (M.faceReturn Γ) := by
    have h5 := conjVia_firstReturn hB' hT
    unfold faceReturn at h5 ⊢
    rwa [firstReturn_firstReturn _ hsP', firstReturn_firstReturn _ hsub] at h5
  -- The marked corners of the disks that belong to the map's corners.
  obtain ⟨x₀, hx₀⟩ := hΓ
  let βi : D → Σ i, E i := fun y =>
    if h : y ∈ Γ' then ((β.symm ⟨y, h⟩ : sigmaPorts l) : Σ i, E i) else
      ((β.symm ⟨x₀, hsub hx₀⟩ : sigmaPorts l) : Σ i, E i)
  have hβi : ∀ y ∈ Γ', Corr β (βi y) y := by
    intro y hy
    have h5 : βi y = ((β.symm ⟨y, hy⟩ : sigmaPorts l) : Σ i, E i) := dite_eq_left hy
    rw [h5]
    exact ⟨(β.symm ⟨y, hy⟩).2, by simp⟩
  have hβΓ : ∀ y ∈ Γ, Corr β (βi y) y := fun y hy => hβi y (hsub hy)
  have hsPne : sP.Nonempty := ⟨βi x₀, (hT _ _ (hβΓ x₀ hx₀)).2 hx₀⟩
  have hSP : Q'.SkeletonConnected sP := by
    intro p hp q hq
    obtain ⟨y1, hy1, h5⟩ := (Finset.mem_filter.1 hp).2
    obtain ⟨y2, hy2, h6⟩ := (Finset.mem_filter.1 hq).2
    exact (permMap_gcomp_corr hA hB h5 h6).2 (hS y1 hy1 y2 hy2)
  set l₀ := c.map βi with hl₀
  have hl₀n : l₀.Nodup := hcn.map_on fun p hp q hq h =>
    ((hβΓ p (hcm p hp))).right_unique (h ▸ hβΓ q (hcm q hq))
  have hl₀m : ∀ y' ∈ l₀, y' ∈ sP := by
    intro y' hy'
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hy'
    exact (hT _ _ (hβΓ y (hcm y hy))).2 (hcm y hy)
  have hl₀ψ : ∀ y' ∈ l₀, Q'.psi sP y' = l₀.formPerm y' := by
    intro y' hy'
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hy'
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hy
    have h5 : Corr β (Q'.psi sP (βi c[n])) (M.psi Γ c[n]) :=
      (hA.mul hB) _ _ (hβΓ _ (hcm _ hy))
    rw [hcψ _ hy, List.formPerm_apply_getElem _ hcn] at h5
    have hn' : n < l₀.length := by simpa [hl₀] using hn
    have h6 : βi c[n] = l₀[n] := by simp [hl₀]
    rw [h6, List.formPerm_apply_getElem _ hl₀n, ← h6]
    refine h5.left_unique ?_
    have h7 : l₀[(n + 1) % l₀.length]'(Nat.mod_lt _ (by omega)) =
        βi (c[(n + 1) % c.length]'(Nat.mod_lt _ (by omega))) := by
      simp [hl₀]
    rw [h7]
    exact hβΓ _ (hcm _ (List.getElem_mem _))
  have hF : (Q'.split sP).FaceDrawn l₀ := split_faceDrawn h1 h2 hsPne hSP hl₀n hl₀m hl₀ψ
  -- The split of the composition, as a gluing of the disks.
  have hQ : Q'.split sP = (sigmaMap K).glue (Q'.nodeReturn (sigmaPorts l) * (Q'.nodeReturn sP)⁻¹) := by
    refine RotSystem.ext rfl ?_
    show Q'.rot * (Q'.nodeReturn sP)⁻¹ =
      (sigmaMap K).rot * (Q'.nodeReturn (sigmaPorts l) * (Q'.nodeReturn sP)⁻¹)
    rw [h3, ← mul_assoc]
    rfl
  have hν : FixesOff (Q'.nodeReturn (sigmaPorts l) * (Q'.nodeReturn sP)⁻¹) (sigmaPorts l) :=
    (Q'.fixesOff_nodeReturn _).mul ((Q'.fixesOff_nodeReturn _).inv.mono hsP')
  have hνP : (M.split Γ).nodeReturn Γ' = M.nodeReturn Γ' * (M.nodeReturn Γ)⁻¹ :=
    M.nodeReturn_glue ((M.fixesOff_nodeReturn Γ).inv.mono hsub)
  have hconj : ConjVia β (Q'.nodeReturn (sigmaPorts l) * (Q'.nodeReturn sP)⁻¹)
      ((M.split Γ).nodeReturn Γ') := by
    rw [hνP]
    exact hA'.mul hA.inv
  have hstep : ∀ a' a b' b, Corr β a' a → Corr β b' b →
      gluedStep (sigmaMap K) (Q'.nodeReturn (sigmaPorts l) * (Q'.nodeReturn sP)⁻¹)
        (sigmaWeight g) a' b' = stepOf ((M.split Γ).nodeReturn Γ') μ a b := by
    intro a' a b' b ha hb
    unfold gluedStep stepOf
    have hiff := (⟨fconnect_corr hconj ha hb, fconnect_corr hconj.symm ha.symm hb.symm⟩ :
      fconnect (Q'.nodeReturn (sigmaPorts l) * (Q'.nodeReturn sP)⁻¹) a' b' ↔
        fconnect ((M.split Γ).nodeReturn Γ') a b)
    by_cases hf : fconnect ((M.split Γ).nodeReturn Γ') a b
    · rw [ite_eq_left hf, ite_eq_left (hiff.2 hf)]
    · rw [ite_eq_right hf, ite_eq_right (fun h => hf (hiff.1 h))]
      beta_reduce
      obtain ⟨i, n, ha1, ha2, rfl, rfl⟩ := exists_index hL hlen hnd ha
      obtain ⟨j, m, hb1, hb2, rfl, rfl⟩ := exists_index hL hlen hnd hb
      by_cases hij : i = j
      · subst hij
        rw [walkDist_sigma K g, hμ i n ha1 ha2 m hb1 hb2]
      · rw [walkDist_sigma_ne K g hij, hμ' i j _ _ hij (List.getElem_mem _) (List.getElem_mem _)]
  have hW : ∀ p ∈ Γ', ∀ q ∈ Γ',
      (Q'.split sP).walkDist (sigmaWeight g) ((Q'.split sP).tail (βi p))
        ((Q'.split sP).tail (βi q)) = hubDist Γ' (stepOf ((M.split Γ).nodeReturn Γ') μ) p q := by
    intro p hp q hq
    rw [walkDist_of_eq_glue hQ hP'.node_return hν (sigmaWeight g) (βi p) (βi q) (hβi q hq).1
      (hβi p hp).1]
    exact hubDist_corr hstep (hβi p hp) (hβi q hq)
  have hmemc : ∀ y ∈ [a, b, c', f], y ∈ Γ' := fun y hy => hsub (hcm y (hsl.subset hy))
  have hm := hF.monge (sigmaWeight g) (a := βi a) (b := βi b) (c := βi c') (d := βi f)
    (u := βi u) (v := βi v) (w := βi x) (z := βi z) (by simpa using hsl.map βi) (by
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩) (by
      rcases hxz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩)
  have hu : u ∈ Γ' := by
    rcases huv with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact hmemc _ (by simp)
  have hv : v ∈ Γ' := by
    rcases huv with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact hmemc _ (by simp)
  have hx : x ∈ Γ' := by
    rcases hxz with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact hmemc _ (by simp)
  have hz : z ∈ Γ' := by
    rcases hxz with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact hmemc _ (by simp)
  rwa [hW u hu z hz, hW x hx v hv, hW u hu v hv, hW x hx z hz] at hm

end Compose

end RotSystem

end SsspFlow
