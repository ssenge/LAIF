import SsspFlow.Levels

/-!
# Estimates between the vertices and the hubs of a bag

In a hierarchy of region bags, values `dV x` between the hubs of a bag `x` give values `est x v h` from
all vertices of the bag to its hubs: `est x v h = dV x v h` on a hub, and otherwise the least
`est c v t + dV x t h` over the hubs `t` of `x` in the child `c` of `v`. `est_bounds`: they keep the bounds
of `dV`, with no growth over the levels.

`bagHubs`, `bagStep`, `bagDist`: the values `dV` of a bag on a doubled map, from values `δ` on its corners.
Two corners at one vertex are not told apart: a step between two hubs is the least value over their
corners. `bagDist_lo`, `bagDist_hi`: the bounds of `δ` on the corners give those of `bagDist`, with respect
to walks in the graph and to walks along the arcs of the bag.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal

namespace SsspFlow

open FourColor

universe u v

namespace Walk

variable {V : Type u} {adj : V → V → Prop}

lemma arcsIn_append {A : V → V → Prop} : ∀ {a b c : V} (p : Walk adj a b) (q : Walk adj b c),
    p.arcsIn A → q.arcsIn A → (p.append q).arcsIn A
  | _, _, _, nil _, _, _, hq => hq
  | _, _, _, cons e p, q, hp, hq => by
    have hp' := (arcsIn_cons A e p).1 hp
    exact (arcsIn_cons A e _).2 ⟨hp'.1, arcsIn_append p q hp'.2 hq⟩

lemma arcsIn_reverse {A : V → V → Prop} : ∀ {a b : V} (p : Walk adj a b), p.arcsIn A →
    p.reverse.arcsIn (fun x y => A y x)
  | _, _, nil _, _ => trivial
  | _, _, cons e p, hp => by
    have hp' := (arcsIn_cons A e p).1 hp
    exact arcsIn_append _ _ (arcsIn_reverse p hp'.2) ⟨hp'.1, trivial⟩

end Walk

lemma distR_flip_le {V : Type u} {adj : V → V → Prop} (w : V → V → ℝ≥0∞) (A : V → V → Prop)
    (a b : V) : distR (flip adj) (flip w) (fun x y => A y x) b a ≤ distR adj w A a b := by
  simp only [distR, le_iInf_iff]
  intro p hp
  rw [← Walk.wt_reverse w p]
  exact iInf₂_le p.reverse (Walk.arcsIn_reverse p hp)

lemma distR_flip {V : Type u} {adj : V → V → Prop} (w : V → V → ℝ≥0∞) (A : V → V → Prop)
    (a b : V) : distR (flip adj) (flip w) (fun x y => A y x) b a = distR adj w A a b :=
  le_antisymm (distR_flip_le w A a b) (distR_flip_le (adj := flip adj) (flip w) (fun x y => A y x) b a)

namespace RHierarchy

variable {V : Type u} {ι : Type v} {adj : V → V → Prop} (H : RHierarchy V ι adj)

/-- The hierarchy of the reversed digraph. -/
def flip : RHierarchy V ι (Function.swap adj) where
  bag := H.bag
  arc x a b := H.arc x b a
  hub := H.hub
  kid := H.kid
  wf := H.wf
  root := H.root
  root_bag := H.root_bag
  root_arc a b h := H.root_arc b a h
  arc_bag x a b h := (H.arc_bag x b a h).symm
  cover := H.cover
  uniq := H.uniq
  edge x a b h ha hb := H.edge x b a h hb ha

/-- A walk in the region of a bag from outside the hubs to a hub reaches the hubs inside one child. -/
lemma first_hub (hedge : ∀ x a b, H.arc x a b → a ∉ H.hub x → ∃ c, H.kid c x ∧ H.arc c a b)
    (w : V → V → ℝ≥0∞) (x : ι) : ∀ {a b : V} (p : Walk adj a b), p.arcsIn (H.arc x) → a ∉ H.hub x →
    b ∈ H.hub x → ∃ c t, H.kid c x ∧ a ∈ H.bag c ∧ t ∈ H.hub x ∧ t ∈ H.bag c ∧
      ∃ (p₁ : Walk adj a t) (p₂ : Walk adj t b), p₁.arcsIn (H.arc c) ∧ p₂.arcsIn (H.arc x) ∧
        p₁.wt w + p₂.wt w = p.wt w
  | _, _, .nil _, _, ha, hb => absurd hb ha
  | _, b, .cons (b := m) e p, hp, ha, hb => by
    have hp' := (Walk.arcsIn_cons _ e p).1 hp
    obtain ⟨c, hk, hac⟩ := hedge x _ _ hp'.1 ha
    have hbag := H.arc_bag c _ _ hac
    by_cases hm : m ∈ H.hub x
    · exact ⟨c, m, hk, hbag.1, hm, hbag.2, .cons e (.nil m), p, ⟨hac, trivial⟩, hp'.2, by simp⟩
    · obtain ⟨c', t, hk', hmc, ht, htc, p₁, p₂, h₁, h₂, hw⟩ := first_hub hedge w x p hp'.2 hm hb
      obtain rfl := H.uniq x c c' m hk hk' (H.arc_bag x _ _ hp'.1).2 hm hbag.2 hmc
      refine ⟨c, t, hk, hbag.1, ht, htc, .cons e p₁, p₂, ⟨hac, h₁⟩, h₂, ?_⟩
      simp only [Walk.wt_cons, ← hw, add_assoc]

/-- **Estimates to the hubs.** They keep the bounds of the values between the hubs. -/
theorem est_bounds (hedge : ∀ x a b, H.arc x a b → a ∉ H.hub x → ∃ c, H.kid c x ∧ H.arc c a b)
    (hubk : ∀ x c t, H.kid c x → t ∈ H.hub x → t ∈ H.bag c → t ∈ H.hub c)
    (w : V → V → ℝ≥0∞) (κ lam : ℝ≥0∞) (hlam0 : lam ≠ 0) (hlamT : lam ≠ ⊤) (dV : ι → V → V → ℝ≥0∞)
    (hlo : ∀ x, ∀ a ∈ H.hub x, ∀ b ∈ H.hub x, κ * dist adj w Set.univ a b ≤ dV x a b)
    (hhi : ∀ x, ∀ a ∈ H.hub x, ∀ b ∈ H.hub x, dV x a b ≤ lam * distR adj w (H.arc x) a b)
    (est : ι → V → V → ℝ≥0∞)
    (h1 : ∀ x v h, v ∈ H.hub x → h ∈ H.hub x → est x v h = dV x v h)
    (h2 : ∀ x v h, v ∈ H.bag x → v ∉ H.hub x → h ∈ H.hub x → est x v h =
      ⨅ (c : ι) (t : V) (_ : H.kid c x ∧ v ∈ H.bag c ∧ t ∈ H.hub x ∧ t ∈ H.bag c),
        est c v t + dV x t h)
    (x : ι) : ∀ v ∈ H.bag x, ∀ h ∈ H.hub x,
      κ * dist adj w Set.univ v h ≤ est x v h ∧ est x v h ≤ lam * distR adj w (H.arc x) v h := by
  induction x using H.wf.induction with
  | _ x ih =>
  intro v hv h hh
  by_cases hvh : v ∈ H.hub x
  · rw [h1 x v h hvh hh]
    exact ⟨hlo x v hvh h hh, hhi x v hvh h hh⟩
  · rw [h2 x v h hv hvh hh]
    constructor
    · refine le_iInf fun c => le_iInf fun t => le_iInf fun hc => ?_
      obtain ⟨hk, hvc, ht, htc⟩ := hc
      calc κ * dist adj w Set.univ v h
          ≤ κ * (dist adj w Set.univ v t + dist adj w Set.univ t h) := by
            gcongr
            exact dist_triangle' w _ _ _ _
        _ = κ * dist adj w Set.univ v t + κ * dist adj w Set.univ t h := mul_add _ _ _
        _ ≤ est c v t + dV x t h :=
            add_le_add (ih c hk v hvc t (hubk x c t hk ht htc)).1 (hlo x t ht h hh)
    · conv_rhs => rw [distR, ENNReal.mul_iInf_of_ne hlam0 hlamT]
      refine le_iInf fun p => ?_
      rw [ENNReal.mul_iInf_of_ne hlam0 hlamT]
      refine le_iInf fun hp => ?_
      obtain ⟨c, t, hk, hvc, ht, htc, p₁, p₂, h₁, h₂, hw⟩ := H.first_hub hedge w x p hp hvh hh
      calc (⨅ (c : ι) (t : V) (_ : H.kid c x ∧ v ∈ H.bag c ∧ t ∈ H.hub x ∧ t ∈ H.bag c),
            est c v t + dV x t h)
          ≤ est c v t + dV x t h :=
            (iInf_le _ c).trans ((iInf_le _ t).trans (iInf_le _ ⟨hk, hvc, ht, htc⟩))
        _ ≤ lam * distR adj w (H.arc c) v t + lam * distR adj w (H.arc x) t h :=
            add_le_add (ih c hk v hvc t (hubk x c t hk ht htc)).2 (hhi x t ht h hh)
        _ ≤ lam * p₁.wt w + lam * p₂.wt w := by
            gcongr
            · exact iInf₂_le p₁ h₁
            · exact iInf₂_le p₂ h₂
        _ = lam * p.wt w := by rw [← mul_add, hw]

/-- **Estimates from the hubs.** The same in the reversed digraph. -/
theorem est_bounds_in (hedge : ∀ x a b, H.arc x a b → b ∉ H.hub x → ∃ c, H.kid c x ∧ H.arc c a b)
    (hubk : ∀ x c t, H.kid c x → t ∈ H.hub x → t ∈ H.bag c → t ∈ H.hub c)
    (w : V → V → ℝ≥0∞) (κ lam : ℝ≥0∞) (hlam0 : lam ≠ 0) (hlamT : lam ≠ ⊤) (dV : ι → V → V → ℝ≥0∞)
    (hlo : ∀ x, ∀ a ∈ H.hub x, ∀ b ∈ H.hub x, κ * dist adj w Set.univ a b ≤ dV x a b)
    (hhi : ∀ x, ∀ a ∈ H.hub x, ∀ b ∈ H.hub x, dV x a b ≤ lam * distR adj w (H.arc x) a b)
    (est : ι → V → V → ℝ≥0∞)
    (h1 : ∀ x v h, v ∈ H.hub x → h ∈ H.hub x → est x v h = dV x h v)
    (h2 : ∀ x v h, v ∈ H.bag x → v ∉ H.hub x → h ∈ H.hub x → est x v h =
      ⨅ (c : ι) (t : V) (_ : H.kid c x ∧ v ∈ H.bag c ∧ t ∈ H.hub x ∧ t ∈ H.bag c),
        est c v t + dV x h t)
    (x : ι) : ∀ v ∈ H.bag x, ∀ h ∈ H.hub x,
      κ * dist adj w Set.univ h v ≤ est x v h ∧ est x v h ≤ lam * distR adj w (H.arc x) h v := by
  intro v hv h hh
  have key := H.flip.est_bounds (fun x a b h' ha => by
      obtain ⟨c, hc, hac⟩ := hedge x b a h' ha
      exact ⟨c, hc, hac⟩) hubk (Function.swap w) κ lam hlam0 hlamT (fun x a b => dV x b a)
    (fun x a ha b hb => by
      have h3 := hlo x b hb a ha
      rw [← dist_flip w] at h3
      exact h3)
    (fun x a ha b hb => by
      have h3 := hhi x b hb a ha
      rw [← distR_flip w] at h3
      exact h3)
    est h1 h2 x v hv h hh
  have e1 : dist (Function.swap adj) (Function.swap w) Set.univ v h = dist adj w Set.univ h v :=
    dist_flip w _ h v
  have e2 : distR (Function.swap adj) (Function.swap w) (H.flip.arc x) v h = distR adj w (H.arc x) h v :=
    distR_flip w (H.arc x) h v
  rw [e1, e2] at key
  exact key

end RHierarchy

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace RootedTree

variable {V : Type*} [Fintype V] [DecidableEq V] {t : R.RootedTree V} {Γ : Finset (D × Bool)}

/-! ### Vertices of a split -/

/-- Darts along a trail of the rotation lie at one vertex of the split. -/
theorem split_tail_of_trail {z c : D × Bool} (h : Trail R.double.rot Γ z c) :
    (R.double.split Γ).tail z = (R.double.split Γ).tail c :=
  R.double.tail_glue_of_trail (R.double.fixesOff_nodeReturn Γ).inv h

/-- A dart at a vertex with a corner lies at one vertex of the split with a corner. -/
theorem exists_port_tail {u : D × Bool} (h : ¬ t.NP Γ (t.vertM u)) :
    ∃ g ∈ Γ, t.vertM g = t.vertM u ∧ (R.double.split Γ).tail u = (R.double.split Γ).tail g := by
  have h' : ∃ g ∈ Γ, t.vertM g = t.vertM u := by
    by_contra hn
    push Not at hn
    exact h hn
  obtain ⟨g, hg, hgu⟩ := h'
  obtain ⟨c, hc⟩ := exists_trail hg ((t.vertM_eq_iff u g).1 hgu.symm)
  exact ⟨c, hc.mem, ((t.vertM_eq_iff _ _).2 hc.to_fconnect).symm, split_tail_of_trail hc⟩

/-- All darts at a vertex without a corner lie at one vertex of the split. -/
theorem NP.tail_eq {v : V} (hv : t.NP Γ v) {z z' : D × Bool} (hz : t.vertM z = v)
    (hz' : t.vertM z' = v) : (R.double.split Γ).tail z = (R.double.split Γ).tail z' := by
  have h : fconnect R.double.rot z z' := (t.vertM_eq_iff _ _).1 (hz.trans hz'.symm)
  induction h with
  | refl => rfl
  | @tail e c he hec ih =>
    obtain rfl : R.double.rot e = c := hec
    have he' : t.vertM e = v := ((t.vertM_eq_iff _ _).2 he).symm.trans hz
    rw [ih he', ← (R.double.split Γ).tail_rot e, split_rot_of_not_mem _ (hv.not_mem he')]

/-- A vertex of the split lies at one vertex of the graph. -/
theorem vertM_of_tail {x y : D × Bool} (h : (R.double.split Γ).tail x = (R.double.split Γ).tail y) :
    t.vertM x = t.vertM y := by
  have h1 : fconnect (R.double.split Γ).rot x y := ((R.double.split Γ).tail_eq_iff x y).1 h
  induction h1 with
  | refl => rfl
  | @tail e c he hec ih =>
    obtain rfl : (R.double.split Γ).rot e = c := hec
    rw [ih ((R.double.split Γ).tail_eq_iff x e |>.2 he), split_rot_apply, t.vertM_rot]
    have h2 := fconnect_firstReturn R.double.rot Γ ((R.double.nodeReturn Γ)⁻¹ e)
    have h3 : firstReturn R.double.rot Γ ((R.double.nodeReturn Γ)⁻¹ e) = e :=
      perm_apply_inv_self _ _
    rw [h3] at h2
    exact (t.vertM_eq_iff _ _).2 h2 |>.symm

/-! ### Walks of a split in the graph -/

section Project

variable {adj : V → V → Prop} {w : V → V → ℝ≥0∞} {g : D × Bool → ℕ}

/-- The distance in the graph is at most the distance in a split. -/
theorem dist_le_walkDist (hadj : ∀ z, adj (t.vertM z) (t.vertM (R.double.rev z)))
    (hg : ∀ z, (g z : ℝ≥0∞) = w (t.vertM z) (t.vertM (R.double.rev z))) (x y : D × Bool) :
    dist adj w Set.univ (t.vertM x) (t.vertM y) ≤
      (R.double.split Γ).walkDist (fun z => (g z : ℝ≥0∞)) ((R.double.split Γ).tail x)
        ((R.double.split Γ).tail y) := by
  refine le_iInf₂ fun ws hws => ?_
  induction ws generalizing x with
  | nil =>
    have h1 : t.vertM x = t.vertM y := vertM_of_tail hws
    rw [h1]
    exact (iInf₂_le (Walk.nil _) (by simp)).trans (by simp)
  | cons z ws ih =>
    obtain ⟨h1, h2⟩ := hws
    have h3 : t.vertM z = t.vertM x := vertM_of_tail h1
    have h4 := ih (R.double.rev z) h2
    simp only [List.map_cons, List.sum_cons]
    rw [← h3, hg z]
    calc dist adj w Set.univ (t.vertM z) (t.vertM y)
        ≤ dist adj w Set.univ (t.vertM z) (t.vertM (R.double.rev z)) +
            dist adj w Set.univ (t.vertM (R.double.rev z)) (t.vertM y) := dist_triangle' w _ _ _ _
      _ ≤ w (t.vertM z) (t.vertM (R.double.rev z)) +
            (ws.map fun z => (g z : ℝ≥0∞)).sum := by
          refine add_le_add ?_ h4
          exact (iInf₂_le (Walk.cons (hadj z) (Walk.nil _)) (by simp)).trans (by simp)

end Project

/-! ### The hubs of a bag -/

section BagDist

variable (t) (Γ) (X : Set (D × Bool)) (δ : D × Bool → D × Bool → ℝ≥0∞)

open Classical in
/-- The corners of `Γ` in the set `X` of darts. -/
noncomputable def bagCorners : Finset (D × Bool) := Γ.filter (· ∈ X)

/-- The vertices of the corners of `Γ` in `X`. -/
noncomputable def bagHubs : Finset V := (bagCorners Γ X).image t.vertM

/-- A step between two hubs: the least value between their corners. -/
noncomputable def bagStep (a b : V) : ℝ≥0∞ :=
  ⨅ (p : D × Bool) (q : D × Bool)
    (_ : p ∈ bagCorners Γ X ∧ q ∈ bagCorners Γ X ∧ t.vertM p = a ∧ t.vertM q = b), δ p q

/-- The least total value of a walk of steps between hubs. -/
noncomputable def bagDist (a b : V) : ℝ≥0∞ := hubDist (bagHubs t Γ X) (bagStep t Γ X δ) a b

/-- The arcs of the darts of `X`. -/
def bagArc (a b : V) : Prop := ∃ z ∈ X, t.vertM z = a ∧ t.vertM (R.double.rev z) = b

variable {t Γ X δ}

theorem mem_bagCorners {p : D × Bool} : p ∈ bagCorners Γ X ↔ p ∈ Γ ∧ p ∈ X := by
  classical
  simp [bagCorners]

theorem mem_bagHubs {a : V} : a ∈ bagHubs t Γ X ↔ ∃ p ∈ Γ, p ∈ X ∧ t.vertM p = a := by
  classical
  simp [bagHubs, mem_bagCorners, and_assoc]

variable (hX : ∀ z z', z ∈ X → (R.double.split Γ).toHypermap.gcomp z z' → z' ∈ X)

include hX

/-- A dart of `X` at a hub has a corner of `X` at its vertex of the split. -/
theorem exists_port_bag {u : D × Bool} (hu : u ∈ X) (h : ¬ t.NP Γ (t.vertM u)) :
    ∃ g ∈ bagCorners Γ X, t.vertM g = t.vertM u ∧
      (R.double.split Γ).tail u = (R.double.split Γ).tail g := by
  obtain ⟨g, hg, h1, h2⟩ := exists_port_tail h
  refine ⟨g, mem_bagCorners.2 ⟨hg, hX u g hu ?_⟩, h1, h2⟩
  exact (R.double.split Γ).toHypermap.gcomp_of_cnode (((R.double.split Γ).tail_eq_iff _ _).1 h2)

/-- A dart of `X` off the hubs is at a vertex without a corner. -/
theorem np_of_not_bagHubs {u : D × Bool} (hu : u ∈ X) (h : t.vertM u ∉ bagHubs t Γ X) :
    t.NP Γ (t.vertM u) := by
  by_contra hn
  obtain ⟨g, hg, h1, -⟩ := exists_port_bag hX hu hn
  obtain ⟨hg1, hg2⟩ := mem_bagCorners.1 hg
  exact h (mem_bagHubs.2 ⟨g, hg1, hg2, h1⟩)

omit hX in
theorem not_np_of_bagHubs {a : V} (h : a ∈ bagHubs t Γ X) : ¬ t.NP Γ a := by
  obtain ⟨p, hp, -, rfl⟩ := mem_bagHubs.1 h
  exact fun hn => hn p hp rfl

omit hX in
theorem bagDist_le_step {a b : V} (ha : a ∈ bagHubs t Γ X) (hb : b ∈ bagHubs t Γ X) :
    bagDist t Γ X δ a b ≤ bagStep t Γ X δ a b :=
  hubDist_le_step ha hb

omit hX in
theorem bagStep_le {p q : D × Bool} (hp : p ∈ bagCorners Γ X) (hq : q ∈ bagCorners Γ X) :
    bagStep t Γ X δ (t.vertM p) (t.vertM q) ≤ δ p q :=
  (iInf_le _ p).trans ((iInf_le _ q).trans (iInf_le _ ⟨hp, hq, rfl, rfl⟩))

omit hX in
theorem vertM_mem_bagHubs {p : D × Bool} (hp : p ∈ bagCorners Γ X) : t.vertM p ∈ bagHubs t Γ X := by
  obtain ⟨h1, h2⟩ := mem_bagCorners.1 hp
  exact mem_bagHubs.2 ⟨p, h1, h2, rfl⟩

variable {adj : V → V → Prop} {w : V → V → ℝ≥0∞} {g : D × Bool → ℕ} {U : ℕ} {κ : ℝ≥0∞}

omit hX in
/-- **Lower bound.** Values above the distances of the split are above the distances of the graph. -/
theorem bagDist_lo (hadj : ∀ z, adj (t.vertM z) (t.vertM (R.double.rev z)))
    (hg : ∀ z, (g z : ℝ≥0∞) = w (t.vertM z) (t.vertM (R.double.rev z)))
    (hδ : ∀ p ∈ bagCorners Γ X, ∀ q ∈ bagCorners Γ X, lvlT R.double g U Γ p q ≤ δ p q) (a b : V) :
    (U : ℝ≥0∞) * dist adj w Set.univ a b ≤ bagDist t Γ X δ a b := by
  refine le_hubDist (f := fun a b => (U : ℝ≥0∞) * dist adj w Set.univ a b) (fun a => ?_)
    (fun a b c => ?_) (fun a ha b hb => ?_) a b
  · have h : dist adj w Set.univ a a ≤ 0 := (iInf₂_le (Walk.nil a) (by simp)).trans (by simp)
    simp [le_antisymm h zero_le]
  · rw [← mul_add]
    gcongr
    exact dist_triangle' w _ _ _ _
  · refine le_iInf fun p => le_iInf fun q => le_iInf ?_
    rintro ⟨hp, hq, rfl, rfl⟩
    refine le_trans ?_ (hδ p hp q hq)
    unfold lvlT
    gcongr
    exact dist_le_walkDist hadj hg p q

/-- Every dart of `X` at the start of a walk along the arcs of `X` reaches the hubs. -/
theorem lift_walk (hg : ∀ z, (g z : ℝ≥0∞) = w (t.vertM z) (t.vertM (R.double.rev z)))
    (hδ : ∀ p ∈ bagCorners Γ X, ∀ q ∈ bagCorners Γ X, δ p q ≤ κ * lvlT R.double g U Γ p q)
    {a b : V} (r : Walk adj a b) (hr : r.arcsIn (bagArc t X)) (hb : b ∈ bagHubs t Γ X) :
    ∀ u ∈ X, t.vertM u = a → ∃ q ∈ bagCorners Γ X,
      κ * ((U : ℝ≥0∞) * (R.double.split Γ).walkDist (fun z => (g z : ℝ≥0∞))
        ((R.double.split Γ).tail u) ((R.double.split Γ).tail q)) + bagDist t Γ X δ (t.vertM q) b ≤
      κ * ((U : ℝ≥0∞) * r.wt w) := by
  induction r with
  | nil a =>
    intro u hu hua
    obtain ⟨q, hq, hqu, htq⟩ := exists_port_bag hX hu (by rw [hua]; exact not_np_of_bagHubs hb)
    refine ⟨q, hq, ?_⟩
    have h0 : bagDist t Γ X δ (t.vertM q) a = 0 := by
      rw [hqu, hua]
      exact hubDist_self_le hb
    rw [← htq, walkDist_self, h0]
    simp
  | @cons a m b e p ih =>
    intro u hu hua
    obtain ⟨⟨z, hz, hza, hzm⟩, hp⟩ := (Walk.arcsIn_cons _ e p).1 hr
    have hzr : R.double.rev z ∈ X := hX z _ hz (same_rev Γ z)
    obtain ⟨q, hq, hq1⟩ := ih hp hb _ hzr hzm
    set Wd := (R.double.split Γ).walkDist (fun z => (g z : ℝ≥0∞)) with hWd
    have hwz : Wd ((R.double.split Γ).tail z) ((R.double.split Γ).tail q) ≤
        (g z : ℝ≥0∞) + Wd ((R.double.split Γ).tail (R.double.rev z)) ((R.double.split Γ).tail q) := by
      refine (walkDist_triangle _ _ ((R.double.split Γ).tail (R.double.rev z)) _).trans ?_
      gcongr
      have h1 : (R.double.split Γ).IsWalk ((R.double.split Γ).tail z) [z]
          ((R.double.split Γ).tail (R.double.rev z)) := ⟨rfl, rfl⟩
      exact (walkDist_le _ h1).trans (by simp)
    have hwt : (Walk.cons e p).wt w = (g z : ℝ≥0∞) + p.wt w := by
      rw [Walk.wt_cons, hg z, hza, hzm]
    have hstep : κ * ((U : ℝ≥0∞) * Wd ((R.double.split Γ).tail z) ((R.double.split Γ).tail q)) +
        bagDist t Γ X δ (t.vertM q) b ≤ κ * ((U : ℝ≥0∞) * (Walk.cons e p).wt w) := by
      rw [hwt]
      calc κ * ((U : ℝ≥0∞) * Wd ((R.double.split Γ).tail z) ((R.double.split Γ).tail q)) +
            bagDist t Γ X δ (t.vertM q) b
          ≤ κ * ((U : ℝ≥0∞) * ((g z : ℝ≥0∞) +
              Wd ((R.double.split Γ).tail (R.double.rev z)) ((R.double.split Γ).tail q))) +
            bagDist t Γ X δ (t.vertM q) b := by gcongr
        _ = κ * ((U : ℝ≥0∞) * (g z : ℝ≥0∞)) + (κ * ((U : ℝ≥0∞) *
              Wd ((R.double.split Γ).tail (R.double.rev z)) ((R.double.split Γ).tail q)) +
            bagDist t Γ X δ (t.vertM q) b) := by ring
        _ ≤ κ * ((U : ℝ≥0∞) * (g z : ℝ≥0∞)) + κ * ((U : ℝ≥0∞) * p.wt w) := by gcongr
        _ = κ * ((U : ℝ≥0∞) * ((g z : ℝ≥0∞) + p.wt w)) := by ring
    by_cases ha : a ∈ bagHubs t Γ X
    · obtain ⟨q₀, hq₀, hq₀u, htq₀⟩ := exists_port_bag hX hu (by rw [hua]; exact not_np_of_bagHubs ha)
      obtain ⟨p₀, hp₀, hp₀z, htp₀⟩ := exists_port_bag hX hz (by rw [hza]; exact not_np_of_bagHubs ha)
      refine ⟨q₀, hq₀, ?_⟩
      have h0 : Wd ((R.double.split Γ).tail u) ((R.double.split Γ).tail u) = 0 := walkDist_self _ _
      rw [← htq₀, h0, mul_zero, mul_zero, zero_add, hq₀u, hua]
      refine le_trans ?_ hstep
      rw [← hza]
      have h3 : bagDist t Γ X δ (t.vertM z) b ≤
          bagDist t Γ X δ (t.vertM z) (t.vertM q) + bagDist t Γ X δ (t.vertM q) b :=
        hubDist_triangle _ _ _ _
      refine h3.trans (add_le_add ?_ le_rfl)
      rw [← hp₀z]
      refine (bagDist_le_step (vertM_mem_bagHubs hp₀) (vertM_mem_bagHubs hq)).trans
        ((bagStep_le hp₀ hq).trans ((hδ p₀ hp₀ q hq).trans ?_))
      unfold lvlT
      rw [htp₀]
    · have hnp : t.NP Γ a := by
        have h1 := np_of_not_bagHubs hX hz (by rw [hza]; exact ha)
        rwa [hza] at h1
      refine ⟨q, hq, ?_⟩
      rw [hnp.tail_eq hua hza]
      exact hstep

/-- **Upper bound.** Values within `κ` of the distances of the split are within `κ` of walks along the
arcs of `X`. -/
theorem bagDist_hi (hg : ∀ z, (g z : ℝ≥0∞) = w (t.vertM z) (t.vertM (R.double.rev z)))
    (hδ : ∀ p ∈ bagCorners Γ X, ∀ q ∈ bagCorners Γ X, δ p q ≤ κ * lvlT R.double g U Γ p q)
    (hκ0 : κ ≠ 0) (hκT : κ ≠ ⊤) (hU : 1 ≤ U) {a b : V} (ha : a ∈ bagHubs t Γ X)
    (hb : b ∈ bagHubs t Γ X) :
    bagDist t Γ X δ a b ≤ (κ * (U : ℝ≥0∞)) * distR adj w (bagArc t X) a b := by
  have hU0 : (U : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (by omega : U ≠ 0)
  have h0 : κ * (U : ℝ≥0∞) ≠ 0 := mul_ne_zero hκ0 hU0
  have hT : κ * (U : ℝ≥0∞) ≠ ⊤ := ENNReal.mul_ne_top hκT (ENNReal.natCast_ne_top U)
  rw [distR, ENNReal.mul_iInf_of_ne h0 hT]
  refine le_iInf fun r => ?_
  rw [ENNReal.mul_iInf_of_ne h0 hT]
  refine le_iInf fun hr => ?_
  obtain ⟨p₀, hp₀, hx₀, rfl⟩ := mem_bagHubs.1 ha
  have hp₀c : p₀ ∈ bagCorners Γ X := mem_bagCorners.2 ⟨hp₀, hx₀⟩
  obtain ⟨q, hq, h1⟩ := lift_walk hX hg hδ r hr hb p₀ hx₀ rfl
  calc bagDist t Γ X δ (t.vertM p₀) b
      ≤ bagDist t Γ X δ (t.vertM p₀) (t.vertM q) + bagDist t Γ X δ (t.vertM q) b :=
        hubDist_triangle _ _ _ _
    _ ≤ κ * lvlT R.double g U Γ p₀ q + bagDist t Γ X δ (t.vertM q) b := by
        refine add_le_add ?_ le_rfl
        exact (bagDist_le_step ha (vertM_mem_bagHubs hq)).trans
          ((bagStep_le hp₀c hq).trans (hδ p₀ hp₀c q hq))
    _ ≤ κ * ((U : ℝ≥0∞) * r.wt w) := h1
    _ = (κ * (U : ℝ≥0∞)) * r.wt w := by ring

end BagDist

end RootedTree

end RotSystem

end SsspFlow
