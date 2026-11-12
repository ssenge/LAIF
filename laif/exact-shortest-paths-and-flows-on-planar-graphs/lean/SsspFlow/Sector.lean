import SsspFlow.Select

/-!
# Distances in a bag between darts

Two darts are linked if one is the reverse of the other, or if they lie at one vertex of the split map. Within a
bag, every two darts are at small distance for these links (`dart_diam`). A flood along them finds the name of
a bag.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SsspFlow

open FourColor

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D}

variable (R) in
/-- Reverse darts, and darts at one vertex of the split map. -/
def dartLink (Γ : Finset (D × Bool)) (x y : D × Bool) : Prop :=
  y = R.double.rev x ∨ (R.double.split Γ).tail x = (R.double.split Γ).tail y

variable {Γ : Finset (D × Bool)}

theorem dartLink_symm {x y : D × Bool} (h : R.dartLink Γ x y) : R.dartLink Γ y x := by
  rcases h with rfl | h
  · exact Or.inl (R.double.rev_rev x).symm
  · exact Or.inr h.symm

theorem same_of_dartLink {x y : D × Bool} (h : R.dartLink Γ x y) : R.Same Γ x y := by
  rcases h with rfl | h
  · exact same_rev Γ x
  · exact (R.double.split Γ).toHypermap.gcomp_of_cnode (((R.double.split Γ).tail_eq_iff x y).1 h)

variable (R) in
/-- The links in the bag of `u`. -/
def bagLink (Γ : Finset (D × Bool)) (u x y : D × Bool) : Prop := R.Same Γ u x ∧ R.dartLink Γ x y

theorem bagLink_symm {u x y : D × Bool} (h : R.bagLink Γ u x y) : R.bagLink Γ u y x :=
  ⟨Same.trans h.1 (same_of_dartLink h.2), dartLink_symm h.2⟩

/-- A bag is connected by its links. -/
theorem reach_bagLink {u x y : D × Bool} (hx : R.Same Γ u x) (h : R.Same Γ x y) :
    Relation.ReflTransGen (R.bagLink Γ u) x y := by
  have hsym : ∀ {a b : D × Bool}, Relation.ReflTransGen (R.bagLink Γ u) a b →
      Relation.ReflTransGen (R.bagLink Γ u) b a := by
    intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact (Relation.ReflTransGen.single (bagLink_symm hbc)).trans ih
  have h' := (R.double.gcomp_split_iff Γ x y).1 h
  clear h
  revert hx
  induction h' with
  | rel a b hab =>
    intro ha
    refine Relation.ReflTransGen.single ⟨ha, ?_⟩
    rcases hab with rfl | ⟨hn, rfl⟩
    · exact Or.inl rfl
    · refine Or.inr ?_
      rw [← split_rot_of_not_mem _ hn, (R.double.split Γ).tail_rot]
  | refl a => exact fun _ => Relation.ReflTransGen.refl
  | symm a b hab ih =>
    intro hb
    exact hsym (ih (Same.trans hb ((R.double.gcomp_split_iff Γ b a).2 (Relation.EqvGen.symm _ _ hab))))
  | trans a b c hab _ ih1 ih2 =>
    intro ha
    exact (ih1 ha).trans (ih2 (Same.trans ha ((R.double.gcomp_split_iff Γ a b).2 hab)))

namespace RootedTree

variable {V : Type*} [Fintype V] [DecidableEq V] {t : R.RootedTree V}

/-- From a dart, a walk up the tree in the bag reaches a corner of the bag. -/
theorem up_link {u : D × Bool} (hL : t.IsLevel Γ) (n : ℕ) :
    ∀ z, t.dep (t.vertM z) = n → R.Same Γ u z →
      ∃ g ∈ Γ, R.Same Γ u g ∧ ReachLE (R.bagLink Γ u) (2 * n + 1) z g := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z hn hz
    by_cases hv : t.NP Γ (t.vertM z)
    · have hne := hv.ne_root hL
      have h1 : R.dartLink Γ z (t.c1 (t.vertM z)) := Or.inr (hv.tail_eq rfl (t.vertM_c1 hne))
      have h2 : R.dartLink Γ (t.c1 (t.vertM z)) (t.c0 (t.vertM z)) := Or.inl (t.rev_c1 _).symm
      have hz1 := Same.trans hz (same_of_dartLink h1)
      have hz2 := Same.trans hz1 (same_of_dartLink h2)
      obtain ⟨g, hg, hug, hr⟩ := ih (t.dep (t.vertM (t.c0 (t.vertM z))))
        (by rw [t.vertM_c0, ← hn]; exact t.dep_par_lt hne) _ rfl hz2
      refine ⟨g, hg, hug, (((ReachLE.of_adj ⟨hz, h1⟩).trans (ReachLE.of_adj ⟨hz1, h2⟩)).trans hr).mono ?_⟩
      have := t.dep_par_lt hne
      rw [t.vertM_c0]
      omega
    · obtain ⟨g, hg, _, hs⟩ := exists_port_tail hv
      have h1 : R.dartLink Γ z g := Or.inr hs
      exact ⟨g, hg, Same.trans hz (same_of_dartLink h1), (ReachLE.of_adj ⟨hz, h1⟩).mono (by omega)⟩

/-- From a digon corner, the reverse lies at the vertex of the split map of the first return of the boundary
of the disk. -/
theorem tail_psi_digon (hL : t.IsLevel Γ) {g : D × Bool} (hg : g ∈ Γ) (h0 : g.2 = false) :
    (R.double.split Γ).tail (R.double.rev g) = (R.double.split Γ).tail (R.double.psi Γ g) := by
  obtain ⟨d, b⟩ := g
  obtain rfl : b = false := h0
  have hb : R.double.faceReturn Γ (d, false) = (R.rev d, false) :=
    firstReturn_eq_of_trail _ hg (Trail.here (hL.pairs d hg))
  have he : (R.rev d, false) ∈ Γ := hL.pairs d hg
  have htr := firstReturn_trail R.double.rot he
  have h1 := split_tail_of_trail htr
  have h2 : R.double.rot (R.rev d, false) = R.double.rev (d, false) := rfl
  rw [h2] at h1
  show _ = (R.double.split Γ).tail (R.double.nodeReturn Γ (R.double.faceReturn Γ (d, false)))
  rw [hb]
  exact h1

/-- **The diameter of a bag for links between darts.** -/
theorem dart_diam (hL : t.IsLevel Γ) (hR : R.Planar) (hc : R.Connected) {u : D × Bool} {h J G : ℕ}
    (hdep : ∀ v, t.dep v ≤ h) (hJ : (R.portsOf Γ u).card ≤ J) (hG : (R.gapsOf Γ u).card ≤ G)
    {a b : D × Bool} (ha : R.Same Γ u a) (hb : R.Same Γ u b) :
    ReachLE (R.bagLink Γ u) ((G + 1) * (2 * (2 * h + 1 + 2 * J) + 1)) a b := by
  classical
  have hMP := R.double_planar hR hc
  have hMc := R.double_connected hc
  have horb := (R.double.split_planar hMP hMc hL.nonempty hL.skel).2.2.2
  obtain ⟨g₀, hg₀, hug₀⟩ := R.double.split_meets hMc hL.nonempty u
  let T : Finset (D × Bool) := insert g₀ (R.gapsOf Γ u)
  have hTΓ : ∀ y ∈ T, y ∈ Γ ∧ R.Same Γ u y := by
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact ⟨hg₀, hug₀⟩
    · obtain ⟨h1, _, h3⟩ := mem_gapsOf.1 hy
      exact ⟨h1, h3⟩
  have hreach : ∀ a ∈ {z | R.Same Γ u z}, ∃ c ∈ T, c ∈ {z | R.Same Γ u z} ∧
      ReachLE (R.bagLink Γ u) (2 * h + 1 + 2 * J) a c := by
    intro z hz
    obtain ⟨g, hg, hug, hr1⟩ := up_link (u := u) hL _ z rfl hz
    have hor : ∀ y, y ∈ Γ → R.Same Γ u y → fconnect (R.double.psi Γ) g y :=
      fun y hy huy => (horb g hg y hy).1 (Same.trans (Same.symm hug) huy)
    obtain ⟨y, hyT, hmin⟩ := T.exists_min_image (pos (R.double.psi Γ) g) ⟨g₀, Finset.mem_insert_self _ _⟩
    obtain ⟨hyΓ, huy⟩ := hTΓ y hyT
    have hgy := hor y hyΓ huy
    have hit : ∀ i, i ≤ pos (R.double.psi Γ) g y →
        (⇑(R.double.psi Γ))^[i] g ∈ Γ ∧ R.Same Γ u ((⇑(R.double.psi Γ))^[i] g) ∧
          ReachLE (R.bagLink Γ u) (2 * i) g ((⇑(R.double.psi Γ))^[i] g) := by
      intro i
      induction i with
      | zero => exact fun _ => ⟨hg, hug, ReachLE.refl _⟩
      | succ i ih =>
        intro hi
        obtain ⟨h1, h2, h3⟩ := ih (by omega)
        rw [Function.iterate_succ_apply']
        have hm := ((R.double.fixesOff_psi Γ).mem_iff _).2 h1
        have hs : R.Same Γ ((⇑(R.double.psi Γ))^[i] g) (R.double.psi Γ ((⇑(R.double.psi Γ))^[i] g)) :=
          R.double.gcomp_split_of_fconnect_psi (fconnect1 _ _)
        refine ⟨hm, Same.trans h2 hs, ?_⟩
        have hb0 : ((⇑(R.double.psi Γ))^[i] g).2 = false := by
          by_contra hne
          have htrue : ((⇑(R.double.psi Γ))^[i] g).2 = true := by simpa using hne
          have hmem : (⇑(R.double.psi Γ))^[i] g ∈ T :=
            Finset.mem_insert_of_mem (mem_gapsOf.2 ⟨h1, htrue, h2⟩)
          have h4 := hmin _ hmem
          have h5 : pos (R.double.psi Γ) g ((⇑(R.double.psi Γ))^[i] g) ≤ i := pos_le rfl
          omega
        have hd := tail_psi_digon hL h1 hb0
        have hl1 : R.dartLink Γ ((⇑(R.double.psi Γ))^[i] g) (R.double.rev ((⇑(R.double.psi Γ))^[i] g)) :=
          Or.inl rfl
        have hl2 : R.dartLink Γ (R.double.rev ((⇑(R.double.psi Γ))^[i] g))
            (R.double.psi Γ ((⇑(R.double.psi Γ))^[i] g)) := Or.inr hd
        have h6 := ((h3.trans (ReachLE.of_adj ⟨h2, hl1⟩)).trans
          (ReachLE.of_adj ⟨Same.trans h2 (same_of_dartLink hl1), hl2⟩))
        exact h6.mono (by omega)
    obtain ⟨_, h2, h3⟩ := hit _ le_rfl
    rw [pos_spec hgy] at h2 h3
    have hposJ : pos (R.double.psi Γ) g y < (R.portsOf Γ u).card := by
      refine pos_lt_card _ hgy fun z hz' => mem_portsOf.2 ?_
      constructor
      · have := fconnect_iff_iterate.1 hz'
        obtain ⟨n, rfl⟩ := this
        have key : ∀ n, (⇑(R.double.psi Γ))^[n] g ∈ Γ := by
          intro n
          induction n with
          | zero => exact hg
          | succ n ih =>
            rw [Function.iterate_succ_apply']
            exact ((R.double.fixesOff_psi Γ).mem_iff _).2 ih
        exact key n
      · exact Same.trans hug (R.double.gcomp_split_of_fconnect_psi hz')
    refine ⟨y, hyT, huy, (hr1.trans h3).mono ?_⟩
    have := hdep (t.vertM z)
    omega
  have hcard : T.card ≤ G + 1 := by
    calc T.card ≤ (R.gapsOf Γ u).card + 1 := Finset.card_insert_le _ _
      _ ≤ G + 1 := by omega
  have hconn : ∀ a ∈ {z | R.Same Γ u z}, ∀ b ∈ {z | R.Same Γ u z},
      Relation.ReflTransGen (R.bagLink Γ u) a b := fun a ha b hb =>
    reach_bagLink ha (Same.trans (Same.symm ha) hb)
  have := centers_diam (fun a b h => bagLink_symm h) hconn
    (fun a b h => ⟨h.1, Same.trans h.1 (same_of_dartLink h.2)⟩) hreach ha hb
  exact this.mono (Nat.mul_le_mul_right _ hcard)

namespace Decomp

variable {w₀ : D × Bool} {Γs C : ℕ → Finset (D × Bool)}

/-- The diameter of all bags of a decomposition, up to depth `H`. -/
theorem dart_span (hD : t.Decomp w₀ Γs C) (hR : R.Planar) (hc : R.Connected) {h H d : ℕ}
    (hdep : ∀ v, t.dep v ≤ h) (hd : d ≤ H) {u a b : D × Bool} (ha : R.Same (Γs d) u a)
    (hb : R.Same (Γs d) u b) :
    ReachLE (R.bagLink (Γs d) u) ((2 * H + 2) * (2 * (2 * h + 1 + 2 * (1 + H * (2 + 4 * h))) + 1)) a b := by
  have hJ : (R.portsOf (Γs d) u).card ≤ 1 + H * (2 + 4 * h) := by
    have h1 := hD.card_ports hdep d u
    have h2 : d * (2 + 4 * h) ≤ H * (2 + 4 * h) := Nat.mul_le_mul_right _ hd
    omega
  have hG : (R.gapsOf (Γs d) u).card ≤ 2 * H + 1 := by
    have h1 := hD.card_gaps d u
    omega
  exact dart_diam (hD.level d) hR hc hdep hJ hG ha hb

end Decomp

end RootedTree

end RotSystem

end SsspFlow
