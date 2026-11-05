import SsspFlow.TourNums

/-!
# Masses from the records of the corners of a bag

The positions on the tour through all darts decide the next corner of a dart (`next_port`), and the corners of
a bag follow its boundary in the order of these positions. So the mass from the first corner of a bag to each
of its darts is a sum over the records of the corners (`mass_port`, `mass_off`, `mass_cyc`), and these sums are
functions of a table with one record for each corner (`massT_eq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SsspFlow

open FourColor

section Cycle

variable {D : Type*} [Fintype D] [DecidableEq D] {f : Equiv.Perm D}

/-- The mass of all elements of one cycle through everything. -/
theorem cycMass_univ {g : D} (hconn : ∀ a b, fconnect f a b) :
    cycMass f Finset.univ g = Fintype.card D := by
  classical
  unfold cycMass
  rw [Finset.filter_true_of_mem fun z _ => hconn g z, Finset.card_univ]

/-- Positions on a cycle through everything, from the positions from one start. -/
theorem pos_eq_massBy {g x y : D} (hconn : ∀ a b, fconnect f a b) :
    pos f x y = massBy (pos f g) (pos f g) (Fintype.card D) x y := by
  rw [← mass_univ (hconn x y), mass_eq_massBy Finset.univ (fun z hz => (mass_univ hz).symm)
    (fun _ _ => rfl) (hconn g x) (hconn g y), cycMass_univ hconn]

/-- A position on a cycle through everything is below the number of elements. -/
theorem pos_lt_card_univ {x y : D} (hconn : ∀ a b, fconnect f a b) : pos f x y < Fintype.card D := by
  classical
  have := pos_lt_card (S := Finset.univ) f (hconn x y) (fun _ _ => Finset.mem_univ _)
  simpa using this

variable (hconn : ∀ a b : D, fconnect f a b)

include hconn in
theorem pos_cases (g x y : D) :
    pos f x y = if pos f g x ≤ pos f g y then pos f g y - pos f g x
      else Fintype.card D - (pos f g x - pos f g y) :=
  pos_eq_massBy (g := g) hconn

/-- The distance from `a` to `b` on a cycle of length at most `W`, up to the length of the cycle. -/
def keyMod (W a b : ℕ) : ℕ := (b + W - a) % W

theorem keyMod_of_le {W a b : ℕ} (h : a ≤ b) (hb : b < W) : keyMod W a b = b - a := by
  unfold keyMod
  rw [show b + W - a = (b - a) + W by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem keyMod_of_lt {W a b : ℕ} (h : b < a) (ha : a < W) : keyMod W a b = b + W - a := by
  unfold keyMod
  rw [Nat.mod_eq_of_lt (by omega)]

include hconn in
/-- The order of the positions seen from a dart, from the positions from one start. -/
theorem pos_le_iff_key {W : ℕ} (hW : Fintype.card D ≤ W) (g z p q : D) :
    pos f z p ≤ pos f z q ↔
      keyMod W (pos f g z) (pos f g p) ≤ keyMod W (pos f g z) (pos f g q) := by
  have ha := pos_lt_card_univ (x := g) (y := z) hconn
  have hb := pos_lt_card_univ (x := g) (y := p) hconn
  have hc := pos_lt_card_univ (x := g) (y := q) hconn
  rw [pos_cases hconn g z p, pos_cases hconn g z q]
  by_cases h1 : pos f g z ≤ pos f g p <;> by_cases h2 : pos f g z ≤ pos f g q
  · rw [if_pos h1, if_pos h2, keyMod_of_le h1 (by omega), keyMod_of_le h2 (by omega)]
  · rw [if_pos h1, if_neg h2, keyMod_of_le h1 (by omega), keyMod_of_lt (by omega) (by omega)]
    omega
  · rw [if_neg h1, if_pos h2, keyMod_of_lt (by omega) (by omega), keyMod_of_le h2 (by omega)]
    omega
  · rw [if_neg h1, if_neg h2, keyMod_of_lt (by omega) (by omega), keyMod_of_lt (by omega) (by omega)]
    omega

variable {ψ : Equiv.Perm D} {P : Finset D} {g₀ g : D}

include hconn in
theorem key_step (hmin : ∀ p ∈ P, p ≠ g → pos f g (ψ g) ≤ pos f g p) (hg₀ : g₀ ∈ P)
    (hfix : ψ g = g → g₀ = g) (hne : ψ g ≠ g₀) : pos f g₀ g < pos f g₀ (ψ g) := by
  by_contra hle
  have hle' : pos f g₀ (ψ g) ≤ pos f g₀ g := by omega
  have hinj : ∀ {a b : D}, pos f g₀ a = pos f g₀ b → a = b :=
    fun e => pos_inj (hconn _ _) (hconn _ _) e
  have hK0 : pos f g₀ g₀ = 0 := pos_self
  have hgne : g₀ ≠ g := by
    rintro rfl
    exact hne (hinj (by omega))
  have hh0 : pos f g₀ (ψ g) ≠ 0 := fun e => hne (hinj (by omega))
  have h1 := hmin g₀ hg₀ hgne
  rcases eq_or_lt_of_le hle' with e | hlt
  · exact hgne (hfix (hinj e))
  · rw [pos_cases hconn g₀ g (ψ g), pos_cases hconn g₀ g g₀, if_neg (by omega), if_neg (by omega)] at h1
    have := pos_lt_card_univ (x := g₀) (y := g) hconn
    omega

include hconn in
theorem key_between {p : D} (hmin : ∀ p ∈ P, p ≠ g → pos f g (ψ g) ≤ pos f g p) (hp : p ∈ P)
    (h1 : pos f g₀ g < pos f g₀ p) (h2 : pos f g₀ p < pos f g₀ (ψ g)) : False := by
  have hne : p ≠ g := by
    rintro rfl
    omega
  have h3 := hmin p hp hne
  rw [pos_cases hconn g₀ g (ψ g), pos_cases hconn g₀ g p, if_pos (by omega), if_pos (by omega)] at h3
  omega

include hconn in
theorem key_last {p : D} (hmin : ∀ p ∈ P, p ≠ g → pos f g (ψ g) ≤ pos f g p)
    (he : ψ g = g₀) (hp : p ∈ P) (hfix : ψ g = g → p = g) : pos f g₀ p ≤ pos f g₀ g := by
  by_contra hlt
  have hlt' : pos f g₀ g < pos f g₀ p := by omega
  have hne : p ≠ g := by
    rintro rfl
    omega
  have hgne : g ≠ g₀ := by
    rintro rfl
    exact hne (hfix he)
  have hK0 : pos f g₀ g₀ = 0 := pos_self
  have hg0 : pos f g₀ g ≠ 0 := fun e => hgne (pos_inj (hconn g₀ _) (hconn g₀ _) (by omega))
  have h3 := hmin p hp hne
  rw [he, pos_cases hconn g₀ g g₀, pos_cases hconn g₀ g p, if_pos hlt'.le, if_neg (by omega)] at h3
  have := pos_lt_card_univ (x := g₀) (y := p) hconn
  omega

/-- The sum of the values of the corners up to `z`, without the first corner. -/
noncomputable def offAt (f : Equiv.Perm D) (P : Finset D) (g₀ : D) (arc : D → ℕ) (z : D) : ℕ :=
  ∑ p ∈ P.filter (fun p => p ≠ g₀ ∧ pos f g₀ p ≤ pos f g₀ z), arc p

/-- The sum of the values up to a corner, where the first corner closes the cycle. -/
noncomputable def offIn (f : Equiv.Perm D) (P : Finset D) (g₀ : D) (arc : D → ℕ) (h : D) : ℕ :=
  if h = g₀ then ∑ p ∈ P, arc p else offAt f P g₀ arc h

include hconn in
theorem offAt_self (arc : D → ℕ) : offAt f P g₀ arc g₀ = 0 := by
  unfold offAt
  rw [Finset.filter_false_of_mem, Finset.sum_empty]
  rintro p - ⟨h1, h2⟩
  have hK0 : pos f g₀ g₀ = 0 := pos_self
  exact h1 (pos_inj (hconn g₀ _) (hconn g₀ _) (by omega))

include hconn in
theorem offAt_step {arc : D → ℕ} (hmin : ∀ p ∈ P, p ≠ g → pos f g (ψ g) ≤ pos f g p)
    (hg₀ : g₀ ∈ P) (hψ : ψ g ∈ P) (hfix : ψ g = g → g₀ = g) (hne : ψ g ≠ g₀) :
    offAt f P g₀ arc (ψ g) = offAt f P g₀ arc g + arc (ψ g) := by
  have hlt := key_step hconn hmin hg₀ hfix hne
  have hset : P.filter (fun p => p ≠ g₀ ∧ pos f g₀ p ≤ pos f g₀ (ψ g)) =
      insert (ψ g) (P.filter (fun p => p ≠ g₀ ∧ pos f g₀ p ≤ pos f g₀ g)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hp, hp0, hle⟩
      rcases eq_or_lt_of_le hle with e | hl
      · exact Or.inl (pos_inj (hconn _ _) (hconn _ _) e)
      · refine Or.inr ⟨hp, hp0, ?_⟩
        by_contra hc
        exact key_between hconn hmin hp (by omega) hl
    · rintro (rfl | ⟨hp, hp0, hle⟩)
      · exact ⟨hψ, hne, le_rfl⟩
      · exact ⟨hp, hp0, by omega⟩
  unfold offAt
  rw [hset, Finset.sum_insert, Nat.add_comm]
  simp only [Finset.mem_filter, not_and, not_le]
  intro _ _
  exact hlt

include hconn in
theorem offIn_step {arc : D → ℕ} {h : D}
    (hmin : ∀ g ∈ P, ∀ p ∈ P, p ≠ g → pos f g (ψ g) ≤ pos f g p) (hg₀ : g₀ ∈ P) (hh : h ∈ P)
    (hinv : ψ⁻¹ h ∈ P) (hfix : ∀ g ∈ P, ∀ p ∈ P, ψ g = g → p = g) :
    offAt f P g₀ arc (ψ⁻¹ h) + arc h = offIn f P g₀ arc h := by
  have hψ : ψ (ψ⁻¹ h) = h := perm_apply_inv_self _ _
  unfold offIn
  by_cases he : h = g₀
  · subst he
    rw [if_pos rfl]
    have hset : P.filter (fun p => p ≠ h ∧ pos f h p ≤ pos f h (ψ⁻¹ h)) = P.erase h := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hp, hp0, _⟩
        exact ⟨hp0, hp⟩
      · rintro ⟨hp0, hp⟩
        exact ⟨hp, hp0, key_last hconn (hmin _ hinv) hψ hp (hfix _ hinv p hp)⟩
    unfold offAt
    rw [hset, Finset.sum_erase_add _ _ hh]
  · rw [if_neg he]
    have h1 := offAt_step (arc := arc) hconn (hmin _ hinv) hg₀ (by rw [hψ]; exact hh)
      (hfix _ hinv _ hg₀) (by rw [hψ]; exact he)
    rw [hψ] at h1
    exact h1.symm

end Cycle

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace RootedTree

variable {V : Type*} [Fintype V] [DecidableEq V] {t : R.RootedTree V}

variable {w₀ : D × Bool} {Γ : Finset (D × Bool)} (hL : t.IsLevel Γ) (hw : w₀ ∈ Γ)
  (h₀ : t.vertM w₀ = t.root) (h₁ : w₀.2 = true)

include hL h₁ in
/-- Off the corners, the tour through all darts stays in the bag. -/
theorem same_tau_of_not_mem {z : D × Bool} (hz : z ∉ Γ) : R.Same Γ z (t.tau w₀ z) := by
  have hrot : ∀ {y : D × Bool}, y ∉ Γ → R.Same Γ y (R.double.rot y) := fun {y} hy => by
    refine (R.double.gcomp_split_iff Γ _ _).2 (Relation.EqvGen.rel _ _ (Or.inr ⟨hy, rfl⟩))
  by_cases hr : ∃ u, u ≠ t.root ∧ z = t.r0 u
  · obtain ⟨u, hu, rfl⟩ := hr
    have hn := np_of_r0_not_mem hL hu hz
    rw [tau_r0 hu]
    have h1 := (hn.gcomp_rails hL (t.vertM_r0 hu)).2
    exact Same.trans h1 (hrot (hL.c0_not_mem hn))
  by_cases hc : ∃ u, u ≠ t.root ∧ z = t.c0 u
  · obtain ⟨u, hu, rfl⟩ := hc
    rw [tau_c0 hu, ← t.rev_c0 u]
    exact same_rev Γ _
  · rw [tau_eq_rot h₁ fun v hv => ⟨fun e => hr ⟨v, hv, e⟩, fun e => hc ⟨v, hv, e⟩⟩]
    exact hrot hz

include hL h₁ in
/-- The next corner of a dart on the tour lies in its bag. -/
theorem same_of_trail {z h : D × Bool} (htr : Trail (t.tau w₀) Γ z h) : R.Same Γ z h := by
  induction htr with
  | here _ => exact connect_refl _
  | step hy _ ih => exact Same.trans (same_tau_of_not_mem hL h₁ hy) ih

/-- The next corner comes first on the tour. -/
theorem pos_trail_le {f : Equiv.Perm (D × Bool)} {S : Finset (D × Bool)} {z h p : D × Bool}
    (htr : Trail f S z h) (hp : p ∈ S) (hc : fconnect f z p) : pos f z h ≤ pos f z p := by
  obtain ⟨k, hk, hkS⟩ := trail_exists_iterate htr
  have h1 : pos f z h ≤ k := pos_le hk
  by_contra hlt
  have h2 := pos_spec hc
  exact hkS (pos f z p) (by omega) (by rw [h2]; exact hp)

include hL hw h₀ h₁ in
/-- Every dart has a next corner on the tour. -/
theorem exists_next_port (z : D × Bool) : ∃ h, Trail (t.tau w₀) Γ z h :=
  exists_trail hw (fconnect_tau h₀ h₁ z w₀)

include hL hw h₀ h₁ in
/-- **The next corner of a dart.** Among the corners of its bag, it comes first on the tour. -/
theorem next_port {z h : D × Bool} (hh : h ∈ Γ)
    (hmin : ∀ p ∈ Γ, R.Same Γ z p → pos (t.tau w₀) z h ≤ pos (t.tau w₀) z p) :
    Trail (t.tau w₀) Γ z h := by
  obtain ⟨h', htr⟩ := exists_next_port hL hw h₀ h₁ z
  have hconn := fconnect_tau (t := t) h₀ h₁
  have h1 := hmin h' htr.mem (same_of_trail hL h₁ htr)
  have h2 := pos_trail_le htr hh (hconn _ _)
  have : h = h' := pos_inj (hconn z h) (hconn z h') (le_antisymm h1 h2)
  rw [this]
  exact htr

variable (hL₀ : t.IsLevel {w₀}) (hR : R.Planar) (hc : R.Connected)
  {T₀ T : Finset (D × Bool)} (hT1 : ∀ y ∈ T, y ∈ T₀)
  (hT : ∀ y, y ∉ Γ → (∀ u, u ≠ t.root → y = t.c1 u → t.NP Γ u) → y ∈ T₀ → y ∈ T)

include hL hR hc in
/-- Corners of a bag lie on one cycle of the boundary. -/
theorem fconnect_psi_of_same {g g' : D × Bool} (hg : g ∈ Γ) (hg' : g' ∈ Γ) (hs : R.Same Γ g g') :
    fconnect (R.double.psi Γ) g g' :=
  ((R.double.split_planar (R.double_planar hR hc) (R.double_connected hc) hL.nonempty hL.skel).2.2.2
    g hg g' hg').1 hs

variable {g₀ : D × Bool} (hg₀ : g₀ ∈ Γ) {W : ℕ} {code : D × Bool → ℕ}

include hL hw h₀ h₁ hL₀ hR hc in
theorem ports_min : ∀ g ∈ R.portsOf Γ g₀, ∀ p ∈ R.portsOf Γ g₀, p ≠ g →
    pos (t.tau w₀) g (R.double.psi Γ g) ≤ pos (t.tau w₀) g p := fun _ hg _ hp hne =>
  let ⟨h1, h2⟩ := mem_portsOf.1 hg
  let ⟨h3, h4⟩ := mem_portsOf.1 hp
  pos_psi_le h₀ h₁ hL₀ hL hw hR hc h1 h3 (Same.trans (Same.symm h2) h4) hne

theorem ports_psi {g : D × Bool} (hg : g ∈ R.portsOf Γ g₀) : R.double.psi Γ g ∈ R.portsOf Γ g₀ := by
  obtain ⟨h1, h2⟩ := mem_portsOf.1 hg
  exact mem_portsOf.2 ⟨((R.double.fixesOff_psi Γ).mem_iff _).2 h1,
    Same.trans h2 (R.double.gcomp_split_of_fconnect_psi (fconnect1 _ _))⟩

theorem ports_psi_inv {h : D × Bool} (hh : h ∈ R.portsOf Γ g₀) :
    (R.double.psi Γ)⁻¹ h ∈ R.portsOf Γ g₀ := by
  obtain ⟨h1, h2⟩ := mem_portsOf.1 hh
  refine mem_portsOf.2 ⟨((R.double.fixesOff_psi Γ).inv.mem_iff _).2 h1, Same.trans h2 ?_⟩
  have h3 : R.Same Γ ((R.double.psi Γ)⁻¹ h) h := by
    have := R.double.gcomp_split_of_fconnect_psi (Γ := Γ) (fconnect1 (R.double.psi Γ) ((R.double.psi Γ)⁻¹ h))
    rwa [perm_apply_inv_self] at this
  exact Same.symm h3

include hL hR hc in
theorem ports_fix : ∀ g ∈ R.portsOf Γ g₀, ∀ p ∈ R.portsOf Γ g₀, R.double.psi Γ g = g → p = g :=
  fun _ hg _ hp he =>
    let ⟨h1, h2⟩ := mem_portsOf.1 hg
    let ⟨h3, h4⟩ := mem_portsOf.1 hp
    eq_of_fconnect_of_fixed he (fconnect_psi_of_same hL hR hc h1 h3 (Same.trans (Same.symm h2) h4))

include hL hw h₀ h₁ hL₀ hR hc hT1 hT hg₀ in
/-- The conditions of `pot_spec` for the sums over the corners. -/
theorem off_hyps : ∀ g ∈ Γ, R.Same Γ g₀ g → R.double.psi Γ g ≠ g₀ →
    offAt (t.tau w₀) (R.portsOf Γ g₀) g₀ (t.arcV Γ T₀ T w₀) (R.double.psi Γ g) =
      offAt (t.tau w₀) (R.portsOf Γ g₀) g₀ (t.arcV Γ T₀ T w₀) g +
        t.arcV Γ T₀ T w₀ (R.double.psi Γ g) := fun g hg hs hne => by
  have hgP : g ∈ R.portsOf Γ g₀ := mem_portsOf.2 ⟨hg, hs⟩
  have h0P : g₀ ∈ R.portsOf Γ g₀ := mem_portsOf.2 ⟨hg₀, connect_refl _⟩
  exact offAt_step (fconnect_tau h₀ h₁) (ports_min hL hw h₀ h₁ hL₀ hR hc _ hgP) h0P (ports_psi hgP)
    (fun e => ports_fix hL hR hc _ hgP _ h0P e) hne

include hL hw h₀ h₁ hL₀ hR hc hT1 hT hg₀ in
/-- **The mass at a corner of a bag.** -/
theorem mass_port {z : D × Bool} (hz : z ∈ Γ) (hs : R.Same Γ g₀ z) :
    mass (t.tourL Γ) T g₀ z = offAt (t.tau w₀) (R.portsOf Γ g₀) g₀ (t.arcV Γ T₀ T w₀) z :=
  (pot_spec hL hw h₀ h₁ hL₀ hR hc hT1 hT _ (offAt_self (fconnect_tau h₀ h₁) _)
    (off_hyps hL hw h₀ h₁ hL₀ hR hc hT1 hT hg₀) hg₀ z hs).1 hz

include hL hw h₀ h₁ hL₀ hR hc in
theorem offIn_ports {h : D × Bool} (hg₀ : g₀ ∈ Γ) (hh : h ∈ Γ) (hs : R.Same Γ g₀ h) (arc : D × Bool → ℕ) :
    offAt (t.tau w₀) (R.portsOf Γ g₀) g₀ arc ((R.double.psi Γ)⁻¹ h) + arc h =
      offIn (t.tau w₀) (R.portsOf Γ g₀) g₀ arc h := by
  have hhP : h ∈ R.portsOf Γ g₀ := mem_portsOf.2 ⟨hh, hs⟩
  have h0P : g₀ ∈ R.portsOf Γ g₀ := mem_portsOf.2 ⟨hg₀, connect_refl _⟩
  exact offIn_step (fconnect_tau h₀ h₁) (ports_min hL hw h₀ h₁ hL₀ hR hc) h0P hhP (ports_psi_inv hhP)
    (ports_fix hL hR hc)

include hL hw h₀ h₁ hL₀ hR hc hT1 hT hg₀ in
/-- **The mass of a bag.** It is the sum over the corners. -/
theorem mass_cyc :
    cycMass (t.tourL Γ) T g₀ = offIn (t.tau w₀) (R.portsOf Γ g₀) g₀ (t.arcV Γ T₀ T w₀) g₀ := by
  rw [← offIn_ports hL hw h₀ h₁ hL₀ hR hc hg₀ hg₀ (connect_refl _)]
  exact cyc_spec hL hw h₀ h₁ hL₀ hR hc hT1 hT _ (offAt_self (fconnect_tau h₀ h₁) _)
    (off_hyps hL hw h₀ h₁ hL₀ hR hc hT1 hT hg₀) hg₀

include hL hw h₀ h₁ hL₀ hR hc hT1 hT hg₀ in
/-- **The mass at another dart of a bag.** -/
theorem mass_off {z h : D × Bool} (hz : z ∉ Γ) (hs : R.Same Γ g₀ z)
    (htr : Trail (t.tau w₀) Γ z h) :
    mass (t.tourL Γ) T g₀ z =
      offIn (t.tau w₀) (R.portsOf Γ g₀) g₀ (t.arcV Γ T₀ T w₀) h + t.phi T₀ w₀ z -
        t.phiB T₀ T w₀ ((R.double.nodeReturn Γ)⁻¹ h) - t.arcV Γ T₀ T w₀ h := by
  obtain ⟨h1, h2⟩ := (pot_spec hL hw h₀ h₁ hL₀ hR hc hT1 hT _ (offAt_self (fconnect_tau h₀ h₁) _)
    (off_hyps hL hw h₀ h₁ hL₀ hR hc hT1 hT hg₀) hg₀ z hs).2 hz h htr
  have h3 := offIn_ports hL hw h₀ h₁ hL₀ hR hc (arc := t.arcV Γ T₀ T w₀) hg₀ htr.mem
    (Same.trans hs (same_of_trail hL h₁ htr))
  omega

/-- The codes of the corners in the table of a bag. A table holds the field `j` of the corner with code `c`
at the key `Nat.pair c j`, increased by one, and field `0` is the position on the tour through all darts. -/
def portsT (W : ℕ) (tab : ℕ → ℕ) : Finset ℕ :=
  (Finset.range W).filter fun c => tab (Nat.pair c 0) ≠ 0

/-- A field of a corner in a table. -/
def fldT (tab : ℕ → ℕ) (j c : ℕ) : ℕ := tab (Nat.pair c j) - 1

/-- The sum of a field over the corners up to the position `pz`, without the first corner. -/
noncomputable def offAtT (W : ℕ) (tab : ℕ → ℕ) (c₀ ja pz : ℕ) : ℕ :=
  ∑ c ∈ (portsT W tab).filter (fun c => c ≠ c₀ ∧
      keyMod W (fldT tab 0 c₀) (fldT tab 0 c) ≤ keyMod W (fldT tab 0 c₀) pz), fldT tab ja c

/-- The sum of a field up to a corner, where the first corner closes the cycle. -/
noncomputable def offInT (W : ℕ) (tab : ℕ → ℕ) (c₀ ja c : ℕ) : ℕ :=
  if c = c₀ then ∑ c' ∈ portsT W tab, fldT tab ja c' else offAtT W tab c₀ ja (fldT tab 0 c)

/-- The code of the next corner after the position `pz`. -/
noncomputable def nextT (W : ℕ) (tab : ℕ → ℕ) (pz : ℕ) : ℕ :=
  sInf (↑(argminF (portsT W tab) (fun c => keyMod W pz (fldT tab 0 c))) : Set ℕ)

/-- The mass from the first corner to a dart with code `cz`, position `pz` and number `φz` on the first tour. -/
noncomputable def massT (W : ℕ) (tab : ℕ → ℕ) (c₀ ja jb cz pz φz : ℕ) : ℕ :=
  if cz ∈ portsT W tab then offAtT W tab c₀ ja pz
  else offInT W tab c₀ ja (nextT W tab pz) + φz - fldT tab jb (nextT W tab pz) -
    fldT tab ja (nextT W tab pz)

/-- The table of a bag holds the records of its corners. -/
structure TabOK (W : ℕ) (tab : ℕ → ℕ) (P : Finset (D × Bool)) (code : D × Bool → ℕ)
    (px ar br : D × Bool → ℕ) (ja jb : ℕ) : Prop where
  px : ∀ p ∈ P, tab (Nat.pair (code p) 0) = px p + 1
  ar : ∀ p ∈ P, tab (Nat.pair (code p) ja) = ar p + 1
  br : ∀ p ∈ P, tab (Nat.pair (code p) jb) = br p + 1
  none : ∀ c, (∀ p ∈ P, code p ≠ c) → tab (Nat.pair c 0) = 0

section Table

variable {W : ℕ} {tab : ℕ → ℕ} {code : D × Bool → ℕ} {px ar br : D × Bool → ℕ} {ja jb : ℕ}
  (hinj : Function.Injective code) (hcW : ∀ z, code z < W)

include hcW in
theorem TabOK.ports {P : Finset (D × Bool)} (hT : TabOK W tab P code px ar br ja jb) :
    portsT W tab = P.image code := by
  ext c
  simp only [portsT, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨_, h2⟩
    by_contra hno
    exact h2 (hT.none c fun p hp e => hno ⟨p, hp, e⟩)
  · rintro ⟨p, hp, rfl⟩
    refine ⟨hcW p, ?_⟩
    rw [hT.px p hp]
    omega

theorem TabOK.fld0 {P : Finset (D × Bool)} (hT : TabOK W tab P code px ar br ja jb) {p : D × Bool}
    (hp : p ∈ P) : fldT tab 0 (code p) = px p := by
  unfold fldT
  rw [hT.px p hp]
  rfl

theorem TabOK.flda {P : Finset (D × Bool)} (hT : TabOK W tab P code px ar br ja jb) {p : D × Bool}
    (hp : p ∈ P) : fldT tab ja (code p) = ar p := by
  unfold fldT
  rw [hT.ar p hp]
  rfl

theorem TabOK.fldb {P : Finset (D × Bool)} (hT : TabOK W tab P code px ar br ja jb) {p : D × Bool}
    (hp : p ∈ P) : fldT tab jb (code p) = br p := by
  unfold fldT
  rw [hT.br p hp]
  rfl

variable {f : Equiv.Perm (D × Bool)} {x₀ : D × Bool} (hconn : ∀ a b, fconnect f a b)
  (hW : Fintype.card (D × Bool) ≤ W)

include hinj hcW hconn hW in
theorem offAtT_eq {P : Finset (D × Bool)} (hT : TabOK W tab P code (pos f x₀) ar br ja jb)
    {g₀ : D × Bool} (hg₀ : g₀ ∈ P) (z : D × Bool) :
    offAtT W tab (code g₀) ja (pos f x₀ z) = offAt f P g₀ ar z := by
  unfold offAtT offAt
  rw [hT.ports hcW, Finset.filter_image, Finset.sum_image fun _ _ _ _ e => hinj e]
  refine Finset.sum_congr (Finset.filter_congr fun p hp => ?_) fun p hp =>
    hT.flda (Finset.mem_filter.1 hp).1
  rw [hT.fld0 hg₀, hT.fld0 hp, ← pos_le_iff_key hconn hW x₀ g₀ p z]
  simp only [ne_eq, hinj.eq_iff]

include hinj hcW hconn hW in
theorem offInT_eq {P : Finset (D × Bool)} (hT : TabOK W tab P code (pos f x₀) ar br ja jb)
    {g₀ h : D × Bool} (hg₀ : g₀ ∈ P) (hh : h ∈ P) :
    offInT W tab (code g₀) ja (code h) = offIn f P g₀ ar h := by
  unfold offInT offIn
  by_cases he : h = g₀
  · rw [if_pos (by rw [he]), if_pos he, hT.ports hcW, Finset.sum_image fun _ _ _ _ e => hinj e]
    exact Finset.sum_congr rfl fun p hp => hT.flda hp
  · rw [if_neg fun e => he (hinj e), if_neg he, hT.fld0 hh]
    exact offAtT_eq hinj hcW hconn hW hT hg₀ h

include hinj hcW hconn hW in
theorem nextT_eq {P : Finset (D × Bool)} (hT : TabOK W tab P code (pos f x₀) ar br ja jb)
    {z h : D × Bool} (hh : h ∈ P) (hmin : ∀ p ∈ P, pos f z h ≤ pos f z p) :
    nextT W tab (pos f x₀ z) = code h := by
  have hset : argminF (portsT W tab) (fun c => keyMod W (pos f x₀ z) (fldT tab 0 c)) = {code h} := by
    ext c
    rw [mem_argminF, Finset.mem_singleton, hT.ports hcW]
    constructor
    · rintro ⟨hc, hc2⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
      have h1 := hc2 _ (Finset.mem_image_of_mem code hh)
      rw [hT.fld0 hp, hT.fld0 hh, ← pos_le_iff_key hconn hW x₀ z p h] at h1
      rw [pos_inj (hconn z p) (hconn z h) (le_antisymm h1 (hmin p hp))]
    · rintro rfl
      refine ⟨Finset.mem_image_of_mem code hh, fun c hc => ?_⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
      rw [hT.fld0 hp, hT.fld0 hh, ← pos_le_iff_key hconn hW x₀ z h p]
      exact hmin p hp
  unfold nextT
  rw [hset]
  simp

end Table

variable (hinj : Function.Injective code) (hcW : ∀ z, code z < W)
  (hW : Fintype.card (D × Bool) ≤ W)

include hL hw h₀ h₁ hL₀ hR hc hT1 hT hg₀ hinj hcW hW in
/-- **The mass from the first corner to a dart, from the table of its bag.** -/
theorem massT_eq {tab : ℕ → ℕ} {ja jb : ℕ}
    (hTab : TabOK W tab (R.portsOf Γ g₀) code (pos (t.tau w₀) w₀) (t.arcV Γ T₀ T w₀)
      (fun p => t.phiB T₀ T w₀ ((R.double.nodeReturn Γ)⁻¹ p)) ja jb)
    {z : D × Bool} (hs : R.Same Γ g₀ z) :
    massT W tab (code g₀) ja jb (code z) (pos (t.tau w₀) w₀ z) (t.phi T₀ w₀ z) =
      mass (t.tourL Γ) T g₀ z := by
  have hconn := fconnect_tau (t := t) h₀ h₁
  have h0P : g₀ ∈ R.portsOf Γ g₀ := mem_portsOf.2 ⟨hg₀, connect_refl _⟩
  unfold massT
  by_cases hz : z ∈ Γ
  · have hzP : z ∈ R.portsOf Γ g₀ := mem_portsOf.2 ⟨hz, hs⟩
    rw [if_pos (by rw [hTab.ports hcW]; exact Finset.mem_image_of_mem code hzP),
      offAtT_eq hinj hcW hconn hW hTab h0P, mass_port hL hw h₀ h₁ hL₀ hR hc hT1 hT hg₀ hz hs]
  · rw [if_neg]
    · obtain ⟨h, htr⟩ := exists_next_port hL hw h₀ h₁ z
      have hhP : h ∈ R.portsOf Γ g₀ :=
        mem_portsOf.2 ⟨htr.mem, Same.trans hs (same_of_trail hL h₁ htr)⟩
      have hn := nextT_eq hinj hcW hconn hW hTab (z := z) hhP fun p hp =>
        pos_trail_le htr (mem_portsOf.1 hp).1 (hconn _ _)
      rw [hn, offInT_eq hinj hcW hconn hW hTab h0P hhP, hTab.fldb hhP, hTab.flda hhP,
        mass_off hL hw h₀ h₁ hL₀ hR hc hT1 hT hg₀ hz hs htr]
    · rw [hTab.ports hcW]
      intro hm
      obtain ⟨p, hp, e⟩ := Finset.mem_image.1 hm
      exact hz (hinj e ▸ (mem_portsOf.1 hp).1)

include hL hw h₀ h₁ hL₀ hR hc hT1 hT hg₀ hinj hcW hW in
/-- **The mass of a bag, from its table.** -/
theorem cycT_eq {tab : ℕ → ℕ} {ja jb : ℕ}
    (hTab : TabOK W tab (R.portsOf Γ g₀) code (pos (t.tau w₀) w₀) (t.arcV Γ T₀ T w₀)
      (fun p => t.phiB T₀ T w₀ ((R.double.nodeReturn Γ)⁻¹ p)) ja jb) :
    ∑ c ∈ portsT W tab, fldT tab ja c = cycMass (t.tourL Γ) T g₀ := by
  have hconn := fconnect_tau (t := t) h₀ h₁
  have h0P : g₀ ∈ R.portsOf Γ g₀ := mem_portsOf.2 ⟨hg₀, connect_refl _⟩
  rw [mass_cyc hL hw h₀ h₁ hL₀ hR hc hT1 hT hg₀, ← offInT_eq hinj hcW hconn hW hTab h0P h0P]
  unfold offInT
  rw [if_pos rfl]

end RootedTree

end RotSystem

end SsspFlow
