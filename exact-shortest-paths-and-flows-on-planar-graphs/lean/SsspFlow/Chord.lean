import SsspFlow.Splice

/-!
# Chords and restrictions of a rotation system

All maps of one argument live on one dart type. A deleted edge is an isolated edge, and a free chord
is an isolated edge, so restricting and adding chords never change the type.

* The transposition lemma: multiplying a permutation by `swap x y` splits an orbit if `x` and `y`
  lie in one orbit and merges two orbits otherwise (`orb_mul_swap_of_fconnect`,
  `orb_mul_swap_of_not_fconnect`). Inserting a point in the set of a first return puts it right
  after its predecessor (`firstReturn_insert`).
* `attach c x` puts the dart `c`, a fixed point of `rot`, into the corner `x`.
  `genus_attach_of_fconnect`, `genus_attach_of_gcomp`, `genus_attach_of_not_gcomp` give the genus in
  the three possible cases, and `genus_le_attach` says that it never drops.
* `chord c x y`, for an isolated edge `c`, puts `c` into the corner `x` and `rev c` into the corner
  `y`. A chord between two corners of one face keeps the genus (`genus_chord_of_fconnect`) and
  splits the face (`not_fconnect_chord`, `fconnect_chord_cases`). A chord between two faces of one
  component raises the genus by one (`genus_chord_of_not_fconnect`).
* `restrict A` has the rotation `firstReturn rot A`, so darts off `A` become isolated.
  Adding a dart to a restriction is an attach (`restrict_insert`), so the genus does not rise
  (`genus_restrict_le`). `predIn A x` is the last dart of `A` at or before `x` in the rotation,
  `attach_restrict` commutes attach and restriction, and `restrict_chord` commutes chord and
  restriction. Then `fconnect_predIn_of_fconnect`: two corners of one face of a planar map lie in
  one face of every connected restriction.
* `genus_twisted`: two chords between the same two corners in the same order at both ends raise the
  genus.
* `lift k` adds `k` isolated edges and changes nothing else.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor

section Swap

variable {D : Type*} [Fintype D] [DecidableEq D]

omit [Fintype D] [DecidableEq D] in
/-- The orbit of a fixed point is the point. -/
theorem eq_of_fconnect_of_fixed {g : D → D} {x y : D} (hg : g x = x) (h : fconnect g x y) :
    y = x := by
  obtain ⟨n, rfl⟩ := fconnect_iff_iterate.1 h
  exact Function.iterate_fixed hg n

omit [Fintype D] [DecidableEq D] in
theorem perm_inv_apply_self (f : Equiv.Perm D) (x : D) : f⁻¹ (f x) = x := f.symm_apply_apply x

omit [Fintype D] [DecidableEq D] in
theorem perm_apply_inv_self (f : Equiv.Perm D) (x : D) : f (f⁻¹ x) = x := f.apply_symm_apply x

omit [Fintype D] [DecidableEq D] in
/-- The inverse of a permutation has the same orbits. -/
theorem fconnect_inv_iff [Finite D] (g : Equiv.Perm D) {x y : D} :
    fconnect (⇑g⁻¹) x y ↔ fconnect g x y :=
  fconnect_inverse (f := ⇑g) (g := ⇑g⁻¹) g.symm_apply_apply g.apply_symm_apply

omit [Fintype D] in
theorem fixesOff_swap_of_mem {S : Finset D} {x y : D} (hx : x ∈ S) (hy : y ∈ S) :
    FixesOff (Equiv.swap x y) S := fun _ hz =>
  Equiv.swap_apply_of_ne_of_ne (fun e => hz (e ▸ hx)) (fun e => hz (e ▸ hy))

omit [Fintype D] in
theorem fixesOff_swap_pair (x y : D) : FixesOff (Equiv.swap x y) {x, y} :=
  fixesOff_swap_of_mem (by simp) (by simp)

/-- A transposition has one orbit less than the identity. -/
theorem orb_swap {x y : D} (hxy : x ≠ y) : orb (Equiv.swap x y) + 1 = Fintype.card D := by
  have h := orb_eq_add_card (fixesOff_swap_pair x y)
  have h1 : fcard (Equiv.swap x y) (({x, y} : Finset D) : Set D) = 1 := by
    refine nComp_eq_one_of_connect (fconnect_sym (Equiv.swap x y).injective) ⟨x, by simp⟩ ?_
    have hxy' : fconnect (Equiv.swap x y) x y := connect_of_rel (Equiv.swap_apply_left x y)
    have hyx' : fconnect (Equiv.swap x y) y x := connect_of_rel (Equiv.swap_apply_right x y)
    intro a ha b hb
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact connect_refl _
    · exact hxy'
    · exact hyx'
    · exact connect_refl _
  have h2 := Finset.card_add_card_compl ({x, y} : Finset D)
  rw [Finset.card_pair hxy] at h2
  omega

/-- The first return to two points of one orbit exchanges them. -/
theorem firstReturn_pair_of_fconnect (f : Equiv.Perm D) {x y : D} (hxy : x ≠ y)
    (h : fconnect f x y) : firstReturn f {x, y} = Equiv.swap x y := by
  have hxS : x ∈ ({x, y} : Finset D) := by simp
  have hyS : y ∈ ({x, y} : Finset D) := by simp
  have h1 : fconnect (firstReturn f {x, y}) x y := (fconnect_firstReturn_iff f hxS hyS).2 h
  have h2 : fconnect (firstReturn f {x, y}) y x :=
    fconnect_sym (firstReturn f {x, y}).injective _ _ h1
  have hx : firstReturn f {x, y} x = y := by
    have hm := (firstReturn_mem_iff f {x, y} x).2 hxS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exact absurd (eq_of_fconnect_of_fixed hm h1).symm hxy
    · exact hm
  have hy : firstReturn f {x, y} y = x := by
    have hm := (firstReturn_mem_iff f {x, y} y).2 hyS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exact hm
    · exact absurd (eq_of_fconnect_of_fixed hm h2) hxy
  ext z
  by_cases hzx : z = x
  · rw [hzx, hx, Equiv.swap_apply_left]
  by_cases hzy : z = y
  · rw [hzy, hy, Equiv.swap_apply_right]
  · rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
    exact firstReturn_of_not_mem f (by simp [hzx, hzy])

/-- The first return to two points of different orbits fixes them. -/
theorem firstReturn_pair_of_not_fconnect (f : Equiv.Perm D) {x y : D} (h : ¬ fconnect f x y) :
    firstReturn f {x, y} = 1 := by
  have hx : firstReturn f {x, y} x = x := by
    have hm := (firstReturn_mem_iff f {x, y} x).2 (by simp)
    have hc := fconnect_firstReturn f {x, y} x
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exact hm
    · rw [hm] at hc
      exact absurd hc h
  have hy : firstReturn f {x, y} y = y := by
    have hm := (firstReturn_mem_iff f {x, y} y).2 (by simp)
    have hc := fconnect_firstReturn f {x, y} y
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · rw [hm] at hc
      exact absurd (fconnect_sym f.injective _ _ hc) h
    · exact hm
  ext z
  rw [Equiv.Perm.one_apply]
  by_cases hzx : z = x
  · rw [hzx, hx]
  by_cases hzy : z = y
  · rw [hzy, hy]
  · exact firstReturn_of_not_mem f (by simp [hzx, hzy])

/-- **Transposition lemma**, one orbit: the orbit splits. -/
theorem orb_mul_swap_of_fconnect (f : Equiv.Perm D) {x y : D} (hxy : x ≠ y) (h : fconnect f x y) :
    orb (f * Equiv.swap x y) = orb f + 1 := by
  have h1 := orb_mul_right f (fixesOff_swap_pair x y)
  rw [firstReturn_pair_of_fconnect f hxy h, Equiv.swap_mul_self, orb_one] at h1
  have h2 := orb_swap hxy
  omega

/-- **Transposition lemma**, two orbits: they merge. -/
theorem orb_mul_swap_of_not_fconnect (f : Equiv.Perm D) {x y : D} (h : ¬ fconnect f x y) :
    orb (f * Equiv.swap x y) + 1 = orb f := by
  have hxy : x ≠ y := fun e => h (e ▸ connect_refl x)
  have h1 := orb_mul_right f (fixesOff_swap_pair x y)
  rw [firstReturn_pair_of_not_fconnect f h, one_mul, orb_one] at h1
  have h2 := orb_swap hxy
  omega

theorem orb_swap_mul_of_fconnect (f : Equiv.Perm D) {x y : D} (hxy : x ≠ y) (h : fconnect f x y) :
    orb (Equiv.swap x y * f) = orb f + 1 := by
  have h1 := orb_mul_left f (fixesOff_swap_pair x y)
  rw [firstReturn_pair_of_fconnect f hxy h, Equiv.swap_mul_self, orb_one] at h1
  have h2 := orb_swap hxy
  omega

theorem orb_swap_mul_of_not_fconnect (f : Equiv.Perm D) {x y : D} (h : ¬ fconnect f x y) :
    orb (Equiv.swap x y * f) + 1 = orb f := by
  have hxy : x ≠ y := fun e => h (e ▸ connect_refl x)
  have h1 := orb_mul_left f (fixesOff_swap_pair x y)
  rw [firstReturn_pair_of_not_fconnect f h, mul_one, orb_one] at h1
  have h2 := orb_swap hxy
  omega

/-- After a split the two points lie in different orbits. -/
theorem not_fconnect_mul_swap (f : Equiv.Perm D) {x y : D} (hxy : x ≠ y) (h : fconnect f x y) :
    ¬ fconnect (f * Equiv.swap x y) x y := by
  intro h'
  have h1 := orb_mul_swap_of_fconnect f hxy h
  have h2 := orb_mul_swap_of_fconnect (f * Equiv.swap x y) hxy h'
  rw [mul_assoc, Equiv.swap_mul_self, mul_one] at h2
  omega

theorem not_fconnect_swap_mul (f : Equiv.Perm D) {x y : D} (hxy : x ≠ y) (h : fconnect f x y) :
    ¬ fconnect (Equiv.swap x y * f) x y := by
  intro h'
  have h1 := orb_swap_mul_of_fconnect f hxy h
  have h2 := orb_swap_mul_of_fconnect (Equiv.swap x y * f) hxy h'
  rw [← mul_assoc, Equiv.swap_mul_self, one_mul] at h2
  omega

/-- After a merge the two points lie in one orbit. -/
theorem fconnect_mul_swap_of_not (f : Equiv.Perm D) {x y : D} (h : ¬ fconnect f x y) :
    fconnect (f * Equiv.swap x y) x y := by
  by_contra h'
  have h1 := orb_mul_swap_of_not_fconnect f h
  have h2 := orb_mul_swap_of_not_fconnect (f * Equiv.swap x y) h'
  rw [mul_assoc, Equiv.swap_mul_self, mul_one] at h2
  omega

theorem fconnect_swap_mul_of_not (f : Equiv.Perm D) {x y : D} (h : ¬ fconnect f x y) :
    fconnect (Equiv.swap x y * f) x y := by
  by_contra h'
  have h1 := orb_swap_mul_of_not_fconnect f h
  have h2 := orb_swap_mul_of_not_fconnect (Equiv.swap x y * f) h'
  rw [← mul_assoc, Equiv.swap_mul_self, one_mul] at h2
  omega

/-- A merge keeps what was connected before. -/
theorem fconnect_swap_mul_of_fconnect (f : Equiv.Perm D) {x y a b : D} (h : ¬ fconnect f x y)
    (hab : fconnect f a b) : fconnect (Equiv.swap x y * f) a b := by
  have hxy := fconnect_swap_mul_of_not f h
  have hyx := fconnect_sym (Equiv.swap x y * f).injective _ _ hxy
  refine connect_sub (fun u v huv => ?_) hab
  obtain rfl : f u = v := huv
  by_cases h1 : f u = x
  · have h3 : (Equiv.swap x y * f) u = y := by
      rw [Equiv.Perm.mul_apply, h1, Equiv.swap_apply_left]
    rw [h1]
    exact connect_trans (connect_of_rel h3) hyx
  by_cases h2 : f u = y
  · have h3 : (Equiv.swap x y * f) u = x := by
      rw [Equiv.Perm.mul_apply, h2, Equiv.swap_apply_right]
    rw [h2]
    exact connect_trans (connect_of_rel h3) hxy
  · exact connect_of_rel (show (Equiv.swap x y * f) u = f u by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2])

omit [Fintype D] in
/-- An orbit that misses both points does not change. -/
theorem fconnect_swap_mul_iff (f : Equiv.Perm D) {x y a b : D} (hx : ¬ fconnect f a x)
    (hy : ¬ fconnect f a y) : fconnect (Equiv.swap x y * f) a b ↔ fconnect f a b := by
  have key : ∀ u, fconnect f a u → (Equiv.swap x y * f) u = f u := fun u hu => by
    have h1 : f u ≠ x := fun e => hx (connect_trans hu (connect_of_rel e))
    have h2 : f u ≠ y := fun e => hy (connect_trans hu (connect_of_rel e))
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
  constructor
  · intro h
    induction h with
    | refl => exact connect_refl _
    | @tail u v _ huv ih =>
      obtain rfl : (Equiv.swap x y * f) u = v := huv
      rw [key u ih]
      exact connect_trans ih (connect_of_rel rfl)
  · intro h
    induction h with
    | refl => exact connect_refl _
    | @tail u v hau huv ih =>
      obtain rfl : f u = v := huv
      exact connect_trans ih (connect_of_rel (key u hau))

omit [Fintype D] in
/-- If `c` is a fixed point of `f`, multiplying by `swap x c` keeps what `f` connects. -/
theorem fconnect_mul_swap_of_fconnect [Finite D] (f : Equiv.Perm D) {c : D} (hc : f c = c) (x : D)
    {a b : D} (h : fconnect f a b) : fconnect (f * Equiv.swap x c) a b := by
  refine connect_sub (fun u v huv => ?_) h
  obtain rfl : f u = v := huv
  by_cases huc : u = c
  · rw [huc, hc]
  by_cases hux : u = x
  · rw [hux]
    have hxc : x ≠ c := hux ▸ huc
    have h1 : (f * Equiv.swap x c) x = c := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hc]
    have h2 : (f * Equiv.swap x c) c = f x := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    exact connect_trans (connect_of_rel h1) (connect_of_rel h2)
  · exact connect_of_rel (show (f * Equiv.swap x c) u = f u by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hux huc])

omit [Fintype D] in
/-- If `c` is a fixed point of `f`, multiplying by `swap x c` connects no further points away
from `c`. -/
theorem fconnect_of_fconnect_mul_swap (f : Equiv.Perm D) {c : D} (hc : f c = c) {x a b : D}
    (ha : a ≠ c) (hb : b ≠ c) (h : fconnect (f * Equiv.swap x c) a b) : fconnect f a b := by
  have hne : ∀ z, z ≠ c → f z ≠ c := fun z hz e => hz (f.injective (e.trans hc.symm))
  have key : ∀ v, fconnect (f * Equiv.swap x c) a v →
      (v ≠ c ∧ fconnect f a v) ∨ (v = c ∧ fconnect f a x) := by
    intro v hv
    induction hv with
    | refl => exact Or.inl ⟨ha, connect_refl a⟩
    | @tail u v _ huv ih =>
      obtain rfl : (f * Equiv.swap x c) u = v := huv
      rcases ih with ⟨huc, hau⟩ | ⟨huc, hax⟩
      · by_cases hux : u = x
        · right
          exact ⟨by rw [hux, Equiv.Perm.mul_apply, Equiv.swap_apply_left, hc], hux ▸ hau⟩
        · left
          rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hux huc]
          exact ⟨hne u huc, connect_trans hau (connect_of_rel rfl)⟩
      · rw [huc, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        by_cases hxc : x = c
        · right
          exact ⟨by rw [hxc, hc], hax⟩
        · left
          exact ⟨hne x hxc, connect_trans hax (connect_of_rel rfl)⟩
  rcases key b h with ⟨-, hab⟩ | ⟨hbc, -⟩
  · exact hab
  · exact absurd hbc hb

/-! ### More on first returns -/

namespace Trail

variable {f g : Equiv.Perm D} {S W : Finset D} {y z : D}

omit [Fintype D] [DecidableEq D] in
/-- The first step of a trail from a point outside the set. -/
theorem of_not_mem (h : Trail f S y z) (hy : y ∉ S) : Trail f S (f y) z := by
  cases h with
  | here hm => exact absurd hm hy
  | step _ ht => exact ht

omit [Fintype D] [DecidableEq D] in
/-- A trail in a larger set that ends in the smaller set is a trail in the smaller set. -/
theorem mono (h : Trail f W y z) (hSW : S ⊆ W) (hz : z ∈ S) : Trail f S y z := by
  induction h with
  | here _ => exact Trail.here hz
  | step hn _ ih => exact Trail.step (fun hm => hn (hSW hm)) (ih hz)

omit [Fintype D] [DecidableEq D] in
/-- A trail read backwards. -/
theorem inv {w : D} (h : Trail f S y w) (hz : Trail f⁻¹ S (f⁻¹ y) z) : Trail f⁻¹ S (f⁻¹ w) z := by
  induction h with
  | here _ => exact hz
  | step hn _ ih =>
    refine ih ?_
    rw [perm_inv_apply_self]
    exact Trail.step hn hz

omit [Fintype D] [DecidableEq D] in
/-- A trail carries over to a permutation and a larger set that agree with it along the trail. -/
theorem transfer {A : Finset D} (h : Trail f A y z) (hAW : A ⊆ W) (P : D → Prop) (hy : P y)
    (hstep : ∀ u, P u → u ∉ A → Trail f A (f u) z → u ∉ W ∧ g u = f u ∧ P (f u)) :
    Trail g W y z := by
  induction h with
  | here hm => exact Trail.here (hAW hm)
  | @step u z hn ht ih =>
    obtain ⟨h1, h2, h3⟩ := hstep u hy hn ht
    exact Trail.step h1 (by rw [h2]; exact ih h3 hstep)

end Trail

/-- The inverse of a first return is the first return of the inverse. -/
theorem firstReturn_inv (f : Equiv.Perm D) (S : Finset D) :
    (firstReturn f S)⁻¹ = firstReturn f⁻¹ S := by
  refine inv_eq_of_mul_eq_one_left ?_
  ext z
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  by_cases hz : z ∈ S
  · refine firstReturn_eq_of_trail f⁻¹ ((firstReturn_mem_iff f S z).2 hz) ?_
    refine (firstReturn_trail f hz).inv ?_
    rw [perm_inv_apply_self]
    exact Trail.here hz
  · rw [firstReturn_of_not_mem f hz, firstReturn_of_not_mem f⁻¹ hz]

/-- Inserting `x` in the set of a first return puts `x` right after the point `p` with
`firstReturn f (insert x A) p = x`. -/
theorem firstReturn_insert_of_apply_eq (f : Equiv.Perm D) {A : Finset D} {x p : D} (hx : x ∉ A)
    (hp : firstReturn f (insert x A) p = x) :
    firstReturn f (insert x A) = firstReturn f A * Equiv.swap p x := by
  have hret := firstReturn_firstReturn f (Finset.subset_insert x A)
  have hne : ∀ z, z ≠ p → firstReturn f (insert x A) z ≠ x := fun z hz e =>
    hz ((firstReturn f (insert x A)).injective (e.trans hp.symm))
  have hA : ∀ z, z ∈ insert x A → z ≠ p → firstReturn f (insert x A) z ∈ A := fun z hz hzp =>
    (Finset.mem_insert.1 ((firstReturn_mem_iff f _ z).2 hz)).resolve_left (hne z hzp)
  ext z
  rw [Equiv.Perm.mul_apply]
  by_cases hzp : z = p
  · rw [hzp, Equiv.swap_apply_left, hp, firstReturn_of_not_mem f hx]
  by_cases hzx : z = x
  · rw [hzx, Equiv.swap_apply_right]
    have hxp : x ≠ p := hzx ▸ hzp
    have hpW : p ∈ insert x A := (firstReturn_mem_iff f _ p).1 (by
      rw [hp]
      exact Finset.mem_insert_self x A)
    have hpA : p ∈ A := (Finset.mem_insert.1 hpW).resolve_left (Ne.symm hxp)
    have ht := firstReturn_trail (firstReturn f (insert x A)) hpA
    rw [hp, hret] at ht
    exact ((ht.of_not_mem hx).unique (Trail.here (hA x (Finset.mem_insert_self x A) hxp))).symm
  rw [Equiv.swap_apply_of_ne_of_ne hzp hzx]
  by_cases hzA : z ∈ A
  · rw [← hret]
    exact (firstReturn_eq_of_trail _ hzA
      (Trail.here (hA z (Finset.mem_insert_of_mem hzA) hzp))).symm
  · have hzW : z ∉ insert x A := by simp [hzx, hzA]
    rw [firstReturn_of_not_mem f hzW, firstReturn_of_not_mem f hzA]

/-- Inserting a point in the set of a first return: it comes right after its predecessor. -/
theorem firstReturn_insert (f : Equiv.Perm D) {A : Finset D} {x : D} (hx : x ∉ A) :
    firstReturn f (insert x A) =
      firstReturn f A * Equiv.swap (firstReturn f⁻¹ (insert x A) x) x := by
  refine firstReturn_insert_of_apply_eq f hx ?_
  rw [← firstReturn_inv]
  exact perm_apply_inv_self _ x

/-- A fixed point of `f` makes no difference to a first return. -/
theorem firstReturn_insert_of_fixed (f : Equiv.Perm D) {A : Finset D} {c : D} (hc : f c = c)
    (hcA : c ∉ A) : firstReturn f (insert c A) = firstReturn f A := by
  have h := firstReturn_insert_of_apply_eq f (p := c) hcA
    (firstReturn_eq_of_trail f (Finset.mem_insert_self c A)
      (by rw [hc]; exact Trail.here (Finset.mem_insert_self c A)))
  rw [Equiv.swap_self] at h
  exact h.trans (mul_one _)

/-- A fixed point `x` of `g` put right after `p ∈ W` is skipped by the first return to `W`. -/
theorem firstReturn_mul_swap_of_fixed {g : Equiv.Perm D} {W : Finset D} {p x : D}
    (hg : FixesOff g W) (hx : x ∉ W) (hp : p ∈ W) : firstReturn (g * Equiv.swap p x) W = g := by
  ext z
  by_cases hz : z ∈ W
  · refine firstReturn_eq_of_trail _ hz ?_
    rw [Equiv.Perm.mul_apply]
    by_cases hzp : z = p
    · rw [hzp, Equiv.swap_apply_left, hg x hx]
      refine Trail.step hx ?_
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      exact Trail.here ((hg.mem_iff p).2 hp)
    · have hzx : z ≠ x := fun e => hx (e ▸ hz)
      rw [Equiv.swap_apply_of_ne_of_ne hzp hzx]
      exact Trail.here ((hg.mem_iff z).2 hz)
  · rw [firstReturn_of_not_mem _ hz, hg z hz]

omit [Fintype D] in
/-- Conjugating one transposition by another. -/
theorem swap_mul_swap_comm {p x c : D} (hpc : p ≠ c) (hxc : x ≠ c) :
    Equiv.swap p x * Equiv.swap x c = Equiv.swap p c * Equiv.swap p x := by
  have h := Equiv.swap_apply_apply (Equiv.swap p x) x c
  rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hpc.symm hxc.symm] at h
  rw [h, inv_mul_cancel_right]

/-! ### Merging two components -/

omit [DecidableEq D] in
/-- Joining two components of a relation, and nothing else, makes one component less. -/
theorem nComp_merge {e e' : D → D → Prop} (hs : ConnectSym e) (hs' : ConnectSym e') {a b : D}
    (hab : ¬ connect e a b) (hle : ∀ u v, connect e u v → connect e' u v)
    (hlink : connect e' a b) (hoff : ∀ u v, e' u v → u ∉ closure e {a, b} → e u v) :
    nComp e' Set.univ + 1 = nComp e Set.univ := by
  have hT : Closed e (closure e {a, b}) := closure_closed hs _
  have hT' : Closed e' (closure e {a, b})ᶜ := Closed.of_forward hs' fun u v huv hu =>
    (hT.compl u v (hoff u v huv hu)).1 hu
  have h1 : nComp e Set.univ = nComp e (closure e {a, b}) + nComp e (closure e {a, b})ᶜ :=
    nComp_compl hT
  have h2 : nComp e' Set.univ = nComp e' (closure e {a, b})ᶜ + nComp e' (closure e {a, b})ᶜᶜ :=
    nComp_compl hT'
  have h3 : nComp e (closure e {a, b}) = 2 := nComp_closure2_of_not_connect hs hab
  have h4 : nComp e' (closure e {a, b})ᶜᶜ = 1 := by
    rw [compl_compl]
    refine nComp_eq_one_of_connect hs' ⟨a, subset_closure _ (by simp)⟩ ?_
    have hto : ∀ u ∈ closure e {a, b}, connect e' u a := by
      rintro u ⟨w, hw, huw⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact hle _ _ huw
      · exact connect_trans (hle _ _ huw) (hs' _ _ hlink)
    exact fun u hu v hv => connect_trans (hto u hu) (hs' _ _ (hto v hv))
  have h5 : nComp e' (closure e {a, b})ᶜ = nComp e (closure e {a, b})ᶜ := by
    refine ncard_image_eq_of_ker _ _ fun u hu v _ => ?_
    rw [comp_eq_iff hs', comp_eq_iff hs]
    refine ⟨fun h => ?_, hle u v⟩
    have key : ∀ w, connect e' u w → w ∈ (closure e {a, b})ᶜ ∧ connect e u w := by
      intro w hw
      induction hw with
      | refl => exact ⟨hu, connect_refl u⟩
      | @tail w₁ w₂ _ hw₁ ih =>
        have hl := hoff w₁ w₂ hw₁ ih.1
        exact ⟨(hT.compl w₁ w₂ hl).1 ih.1, connect_trans ih.2 (connect_of_rel hl)⟩
    exact (key v h).2
  omega

end Swap

section Disjoint

variable {α β : Type*}

/-- Connection inside the left part of a disjoint union. -/
theorem connect_inl_iff {e : α ⊕ β → α ⊕ β → Prop} {e₁ : α → α → Prop}
    (h₁ : ∀ a b, e (Sum.inl a) (Sum.inl b) ↔ e₁ a b) (h₁₂ : ∀ a b, ¬ e (Sum.inl a) (Sum.inr b))
    (a b : α) : connect e (Sum.inl a) (Sum.inl b) ↔ connect e₁ a b :=
  (connect_iff_of_base Sum.inl_injective (a := Set.range Sum.inl)
    (by
      rintro _ y hxy ⟨u, rfl⟩
      cases y with
      | inl v => exact ⟨v, rfl⟩
      | inr v => exact absurd hxy (h₁₂ u v))
    subset_rfl (fun x y _ => h₁ x y) ⟨a, rfl⟩).symm

/-- Connection inside the right part of a disjoint union. -/
theorem connect_inr_iff {e : α ⊕ β → α ⊕ β → Prop} {e₂ : β → β → Prop}
    (h₂ : ∀ a b, e (Sum.inr a) (Sum.inr b) ↔ e₂ a b) (h₂₁ : ∀ a b, ¬ e (Sum.inr a) (Sum.inl b))
    (a b : β) : connect e (Sum.inr a) (Sum.inr b) ↔ connect e₂ a b :=
  (connect_iff_of_base Sum.inr_injective (a := Set.range Sum.inr)
    (by
      rintro _ y hxy ⟨u, rfl⟩
      cases y with
      | inl v => exact absurd hxy (h₂₁ u v)
      | inr v => exact ⟨v, rfl⟩)
    subset_rfl (fun x y _ => h₂ x y) ⟨a, rfl⟩).symm

/-- The components of a disjoint union are the components of the two parts. -/
theorem nComp_sum [Finite α] [Finite β] {e : α ⊕ β → α ⊕ β → Prop} {e₁ : α → α → Prop}
    {e₂ : β → β → Prop} (hs : ConnectSym e) (h₁ : ∀ a b, e (Sum.inl a) (Sum.inl b) ↔ e₁ a b)
    (h₂ : ∀ a b, e (Sum.inr a) (Sum.inr b) ↔ e₂ a b) (h₁₂ : ∀ a b, ¬ e (Sum.inl a) (Sum.inr b))
    (h₂₁ : ∀ a b, ¬ e (Sum.inr a) (Sum.inl b)) :
    nComp e Set.univ = nComp e₁ Set.univ + nComp e₂ Set.univ := by
  have hl := connect_inl_iff h₁ h₁₂
  have hr := connect_inr_iff h₂ h₂₁
  have hs₁ : ConnectSym e₁ := fun a b hab => (hl b a).1 (hs _ _ ((hl a b).2 hab))
  have hs₂ : ConnectSym e₂ := fun a b hab => (hr b a).1 (hs _ _ ((hr a b).2 hab))
  have hc : Closed e (Set.range Sum.inl) := Closed.of_forward hs (by
    rintro _ y hxy ⟨u, rfl⟩
    cases y with
    | inl v => exact ⟨v, rfl⟩
    | inr v => exact absurd hxy (h₁₂ u v))
  have h3 : nComp e (Set.range Sum.inl) = nComp e₁ Set.univ := by
    have h := nComp_adjunction hs hs₁ Sum.inl (a := Set.range Sum.inl) subset_rfl
      fun x y _ _ => (hl x y).symm
    rwa [Set.preimage_range] at h
  have h4 : nComp e (Set.range Sum.inr) = nComp e₂ Set.univ := by
    have h := nComp_adjunction hs hs₂ Sum.inr (a := Set.range Sum.inr) subset_rfl
      fun x y _ _ => (hr x y).symm
    rwa [Set.preimage_range] at h
  rw [nComp_compl hc, h3, Set.compl_range_inl, h4]

/-- The other dart of a free edge. -/
def flipPair {k : ℕ} (i : Fin k × Bool) : Fin k × Bool := (i.1, !i.2)

theorem flipPair_flipPair {k : ℕ} (i : Fin k × Bool) : flipPair (flipPair i) = i :=
  Prod.ext rfl (Bool.not_not i.2)

/-- A relation that joins exactly the two darts of each free edge has one component per edge. -/
theorem nComp_pairs {k : ℕ} {e : Fin k × Bool → Fin k × Bool → Prop} (hs : ConnectSym e)
    (hfl : ∀ i b, connect e (i, b) (i, !b)) (hfst : ∀ u v, e u v → u.1 = v.1) :
    nComp e Set.univ = k := by
  have h1 : nComp e Set.univ = (Prod.fst '' (Set.univ : Set (Fin k × Bool))).ncard := by
    refine ncard_image_eq_of_ker _ _ fun u _ v _ => ?_
    rw [comp_eq_iff hs]
    constructor
    · intro h
      have key : ∀ w, connect e u w → u.1 = w.1 := by
        intro w hw
        induction hw with
        | refl => rfl
        | tail _ hbc ih => exact ih.trans (hfst _ _ hbc)
      exact key v h
    · obtain ⟨i, b⟩ := u
      obtain ⟨j, b'⟩ := v
      rintro (rfl : i = j)
      by_cases hb : b' = b
      · rw [hb]
      · have hb' : b' = !b := by
          cases b <;> cases b' <;> simp_all
        rw [hb']
        exact hfl i b
  rw [h1, Set.image_univ_of_surjective Prod.fst_surjective, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem fcard_flipPair (k : ℕ) : fcard (flipPair (k := k)) Set.univ = k :=
  nComp_pairs (fconnect_sym (Function.LeftInverse.injective flipPair_flipPair))
    (fun _ _ => connect_of_rel rfl) (by rintro u _ rfl; rfl)

/-- The link of a free edge in its hypermap. -/
def pairLink {k : ℕ} (u v : Fin k × Bool) : Prop := flipPair u = v ∨ u = v

theorem nComp_pairLink (k : ℕ) : nComp (pairLink (k := k)) Set.univ = k :=
  nComp_pairs
    (connectSym_of_rev (by
      rintro x _ (rfl | rfl)
      · exact connect_of_rel (Or.inl (flipPair_flipPair x))
      · exact connect_refl _))
    (fun _ _ => connect_of_rel (Or.inl rfl))
    (by rintro u _ (rfl | rfl) <;> rfl)

end Disjoint

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] (R : RotSystem D)

/-! ### Attaching a dart -/

/-- Put the dart `c`, a fixed point of `rot`, into the corner `x`: the rotation `rot * swap x c`, so
`x ↦ c ↦ rot x`. -/
def attach (c x : D) : RotSystem D := R.glue (Equiv.swap x c)

theorem attach_rot (c x : D) : (R.attach c x).rot = R.rot * Equiv.swap x c := rfl

theorem attach_facePerm (c x : D) : (R.attach c x).facePerm = Equiv.swap x c * R.facePerm := by
  rw [attach, glue_facePerm, Equiv.swap_inv]

theorem numVertices_eq_orb : R.numVertices = orb R.rot := rfl

theorem numFaces_eq_orb : R.numFaces = orb R.facePerm := rfl

/-- Attaching a fixed point of the rotation merges two vertices. -/
theorem numVertices_attach {c x : D} (hc : R.rot c = c) (hxc : x ≠ c) :
    (R.attach c x).numVertices + 1 = R.numVertices :=
  orb_mul_swap_of_not_fconnect R.rot
    fun h => hxc (eq_of_fconnect_of_fixed hc (fconnect_sym R.rot.injective _ _ h))

theorem numFaces_attach_of_fconnect {c x : D} (hxc : x ≠ c) (h : fconnect R.facePerm x c) :
    (R.attach c x).numFaces = R.numFaces + 1 := by
  rw [numFaces_eq_orb, numFaces_eq_orb, attach_facePerm]
  exact orb_swap_mul_of_fconnect _ hxc h

theorem numFaces_attach_of_not_fconnect {c x : D} (h : ¬ fconnect R.facePerm x c) :
    (R.attach c x).numFaces + 1 = R.numFaces := by
  rw [numFaces_eq_orb, numFaces_eq_orb, attach_facePerm]
  exact orb_swap_mul_of_not_fconnect _ h

theorem gcomp_attach_self {c : D} (x : D) (hc : R.rot c = c) :
    (R.attach c x).toHypermap.gcomp x c :=
  connect_of_rel (Or.inr (Or.inl (show R.rot (Equiv.swap x c x) = c by
    rw [Equiv.swap_apply_left, hc])))

/-- Attaching keeps what was connected. -/
theorem gcomp_attach_of_gcomp {c : D} (x : D) (hc : R.rot c = c) {a b : D}
    (h : R.toHypermap.gcomp a b) : (R.attach c x).toHypermap.gcomp a b := by
  refine R.mem_of_gcomp (A := {z | (R.attach c x).toHypermap.gcomp a z}) ?_ ?_ h (connect_refl a)
  · exact fun z hz => connect_trans hz (connect_of_rel (Or.inl rfl))
  · exact fun z hz => connect_trans hz ((R.attach c x).toHypermap.gcomp_of_cnode
      (fconnect_mul_swap_of_fconnect R.rot hc x (fconnect1 _ z)))

/-- Attaching inside one component connects nothing new. -/
theorem gcomp_of_gcomp_attach {c x a b : D} (hg : R.toHypermap.gcomp x c)
    (h : (R.attach c x).toHypermap.gcomp a b) : R.toHypermap.gcomp a b := by
  refine (R.attach c x).mem_of_gcomp (A := {z | R.toHypermap.gcomp a z}) ?_ ?_ h (connect_refl a)
  · exact fun z hz => connect_trans hz (connect_of_rel (Or.inl rfl))
  · intro z hz
    have h1 : R.toHypermap.gcomp z (Equiv.swap x c z) := by
      by_cases hzx : z = x
      · rw [hzx, Equiv.swap_apply_left]
        exact hg
      by_cases hzc : z = c
      · rw [hzc, Equiv.swap_apply_right]
        exact R.toHypermap.glinkC _ _ hg
      · rw [Equiv.swap_apply_of_ne_of_ne hzx hzc]
    show R.toHypermap.gcomp a (R.rot (Equiv.swap x c z))
    exact connect_trans hz (connect_trans h1 (connect_of_rel (Or.inr (Or.inl rfl))))

theorem numComponents_attach_of_gcomp {c x : D} (hc : R.rot c = c) (hg : R.toHypermap.gcomp x c) :
    (R.attach c x).numComponents = R.numComponents :=
  nComp_congr (fun _ _ => ⟨R.gcomp_of_gcomp_attach hg, R.gcomp_attach_of_gcomp x hc⟩) _

/-- Attaching between two components merges them. -/
theorem numComponents_attach_of_not_gcomp {c x : D} (hc : R.rot c = c)
    (hg : ¬ R.toHypermap.gcomp x c) : (R.attach c x).numComponents + 1 = R.numComponents := by
  refine nComp_merge R.toHypermap.glinkC (R.attach c x).toHypermap.glinkC hg
    (fun _ _ h => R.gcomp_attach_of_gcomp x hc h) (R.gcomp_attach_self x hc) ?_
  intro u v huv hu
  have hne : ∀ w, R.toHypermap.gcomp u w → w ≠ x ∧ w ≠ c := fun w hw =>
    ⟨fun e => hu ⟨x, by simp, e ▸ hw⟩, fun e => hu ⟨c, by simp, e ▸ hw⟩⟩
  rcases huv with rfl | rfl | rfl
  · exact Or.inl rfl
  · refine Or.inr (Or.inl ?_)
    show R.rot u = R.rot (Equiv.swap x c u)
    have h0 := hne u (connect_refl u)
    rw [Equiv.swap_apply_of_ne_of_ne h0.1 h0.2]
  · refine Or.inr (Or.inr ?_)
    show R.facePerm u = (R.attach c x).facePerm u
    have h0 := hne (R.facePerm u) (R.toHypermap.gcomp_of_cface (fconnect1 _ u))
    rw [attach_facePerm, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h0.1 h0.2]

theorem genus_attach_of_fconnect {c x : D} (hc : R.rot c = c) (hxc : x ≠ c)
    (h : fconnect R.facePerm x c) :
    (R.attach c x).toHypermap.genus = R.toHypermap.genus := by
  have h1 := R.genus_formula
  have h2 := (R.attach c x).genus_formula
  have hV := R.numVertices_attach hc hxc
  have hF := R.numFaces_attach_of_fconnect hxc h
  have hE : (R.attach c x).numEdges = R.numEdges := rfl
  have hC := R.numComponents_attach_of_gcomp hc (R.toHypermap.gcomp_of_cface h)
  omega

theorem genus_attach_of_gcomp {c x : D} (hc : R.rot c = c) (h : ¬ fconnect R.facePerm x c)
    (hg : R.toHypermap.gcomp x c) :
    (R.attach c x).toHypermap.genus = R.toHypermap.genus + 1 := by
  have hxc : x ≠ c := fun e => h (e ▸ connect_refl x)
  have h1 := R.genus_formula
  have h2 := (R.attach c x).genus_formula
  have hV := R.numVertices_attach hc hxc
  have hF := R.numFaces_attach_of_not_fconnect h
  have hE : (R.attach c x).numEdges = R.numEdges := rfl
  have hC := R.numComponents_attach_of_gcomp hc hg
  omega

theorem genus_attach_of_not_gcomp {c x : D} (hc : R.rot c = c) (hg : ¬ R.toHypermap.gcomp x c) :
    (R.attach c x).toHypermap.genus = R.toHypermap.genus := by
  have hxc : x ≠ c := fun e => hg (e ▸ connect_refl x)
  have hf : ¬ fconnect R.facePerm x c := fun h => hg (R.toHypermap.gcomp_of_cface h)
  have h1 := R.genus_formula
  have h2 := (R.attach c x).genus_formula
  have hV := R.numVertices_attach hc hxc
  have hF := R.numFaces_attach_of_not_fconnect hf
  have hE : (R.attach c x).numEdges = R.numEdges := rfl
  have hC := R.numComponents_attach_of_not_gcomp hc hg
  omega

/-- Attaching a dart never lowers the genus. -/
theorem genus_le_attach {c : D} (x : D) (hc : R.rot c = c) :
    R.toHypermap.genus ≤ (R.attach c x).toHypermap.genus := by
  by_cases hg : R.toHypermap.gcomp x c
  · by_cases hf : fconnect R.facePerm x c
    · by_cases hxc : x = c
      · have h : R.attach c x = R := by
          refine RotSystem.ext rfl ?_
          rw [attach_rot, hxc, Equiv.swap_self]
          exact mul_one _
        rw [h]
      · exact (R.genus_attach_of_fconnect hc hxc hf).ge
    · rw [R.genus_attach_of_gcomp hc hf hg]
      exact Nat.le_succ _
  · exact (R.genus_attach_of_not_gcomp hc hg).ge

/-! ### Isolated edges and chords -/

/-- An edge whose two darts are fixed points of the rotation. -/
structure IsolatedEdge (c : D) : Prop where
  rot_self : R.rot c = c
  rot_rev : R.rot (R.rev c) = R.rev c

/-- The dart `x` is neither dart of the edge `c`. -/
def Off (c x : D) : Prop := x ≠ c ∧ x ≠ R.rev c

/-- The chord `c` from the corner `x` to the corner `y`: the rotation
`rot * swap x c * swap y (rev c)`. For `x ≠ y` this is `x ↦ c ↦ rot x` and
`y ↦ rev c ↦ rot y`. For `x = y` this is `x ↦ rev c ↦ c ↦ rot x`. -/
def chord (c x y : D) : RotSystem D := (R.attach c x).attach (R.rev c) y

variable {R} {c x y : D}

theorem chord_rot (c x y : D) :
    (R.chord c x y).rot = R.rot * Equiv.swap x c * Equiv.swap y (R.rev c) := rfl

theorem chord_rev (c x y : D) : (R.chord c x y).rev = R.rev := rfl

theorem chord_facePerm (c x y : D) :
    (R.chord c x y).facePerm = Equiv.swap y (R.rev c) * Equiv.swap x c * R.facePerm := by
  rw [chord, attach_facePerm, attach_facePerm, mul_assoc]

set_option linter.unusedVariables false in
theorem chord_rot_left (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y) (hxy : x ≠ y) :
    (R.chord c x y).rot x = c := by
  rw [chord_rot, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hxy hx.2, Equiv.swap_apply_left, hc.rot_self]

set_option linter.unusedVariables false in
theorem chord_rot_c (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y) :
    (R.chord c x y).rot c = R.rot x := by
  rw [chord_rot, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hy.1.symm (R.rev_ne c).symm, Equiv.swap_apply_right]

set_option linter.unusedVariables false in
theorem chord_rot_right (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y) :
    (R.chord c x y).rot y = R.rev c := by
  rw [chord_rot, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne hx.2.symm (R.rev_ne c), hc.rot_rev]

set_option linter.unusedVariables false in
theorem chord_rot_rev (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y) (hxy : x ≠ y) :
    (R.chord c x y).rot (R.rev c) = R.rot y := by
  rw [chord_rot, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne hxy.symm hy.1]

theorem chord_rot_of_ne {z : D} (hzx : z ≠ x) (hzy : z ≠ y) (hzc : z ≠ c) (hzr : z ≠ R.rev c) :
    (R.chord c x y).rot z = R.rot z := by
  rw [chord_rot, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hzy hzr, Equiv.swap_apply_of_ne_of_ne hzx hzc]

/-! ### Darts off an isolated edge -/

theorem rev_injective : Function.Injective R.rev := Function.LeftInverse.injective R.rev_rev

theorem IsolatedEdge.face_self (hc : R.IsolatedEdge c) : R.facePerm c = R.rev c :=
  R.rot.symm_apply_eq.2 hc.rot_rev.symm

theorem IsolatedEdge.face_rev (hc : R.IsolatedEdge c) : R.facePerm (R.rev c) = c := by
  rw [facePerm_apply, toHypermap_face, R.rev_rev]
  exact R.rot.symm_apply_eq.2 hc.rot_self.symm

theorem IsolatedEdge.eq_of_gcomp (hc : R.IsolatedEdge c) {z : D} (h : R.toHypermap.gcomp c z) :
    z = c ∨ z = R.rev c := by
  refine R.mem_of_gcomp (A := {w | w = c ∨ w = R.rev c}) ?_ ?_ h (Or.inl rfl)
  · rintro w (hw | hw)
    · exact Or.inr (congrArg R.rev hw)
    · exact Or.inl ((congrArg R.rev hw).trans (R.rev_rev c))
  · rintro w (hw | hw)
    · exact Or.inl (by rw [hw, hc.rot_self])
    · exact Or.inr (by rw [hw, hc.rot_rev])

theorem IsolatedEdge.not_gcomp (hc : R.IsolatedEdge c) (hx : R.Off c x) :
    ¬ R.toHypermap.gcomp x c := fun h =>
  (hc.eq_of_gcomp (R.toHypermap.glinkC _ _ h)).elim hx.1 hx.2

theorem Off.rev {z : D} (hz : R.Off c z) : R.Off c (R.rev z) :=
  ⟨fun e => hz.2 (by rw [← e, R.rev_rev]), fun e => hz.1 (R.rev_injective e)⟩

theorem Off.rot {z : D} (hc : R.IsolatedEdge c) (hz : R.Off c z) : R.Off c (R.rot z) :=
  ⟨fun e => hz.1 (R.rot.injective (e.trans hc.rot_self.symm)),
    fun e => hz.2 (R.rot.injective (e.trans hc.rot_rev.symm))⟩

theorem Off.rot_inv {z : D} (hc : R.IsolatedEdge c) (hz : R.Off c z) : R.Off c (R.rot⁻¹ z) :=
  ⟨fun e => hz.1 (Equiv.Perm.inv_eq_iff_eq.1 e |>.trans hc.rot_self),
    fun e => hz.2 (Equiv.Perm.inv_eq_iff_eq.1 e |>.trans hc.rot_rev)⟩

theorem Off.face {z : D} (hc : R.IsolatedEdge c) (hz : R.Off c z) : R.Off c (R.facePerm z) :=
  hz.rev.rot_inv hc

theorem Off.of_fconnect_face {a b : D} (hc : R.IsolatedEdge c) (ha : R.Off c a)
    (h : fconnect R.facePerm a b) : R.Off c b := by
  induction h with
  | refl => exact ha
  | @tail u v _ huv ih =>
    obtain rfl : R.facePerm u = v := huv
    exact ih.face hc

theorem Off.iterate_face {z : D} (hc : R.IsolatedEdge c) (hz : R.Off c z) (n : ℕ) :
    R.Off c ((⇑R.facePerm)^[n] z) :=
  hz.of_fconnect_face hc (fconnect_iterate _ z n)

/-! ### The genus of a chord -/

theorem attach_rot_rev (hc : R.IsolatedEdge c) (hx : R.Off c x) :
    (R.attach c x).rot (R.rev c) = R.rev c := by
  rw [attach_rot, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hx.2.symm (R.rev_ne c),
    hc.rot_rev]

/-- The first attach merges the face of `x` with the face of the edge `c`. -/
theorem fconnect_attach_rev (hc : R.IsolatedEdge c) (hx : R.Off c x) :
    fconnect (R.attach c x).facePerm x (R.rev c) := by
  have h1 : ¬ fconnect R.facePerm x c := fun h =>
    hc.not_gcomp hx (R.toHypermap.gcomp_of_cface h)
  have h2 : fconnect (R.attach c x).facePerm x c := by
    rw [attach_facePerm]
    exact fconnect_swap_mul_of_not _ h1
  have h3 : (R.attach c x).facePerm c = R.rev c := by
    rw [attach_facePerm, Equiv.Perm.mul_apply, hc.face_self,
      Equiv.swap_apply_of_ne_of_ne hx.2.symm (R.rev_ne c)]
  exact connect_trans h2 (connect_of_rel h3)

/-- After the first attach, `y` lies in the face of `rev c` if it lay in the face of `x`. -/
theorem fconnect_attach_of_fconnect (hc : R.IsolatedEdge c) (hx : R.Off c x)
    (h : fconnect R.facePerm x y) : fconnect (R.attach c x).facePerm y (R.rev c) := by
  have h1 : ¬ fconnect R.facePerm x c := fun h =>
    hc.not_gcomp hx (R.toHypermap.gcomp_of_cface h)
  have h2 : fconnect (R.attach c x).facePerm y x := by
    rw [attach_facePerm]
    exact fconnect_swap_mul_of_fconnect _ h1 (fconnect_sym R.facePerm.injective _ _ h)
  exact connect_trans h2 (fconnect_attach_rev hc hx)

/-- After the first attach, `y` does not lie in the face of `rev c` if it lay in another face than
`x`. -/
theorem not_fconnect_attach_of_not_fconnect (hc : R.IsolatedEdge c) (hx : R.Off c x)
    (hy : R.Off c y) (h : ¬ fconnect R.facePerm x y) :
    ¬ fconnect (R.attach c x).facePerm y (R.rev c) := by
  intro h1
  have h2 : fconnect (R.attach c x).facePerm y x :=
    connect_trans h1
      (fconnect_sym (R.attach c x).facePerm.injective _ _ (fconnect_attach_rev hc hx))
  rw [attach_facePerm] at h2
  have h3 : ¬ fconnect R.facePerm y x := fun e => h (fconnect_sym R.facePerm.injective _ _ e)
  have h4 : ¬ fconnect R.facePerm y c := fun e => (hy.of_fconnect_face hc e).1 rfl
  exact h3 ((fconnect_swap_mul_iff _ h3 h4).1 h2)

/-- A chord between two corners of one face keeps the genus. -/
theorem genus_chord_of_fconnect (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y)
    (h : fconnect R.facePerm x y) :
    (R.chord c x y).toHypermap.genus = R.toHypermap.genus :=
  ((R.attach c x).genus_attach_of_fconnect (attach_rot_rev hc hx) hy.2
    (fconnect_attach_of_fconnect hc hx h)).trans
    (R.genus_attach_of_not_gcomp hc.rot_self (hc.not_gcomp hx))

/-- A chord between two faces of one component raises the genus by one. -/
theorem genus_chord_of_not_fconnect (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y)
    (h : ¬ fconnect R.facePerm x y) (hg : R.toHypermap.gcomp x y) :
    (R.chord c x y).toHypermap.genus = R.toHypermap.genus + 1 := by
  have h1 := R.genus_attach_of_not_gcomp hc.rot_self (hc.not_gcomp hx)
  have h2 : (R.attach c x).toHypermap.gcomp y (R.rev c) := by
    refine connect_trans (R.gcomp_attach_of_gcomp x hc.rot_self (R.toHypermap.glinkC _ _ hg)) ?_
    exact connect_trans (R.gcomp_attach_self x hc.rot_self) (connect_of_rel (Or.inl rfl))
  have h3 := (R.attach c x).genus_attach_of_gcomp (attach_rot_rev hc hx)
    (not_fconnect_attach_of_not_fconnect hc hx hy h) h2
  exact h3.trans (by rw [h1])

theorem planar_chord (hR : R.Planar) (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y)
    (h : fconnect R.facePerm x y) : (R.chord c x y).Planar :=
  (genus_chord_of_fconnect hc hx hy h).trans hR

/-- A further isolated edge stays isolated. -/
theorem IsolatedEdge.chord {c' : D} (hc' : R.IsolatedEdge c') (hx : R.Off c' x) (hy : R.Off c' y)
    (hcc : R.Off c' c) : (R.chord c x y).IsolatedEdge c' := by
  have h1 : c' ≠ R.rev c := fun e => hcc.2 (by rw [e, R.rev_rev])
  have h2 : R.rev c' ≠ R.rev c := fun e => hcc.1 (R.rev_injective e).symm
  constructor
  · rw [chord_rot, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hy.1.symm h1, Equiv.swap_apply_of_ne_of_ne hx.1.symm hcc.1.symm,
      hc'.rot_self]
  · show (R.chord c x y).rot (R.rev c') = R.rev c'
    rw [chord_rot, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hy.2.symm h2, Equiv.swap_apply_of_ne_of_ne hx.2.symm hcc.2.symm,
      hc'.rot_rev]

/-! ### The faces of a chord -/

theorem chord_face_c (hc : R.IsolatedEdge c) (hx : R.Off c x) :
    (R.chord c x y).facePerm c = y := by
  rw [chord_facePerm, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hc.face_self,
    Equiv.swap_apply_of_ne_of_ne hx.2.symm (R.rev_ne c), Equiv.swap_apply_right]

theorem chord_face_rev (hc : R.IsolatedEdge c) (hx : R.Off c x) (hxy : x ≠ y) :
    (R.chord c x y).facePerm (R.rev c) = x := by
  rw [chord_facePerm, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hc.face_rev,
    Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hxy hx.2]

theorem chord_face_rev_of_eq (hc : R.IsolatedEdge c) (hxy : x = y) :
    (R.chord c x y).facePerm (R.rev c) = R.rev c := by
  rw [chord_facePerm, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hc.face_rev,
    Equiv.swap_apply_right, hxy, Equiv.swap_apply_left]

theorem chord_face_of_ne {z : D} (h1 : R.facePerm z ≠ x) (h2 : R.facePerm z ≠ y)
    (h3 : R.facePerm z ≠ c) (h4 : R.facePerm z ≠ R.rev c) :
    (R.chord c x y).facePerm z = R.facePerm z := by
  rw [chord_facePerm, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne h1 h3, Equiv.swap_apply_of_ne_of_ne h2 h4]

theorem chord_face_of_face_eq_left (hy : R.Off c y) {z : D} (h : R.facePerm z = x) :
    (R.chord c x y).facePerm z = c := by
  rw [chord_facePerm, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne hy.1.symm (R.rev_ne c).symm]

theorem chord_face_of_face_eq_right (hy : R.Off c y) (hyx : y ≠ x) {z : D}
    (h : R.facePerm z = y) : (R.chord c x y).facePerm z = R.rev c := by
  rw [chord_facePerm, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h,
    Equiv.swap_apply_of_ne_of_ne hyx hy.1, Equiv.swap_apply_left]

/-- A chord in one face splits it: its two darts lie in different orbits. -/
theorem not_fconnect_chord (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y)
    (h : fconnect R.facePerm x y) : ¬ fconnect (R.chord c x y).facePerm c (R.rev c) := by
  intro hcr
  have h3 : ¬ fconnect (R.chord c x y).facePerm y (R.rev c) := by
    rw [chord, attach_facePerm]
    exact not_fconnect_swap_mul _ hy.2 (fconnect_attach_of_fconnect hc hx h)
  have hcy : fconnect (R.chord c x y).facePerm c y := connect_of_rel (chord_face_c hc hx)
  exact h3 (connect_trans (fconnect_sym (R.chord c x y).facePerm.injective _ _ hcy) hcr)

set_option linter.unusedVariables false in
theorem fconnect_chord_rev_left (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y)
    (hxy : x ≠ y) : fconnect (R.chord c x y).facePerm (R.rev c) x :=
  connect_of_rel (chord_face_rev hc hx hxy)

set_option linter.unusedVariables false in
theorem fconnect_chord_c_right (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y) :
    fconnect (R.chord c x y).facePerm c y :=
  connect_of_rel (chord_face_c hc hx)

/-- Along a part of a face without the two corners, the chord changes nothing. -/
theorem fconnect_chord_iterate (hc : R.IsolatedEdge c) {s : D} (hs : R.Off c s) (n : ℕ)
    (h : ∀ j, 0 < j → j ≤ n → (⇑R.facePerm)^[j] s ≠ x ∧ (⇑R.facePerm)^[j] s ≠ y) :
    fconnect (R.chord c x y).facePerm s ((⇑R.facePerm)^[n] s) := by
  induction n with
  | zero => exact connect_refl s
  | succ n ih =>
    have ih' := ih fun j h0 hj => h j h0 (Nat.le_succ_of_le hj)
    have hn := h (n + 1) (Nat.succ_pos n) le_rfl
    have hoff : R.Off c ((⇑R.facePerm)^[n + 1] s) := hs.iterate_face hc (n + 1)
    rw [Function.iterate_succ_apply'] at hn hoff ⊢
    exact connect_trans ih' (connect_of_rel (chord_face_of_ne hn.1 hn.2 hoff.1 hoff.2))

set_option linter.unusedVariables false in
/-- The part of the face from `x` up to `y` stays with `x`. -/
theorem fconnect_chord_left (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y) (n : ℕ)
    (h : ∀ j, 0 < j → j ≤ n → (⇑R.facePerm)^[j] x ≠ x ∧ (⇑R.facePerm)^[j] x ≠ y) :
    fconnect (R.chord c x y).facePerm x ((⇑R.facePerm)^[n] x) :=
  fconnect_chord_iterate hc hx n h

set_option linter.unusedVariables false in
/-- The part of the face from `y` up to `x` stays with `y`. -/
theorem fconnect_chord_right (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y) (n : ℕ)
    (h : ∀ j, 0 < j → j ≤ n → (⇑R.facePerm)^[j] y ≠ x ∧ (⇑R.facePerm)^[j] y ≠ y) :
    fconnect (R.chord c x y).facePerm y ((⇑R.facePerm)^[n] y) :=
  fconnect_chord_iterate hc hy n h

set_option linter.unusedVariables false in
/-- Every dart of the split face lies with `x` or with `y`. -/
theorem fconnect_chord_cases (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y)
    (h : fconnect R.facePerm x y) {z : D} (hz : fconnect R.facePerm x z) :
    fconnect (R.chord c x y).facePerm x z ∨ fconnect (R.chord c x y).facePerm y z := by
  have key : R.Off c z ∧
      (fconnect (R.chord c x y).facePerm x z ∨ fconnect (R.chord c x y).facePerm y z) := by
    induction hz with
    | refl => exact ⟨hx, Or.inl (connect_refl _)⟩
    | @tail u v _ huv ih =>
      obtain rfl : R.facePerm u = v := huv
      obtain ⟨hu, hP⟩ := ih
      have hfu := hu.face hc
      refine ⟨hfu, ?_⟩
      by_cases h1 : R.facePerm u = x
      · rw [h1]
        exact Or.inl (connect_refl _)
      by_cases h2 : R.facePerm u = y
      · rw [h2]
        exact Or.inr (connect_refl _)
      have hstep := chord_face_of_ne h1 h2 hfu.1 hfu.2
      rcases hP with hP | hP
      · exact Or.inl (connect_trans hP (connect_of_rel hstep))
      · exact Or.inr (connect_trans hP (connect_of_rel hstep))
  exact key.2

/-- A face of the chord map off the chord lies in one face of the map, if the chord is in one
face. -/
theorem fconnect_of_fconnect_chord (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y)
    (h : fconnect R.facePerm x y) {a b : D} (ha : R.Off c a) (hb : R.Off c b)
    (hab : fconnect (R.chord c x y).facePerm a b) : fconnect R.facePerm a b := by
  have key : ∀ v, fconnect (R.chord c x y).facePerm a v →
      (R.Off c v ∧ fconnect R.facePerm a v) ∨
        ((v = c ∨ v = R.rev c) ∧ fconnect R.facePerm a x) := by
    intro v hv
    induction hv with
    | refl => exact Or.inl ⟨ha, connect_refl a⟩
    | @tail u v _ huv ih =>
      obtain rfl : (R.chord c x y).facePerm u = v := huv
      rcases ih with ⟨hu, hau⟩ | ⟨hu | hu, hax⟩
      · have hfu := hu.face hc
        by_cases h1 : R.facePerm u = x
        · exact Or.inr ⟨Or.inl (chord_face_of_face_eq_left hy h1),
            connect_trans hau (connect_of_rel h1)⟩
        by_cases h2 : R.facePerm u = y
        · have hyx : y ≠ x := fun e => h1 (h2.trans e)
          exact Or.inr ⟨Or.inr (chord_face_of_face_eq_right hy hyx h2),
            connect_trans (connect_trans hau (connect_of_rel h2))
              (fconnect_sym R.facePerm.injective _ _ h)⟩
        · rw [chord_face_of_ne h1 h2 hfu.1 hfu.2]
          exact Or.inl ⟨hfu, connect_trans hau (fconnect1 _ u)⟩
      · rw [hu, chord_face_c hc hx]
        exact Or.inl ⟨hy, connect_trans hax h⟩
      · rw [hu]
        by_cases hxy : x = y
        · exact Or.inr ⟨Or.inr (chord_face_rev_of_eq hc hxy), hax⟩
        · rw [chord_face_rev hc hx hxy]
          exact Or.inl ⟨hx, hax⟩
  rcases key b hab with ⟨-, h1⟩ | ⟨h1 | h1, -⟩
  · exact h1
  · exact absurd h1 hb.1
  · exact absurd h1 hb.2

set_option linter.unusedVariables false in
/-- A face without the two corners does not change. -/
theorem fconnect_chord_iff_of_not_fconnect (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y)
    {a b : D} (hax : ¬ fconnect R.facePerm a x) (hay : ¬ fconnect R.facePerm a y) (ha : R.Off c a) :
    fconnect (R.chord c x y).facePerm a b ↔ fconnect R.facePerm a b := by
  have key : ∀ u, fconnect R.facePerm a u → (R.chord c x y).facePerm u = R.facePerm u := by
    intro u hu
    have hfu : fconnect R.facePerm a (R.facePerm u) := connect_trans hu (fconnect1 _ u)
    have hoff := ha.of_fconnect_face hc hfu
    exact chord_face_of_ne (fun e => hax (e ▸ hfu)) (fun e => hay (e ▸ hfu)) hoff.1 hoff.2
  constructor
  · intro h
    induction h with
    | refl => exact connect_refl _
    | @tail u v _ huv ih =>
      obtain rfl : (R.chord c x y).facePerm u = v := huv
      rw [key u ih]
      exact connect_trans ih (fconnect1 _ u)
  · intro h
    induction h with
    | refl => exact connect_refl _
    | @tail u v hau huv ih =>
      obtain rfl : R.facePerm u = v := huv
      exact connect_trans ih (connect_of_rel (key u hau))

theorem chord_rot_rev_of_eq (hc : R.IsolatedEdge c) (hxy : x = y) :
    (R.chord c x y).rot (R.rev c) = c := by
  rw [chord_rot, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_right, ← hxy,
    Equiv.swap_apply_left, hc.rot_self]

/-- Components: the chord map keeps the components off the chord, if its corners lie in one
component. -/
theorem gcomp_chord_iff (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y)
    (hg : R.toHypermap.gcomp x y) {a b : D} (ha : R.Off c a) (hb : R.Off c b) :
    (R.chord c x y).toHypermap.gcomp a b ↔ R.toHypermap.gcomp a b := by
  have hrot : ∀ u, R.toHypermap.gcomp u (R.rot u) := fun u =>
    connect_of_rel (Or.inr (Or.inl rfl))
  constructor
  · intro h
    have key : (R.Off c b ∧ R.toHypermap.gcomp a b) ∨
        ((b = c ∨ b = R.rev c) ∧ R.toHypermap.gcomp a x) := by
      refine (R.chord c x y).mem_of_gcomp (A := {v | (R.Off c v ∧ R.toHypermap.gcomp a v) ∨
        ((v = c ∨ v = R.rev c) ∧ R.toHypermap.gcomp a x)}) ?_ ?_ h (Or.inl ⟨ha, connect_refl a⟩)
      · rintro v (⟨hv, hav⟩ | ⟨hv | hv, hax⟩)
        · exact Or.inl ⟨hv.rev, connect_trans hav (connect_of_rel (Or.inl rfl))⟩
        · exact Or.inr ⟨Or.inr (congrArg R.rev hv), hax⟩
        · exact Or.inr ⟨Or.inl ((congrArg R.rev hv).trans (R.rev_rev c)), hax⟩
      · rintro v (⟨hv, hav⟩ | ⟨hv | hv, hax⟩)
        · by_cases hvx : v = x
          · have hax : R.toHypermap.gcomp a x := hvx ▸ hav
            by_cases hxy : x = y
            · refine Or.inr ⟨Or.inr ?_, hax⟩
              rw [hvx, hxy]
              exact chord_rot_right hc (hxy ▸ hx) hy
            · refine Or.inr ⟨Or.inl ?_, hax⟩
              rw [hvx]
              exact chord_rot_left hc hx hy hxy
          · by_cases hvy : v = y
            · have hay : R.toHypermap.gcomp a y := hvy ▸ hav
              refine Or.inr ⟨Or.inr ?_, connect_trans hay (R.toHypermap.glinkC _ _ hg)⟩
              rw [hvy]
              exact chord_rot_right hc hx hy
            · rw [chord_rot_of_ne hvx hvy hv.1 hv.2]
              exact Or.inl ⟨hv.rot hc, connect_trans hav (hrot v)⟩
        · rw [hv, chord_rot_c hc hx hy]
          exact Or.inl ⟨hx.rot hc, connect_trans hax (hrot x)⟩
        · rw [hv]
          by_cases hxy : x = y
          · rw [chord_rot_rev_of_eq hc hxy]
            exact Or.inr ⟨Or.inl rfl, hax⟩
          · rw [chord_rot_rev hc hx hy hxy]
            exact Or.inl ⟨hy.rot hc, connect_trans (connect_trans hax hg) (hrot y)⟩
    rcases key with ⟨-, h1⟩ | ⟨h1 | h1, -⟩
    · exact h1
    · exact absurd h1 hb.1
    · exact absurd h1 hb.2
  · intro h
    exact (R.attach c x).gcomp_attach_of_gcomp y (attach_rot_rev hc hx)
      (R.gcomp_attach_of_gcomp x hc.rot_self h)

set_option linter.unusedVariables false in
/-- Vertices: the chord map keeps the vertices off the chord. -/
theorem tail_chord_iff (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y) {a b : D}
    (ha : R.Off c a) (hb : R.Off c b) :
    (R.chord c x y).tail a = (R.chord c x y).tail b ↔ R.tail a = R.tail b := by
  rw [tail_eq_iff, tail_eq_iff]
  constructor
  · intro h
    exact fconnect_of_fconnect_mul_swap R.rot hc.rot_self ha.1 hb.1
      (fconnect_of_fconnect_mul_swap (R.rot * Equiv.swap x c) (attach_rot_rev hc hx) ha.2 hb.2 h)
  · intro h
    exact fconnect_mul_swap_of_fconnect _ (attach_rot_rev hc hx) y
      (fconnect_mul_swap_of_fconnect R.rot hc.rot_self x h)

set_option linter.unusedVariables false in
theorem tail_chord_c (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y) :
    (R.chord c x y).tail c = (R.chord c x y).tail x := by
  rw [tail_eq_iff]
  have h1 : fconnect (R.rot * Equiv.swap x c) x c := connect_of_rel
    (show (R.rot * Equiv.swap x c) x = c by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hc.rot_self])
  exact (R.chord c x y).toHypermap.cnodeC.1
    (fconnect_mul_swap_of_fconnect _ (attach_rot_rev hc hx) y h1)

theorem tail_chord_rev (hc : R.IsolatedEdge c) (hx : R.Off c x) (hy : R.Off c y) :
    (R.chord c x y).tail (R.rev c) = (R.chord c x y).tail y := by
  rw [tail_eq_iff]
  exact (R.chord c x y).toHypermap.cnodeC.1 (connect_of_rel (chord_rot_right hc hx hy))

variable (R)

/-! ### Restriction -/

/-- The restriction to `A`: the same reversal, and the rotation `firstReturn rot A`. Every dart off
`A` is a fixed point of the rotation. -/
noncomputable def restrict (A : Finset D) : RotSystem D where
  rev := R.rev
  rev_rev := R.rev_rev
  rev_ne := R.rev_ne
  rot := firstReturn R.rot A

/-- Any two darts of `A` lie in one component. -/
def ConnOn (A : Finset D) : Prop := ∀ x ∈ A, ∀ y ∈ A, R.toHypermap.gcomp x y

/-- `A` holds the reverse of each of its darts. -/
def RevClosed (A : Finset D) : Prop := ∀ x ∈ A, R.rev x ∈ A

variable {R}

theorem restrict_rot (A : Finset D) : (R.restrict A).rot = firstReturn R.rot A := rfl

theorem restrict_rev (A : Finset D) : (R.restrict A).rev = R.rev := rfl

theorem restrict_rot_of_not_mem {A : Finset D} {z : D} (hz : z ∉ A) : (R.restrict A).rot z = z :=
  firstReturn_of_not_mem _ hz

theorem restrict_rot_of_rot_mem {A : Finset D} {z : D} (hz : z ∈ A) (h : R.rot z ∈ A) :
    (R.restrict A).rot z = R.rot z :=
  firstReturn_eq_of_trail _ hz (Trail.here h)

theorem isolatedEdge_restrict {A : Finset D} (hcA : c ∉ A) (hrA : R.rev c ∉ A) :
    (R.restrict A).IsolatedEdge c :=
  ⟨restrict_rot_of_not_mem hcA, restrict_rot_of_not_mem hrA⟩

theorem restrict_restrict {S T : Finset D} (h : T ⊆ S) :
    (R.restrict S).restrict T = R.restrict T :=
  RotSystem.ext rfl (firstReturn_firstReturn R.rot h)

theorem restrict_univ : R.restrict Finset.univ = R := by
  refine RotSystem.ext rfl ?_
  ext z
  rw [restrict_rot_of_rot_mem (Finset.mem_univ z) (Finset.mem_univ _)]

/-- Adding one dart to a restriction attaches it after its predecessor. -/
theorem restrict_insert {A : Finset D} {z : D} (hz : z ∉ A) :
    R.restrict (insert z A) = (R.restrict A).attach z (firstReturn R.rot⁻¹ (insert z A) z) :=
  RotSystem.ext rfl (firstReturn_insert R.rot hz)

/-- A fixed point of the rotation makes no difference to a restriction. -/
theorem restrict_insert_of_fixed {A : Finset D} {z : D} (hfix : R.rot z = z) (hz : z ∉ A) :
    R.restrict (insert z A) = R.restrict A :=
  RotSystem.ext rfl (firstReturn_insert_of_fixed R.rot hfix hz)

theorem genus_restrict_le_insert {A : Finset D} {z : D} (hz : z ∉ A) :
    (R.restrict A).toHypermap.genus ≤ (R.restrict (insert z A)).toHypermap.genus := by
  rw [restrict_insert hz]
  exact (R.restrict A).genus_le_attach _ (restrict_rot_of_not_mem hz)

/-- Deleting darts never raises the genus. -/
theorem genus_restrict_le_of_subset {S T : Finset D} (h : T ⊆ S) :
    (R.restrict T).toHypermap.genus ≤ (R.restrict S).toHypermap.genus := by
  have key : ∀ U : Finset D,
      (R.restrict T).toHypermap.genus ≤ (R.restrict (U ∪ T)).toHypermap.genus := by
    intro U
    induction U using Finset.induction_on with
    | empty => rw [Finset.empty_union]
    | insert z U _ ih =>
      rw [Finset.insert_union]
      by_cases hz : z ∈ U ∪ T
      · rw [Finset.insert_eq_of_mem hz]
        exact ih
      · exact ih.trans (genus_restrict_le_insert hz)
  have h1 := key S
  rwa [Finset.union_eq_left.2 h] at h1

theorem genus_restrict_le (A : Finset D) :
    (R.restrict A).toHypermap.genus ≤ R.toHypermap.genus := by
  have h1 := genus_restrict_le_of_subset (R := R) (Finset.subset_univ A)
  rwa [restrict_univ] at h1

theorem planar_restrict (hR : R.Planar) (A : Finset D) : (R.restrict A).Planar :=
  Nat.le_zero.1 ((genus_restrict_le A).trans (Nat.le_of_eq hR))

theorem tail_restrict_iff {A : Finset D} {a b : D} (ha : a ∈ A) (hb : b ∈ A) :
    (R.restrict A).tail a = (R.restrict A).tail b ↔ R.tail a = R.tail b := by
  rw [tail_eq_iff, tail_eq_iff]
  exact fconnect_firstReturn_iff R.rot ha hb

theorem restrict_facePerm (A : Finset D) (z : D) :
    (R.restrict A).facePerm z = firstReturn R.rot⁻¹ A (R.rev z) := by
  rw [← firstReturn_inv]
  rfl

theorem restrict_facePerm_of_mem {A : Finset D} {z : D} (hz : R.rev z ∈ A)
    (h : R.facePerm z ∈ A) : (R.restrict A).facePerm z = R.facePerm z := by
  rw [restrict_facePerm]
  exact firstReturn_eq_of_trail _ hz (Trail.here h)

/-! ### Corners of a restriction -/

variable (R) in
/-- The last dart of `A` at or before `x` in the rotation: the corner `x` of `R` lies in the corner
`predIn A x` of the restriction to `A`. If the vertex of `x` has no dart of `A`, this is `x`. -/
noncomputable def predIn (A : Finset D) (x : D) : D :=
  if x ∈ A then x else firstReturn R.rot⁻¹ (insert x A) x

theorem predIn_of_mem {A : Finset D} {z : D} (hz : z ∈ A) : R.predIn A z = z := by
  simp [predIn, hz]

theorem predIn_of_not_mem {A : Finset D} {z : D} (hz : z ∉ A) :
    R.predIn A z = firstReturn R.rot⁻¹ (insert z A) z := by
  simp [predIn, hz]

/-- `predIn A z` is the first dart of `A` on the backward orbit of `z`, with `z` included. -/
theorem predIn_trail {A : Finset D} {z : D} (h : ∃ a ∈ A, R.tail a = R.tail z) :
    Trail R.rot⁻¹ A z (R.predIn A z) := by
  by_cases hz : z ∈ A
  · rw [predIn_of_mem hz]
    exact Trail.here hz
  · obtain ⟨a, ha, hta⟩ := h
    have hzW : z ∈ insert z A := Finset.mem_insert_self z A
    have haW : a ∈ insert z A := Finset.mem_insert_of_mem ha
    have hconn : fconnect (⇑R.rot⁻¹) z a :=
      (fconnect_inv_iff R.rot).2 ((R.tail_eq_iff z a).1 hta.symm)
    have hne : firstReturn R.rot⁻¹ (insert z A) z ≠ z := fun e =>
      hz (eq_of_fconnect_of_fixed e ((fconnect_firstReturn_iff R.rot⁻¹ hzW haW).2 hconn) ▸ ha)
    have hmem : firstReturn R.rot⁻¹ (insert z A) z ∈ A :=
      (Finset.mem_insert.1 ((firstReturn_mem_iff _ _ z).2 hzW)).resolve_left hne
    rw [predIn_of_not_mem hz]
    exact Trail.step hz ((firstReturn_trail R.rot⁻¹ hzW).mono (Finset.subset_insert z A) hmem)

/-- The first dart of `A` on the backward orbit is `predIn`. -/
theorem predIn_eq_of_trail {A : Finset D} {z p : D} (h : Trail R.rot⁻¹ A z p) :
    R.predIn A z = p :=
  (predIn_trail ⟨p, h.mem, ((R.tail_eq_iff z p).2
    ((fconnect_inv_iff R.rot).1 h.to_fconnect)).symm⟩).unique h

theorem predIn_mem {A : Finset D} {z : D} (h : ∃ a ∈ A, R.tail a = R.tail z) :
    R.predIn A z ∈ A :=
  (predIn_trail h).mem

theorem tail_predIn (A : Finset D) (z : D) : R.tail (R.predIn A z) = R.tail z := by
  by_cases hz : z ∈ A
  · rw [predIn_of_mem hz]
  · rw [predIn_of_not_mem hz]
    exact ((R.tail_eq_iff _ _).2
      ((fconnect_inv_iff R.rot).1 (fconnect_firstReturn R.rot⁻¹ _ z))).symm

private theorem exists_iterate_of_trail_inv {A : Finset D} {z p : D}
    (h : Trail R.rot⁻¹ A z p) :
    ∃ k, (⇑R.rot)^[k] p = z ∧ ∀ j, 0 < j → j ≤ k → (⇑R.rot)^[j] p ∉ A := by
  induction h with
  | here _ => exact ⟨0, rfl, fun j h0 hj => absurd h0 (by omega)⟩
  | @step y w hn _ ih =>
    obtain ⟨k, hk, hj⟩ := ih
    have hk' : (⇑R.rot)^[k + 1] w = y := by
      rw [Function.iterate_succ_apply', hk, perm_apply_inv_self]
    refine ⟨k + 1, hk', fun j h0 hjk => ?_⟩
    by_cases hjk' : j = k + 1
    · rw [hjk', hk']
      exact hn
    · exact hj j h0 (by omega)

/-- From `predIn A z` the rotation reaches `z` without meeting `A`. -/
theorem predIn_spec {A : Finset D} {z : D} (h : ∃ a ∈ A, R.tail a = R.tail z) :
    ∃ k, (⇑R.rot)^[k] (R.predIn A z) = z ∧ ∀ j, 0 < j → j ≤ k → (⇑R.rot)^[j] (R.predIn A z) ∉ A :=
  exists_iterate_of_trail_inv (predIn_trail h)

/-- A step of the rotation to a dart off `A` keeps the corner. -/
theorem predIn_rot {A : Finset D} {z : D} (hA : ∃ a ∈ A, R.tail a = R.tail z) (h : R.rot z ∉ A) :
    R.predIn A (R.rot z) = R.predIn A z :=
  predIn_eq_of_trail (Trail.step h (by
    rw [perm_inv_apply_self]
    exact predIn_trail hA))

/-- Attaching and restricting commute: the corner `x` becomes the corner `predIn W x`. -/
theorem attach_restrict {W : Finset D} (hc : R.rot c = c) (hcW : c ∈ W) (hxc : x ≠ c)
    (hxW : ∃ a ∈ W, R.tail a = R.tail x) :
    (R.attach c x).restrict W = (R.restrict W).attach c (R.predIn W x) := by
  refine RotSystem.ext rfl ?_
  show firstReturn (R.rot * Equiv.swap x c) W = firstReturn R.rot W * Equiv.swap (R.predIn W x) c
  by_cases hx : x ∈ W
  · rw [predIn_of_mem hx]
    exact firstReturn_mul_right R.rot (fixesOff_swap_of_mem hx hcW)
  · have hpW : R.predIn W x ∈ W := predIn_mem hxW
    have hpc : R.predIn W x ≠ c := by
      intro e
      have h1 : R.tail c = R.tail x := by rw [← e, tail_predIn]
      exact hxc (eq_of_fconnect_of_fixed hc ((R.tail_eq_iff c x).1 h1))
    have h1 : firstReturn (R.rot * Equiv.swap x c) (insert x W) =
        firstReturn R.rot (insert x W) * Equiv.swap x c :=
      firstReturn_mul_right R.rot (fixesOff_swap_of_mem (Finset.mem_insert_self x W)
        (Finset.mem_insert_of_mem hcW))
    have h2 := firstReturn_insert R.rot hx
    rw [← predIn_of_not_mem hx] at h2
    rw [← firstReturn_firstReturn (R.rot * Equiv.swap x c) (Finset.subset_insert x W), h1, h2,
      mul_assoc, swap_mul_swap_comm hpc hxc, ← mul_assoc]
    exact firstReturn_mul_swap_of_fixed
      ((fixesOff_firstReturn R.rot W).mul (fixesOff_swap_of_mem hpW hcW)) hx hpW

/-- A chord and a restriction commute, if the two corners stay apart. -/
theorem restrict_chord {A : Finset D} (hc : R.IsolatedEdge c) (hcA : c ∉ A) (hrA : R.rev c ∉ A)
    (hx : R.Off c x) (hy : R.Off c y) (hxA : ∃ a ∈ A, R.tail a = R.tail x)
    (hyA : ∃ a ∈ A, R.tail a = R.tail y) (hne : R.predIn A x ≠ R.predIn A y) :
    (R.chord c x y).restrict (insert c (insert (R.rev c) A)) =
      (R.restrict A).chord c (R.predIn A x) (R.predIn A y) := by
  have hsub : A ⊆ insert c (insert (R.rev c) A) := fun a ha =>
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha)
  have hcW : c ∈ insert c (insert (R.rev c) A) := Finset.mem_insert_self _ _
  have hrW : R.rev c ∈ insert c (insert (R.rev c) A) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hoff : ∀ u, R.Off c u → u ∉ A → u ∉ insert c (insert (R.rev c) A) := fun u hu huA => by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hu.1, hu.2, huA⟩
  have hrest : R.restrict (insert c (insert (R.rev c) A)) = R.restrict A := by
    have hc2 : c ∉ insert (R.rev c) A := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨(R.rev_ne c).symm, hcA⟩
    rw [restrict_insert_of_fixed hc.rot_self hc2, restrict_insert_of_fixed hc.rot_rev hrA]
  have hpx : R.predIn (insert c (insert (R.rev c) A)) x = R.predIn A x :=
    predIn_eq_of_trail ((predIn_trail hxA).transfer hsub (R.Off c) hx
      fun u hu huA _ => ⟨hoff u hu huA, rfl, hu.rot_inv hc⟩)
  have hqy : (R.attach c x).predIn (insert c (insert (R.rev c) A)) y = R.predIn A y := by
    refine predIn_eq_of_trail ((predIn_trail hyA).transfer hsub (R.Off c) hy fun u hu huA ht => ?_)
    refine ⟨hoff u hu huA, ?_, hu.rot_inv hc⟩
    have hrx : R.rot⁻¹ u ≠ x := fun e => hne (predIn_eq_of_trail (e ▸ ht))
    rw [attach_rot, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hrx (hu.rot_inv hc).1]
  have step1 : (R.attach c x).restrict (insert c (insert (R.rev c) A)) =
      (R.restrict A).attach c (R.predIn A x) := by
    rw [R.attach_restrict hc.rot_self hcW hx.1 (hxA.imp fun a ha => ⟨hsub ha.1, ha.2⟩), hrest, hpx]
  have hdart : ∃ a ∈ insert c (insert (R.rev c) A),
      (R.attach c x).tail a = (R.attach c x).tail y :=
    ⟨R.predIn A y, hsub (predIn_mem hyA), ((R.attach c x).tail_eq_iff _ _).2
      (fconnect_mul_swap_of_fconnect R.rot hc.rot_self x ((R.tail_eq_iff _ _).1 (tail_predIn A y)))⟩
  show ((R.attach c x).attach (R.rev c) y).restrict (insert c (insert (R.rev c) A)) =
    ((R.restrict A).attach c (R.predIn A x)).attach (R.rev c) (R.predIn A y)
  rw [(R.attach c x).attach_restrict (attach_rot_rev hc hx) hrW hy.2 hdart, step1, hqy]

/-- **Corners of one face stay in one face of a connected restriction.** -/
theorem fconnect_predIn_of_fconnect {A : Finset D} (hR : R.Planar) (hc : R.IsolatedEdge c)
    (hcA : c ∉ A) (hrA : R.rev c ∉ A) (hx : R.Off c x) (hy : R.Off c y)
    (hconn : (R.restrict A).ConnOn A) (hxA : ∃ a ∈ A, R.tail a = R.tail x)
    (hyA : ∃ a ∈ A, R.tail a = R.tail y) (h : fconnect R.facePerm x y) :
    fconnect (R.restrict A).facePerm (R.predIn A x) (R.predIn A y) := by
  by_cases hne : R.predIn A x = R.predIn A y
  · rw [hne]
  by_contra hf
  have hpA := predIn_mem hxA
  have hqA := predIn_mem hyA
  have hp : (R.restrict A).Off c (R.predIn A x) :=
    ⟨fun e => hcA (e ▸ hpA), fun e => hrA (e ▸ hpA)⟩
  have hq : (R.restrict A).Off c (R.predIn A y) :=
    ⟨fun e => hcA (e ▸ hqA), fun e => hrA (e ▸ hqA)⟩
  have h1 := genus_chord_of_not_fconnect (isolatedEdge_restrict hcA hrA) hp hq hf
    (hconn _ hpA _ hqA)
  have h2 : ((R.chord c x y).restrict (insert c (insert (R.rev c) A))).toHypermap.genus = 0 :=
    planar_restrict (planar_chord hR hc hx hy h) _
  rw [restrict_chord hc hcA hrA hx hy hxA hyA hne, h1] at h2
  omega

/-- **Twisted pair.** Two chords between the same two corners in the same order at both ends raise
the genus. -/
theorem genus_twisted {c' : D} (hc : R.IsolatedEdge c) (hc' : R.IsolatedEdge c') (hx : R.Off c x)
    (hy : R.Off c y) (hx' : R.Off c' x) (hy' : R.Off c' y) (hcc : R.Off c' c)
    (hg : R.toHypermap.gcomp x y) (hxy : x ≠ y) :
    R.toHypermap.genus + 1 ≤ ((R.chord c x y).chord c' x y).toHypermap.genus := by
  have hi : (R.chord c x y).IsolatedEdge c' := hc'.chord hx' hy' hcc
  by_cases hf : fconnect R.facePerm x y
  · have hs := fconnect_sym (R.chord c x y).facePerm.injective
    have hnf : ¬ fconnect (R.chord c x y).facePerm x y := fun e =>
      not_fconnect_chord hc hx hy hf (connect_trans (fconnect_chord_c_right hc hx hy)
        (connect_trans (hs _ _ e) (hs _ _ (fconnect_chord_rev_left hc hx hy hxy))))
    have h1 := genus_chord_of_not_fconnect hi hx' hy' hnf ((gcomp_chord_iff hc hx hy hg hx hy).2 hg)
    rw [h1, genus_chord_of_fconnect hc hx hy hf]
  · rw [← genus_chord_of_not_fconnect hc hx hy hf hg]
    exact ((R.chord c x y).genus_le_attach x hi.rot_self).trans
      (((R.chord c x y).attach c' x).genus_le_attach y (attach_rot_rev hi hx'))

variable (R)

/-! ### Free edges -/

/-- `R` with `k` further isolated edges. -/
def lift (k : ℕ) : RotSystem (D ⊕ Fin k × Bool) where
  rev := Sum.elim (fun d => Sum.inl (R.rev d)) (fun i => Sum.inr (i.1, !i.2))
  rev_rev := by
    rintro (d | i)
    · simp [R.rev_rev]
    · simp
  rev_ne := by
    rintro (d | ⟨i, b⟩)
    · simpa using R.rev_ne d
    · simp
  rot := Equiv.sumCongr R.rot 1

variable {R}

theorem lift_rev_inl (k : ℕ) (d : D) : (R.lift k).rev (Sum.inl d) = Sum.inl (R.rev d) := rfl

theorem lift_rot_inl (k : ℕ) (d : D) : (R.lift k).rot (Sum.inl d) = Sum.inl (R.rot d) := rfl

theorem lift_isolatedEdge (k : ℕ) (i : Fin k × Bool) : (R.lift k).IsolatedEdge (Sum.inr i) :=
  ⟨rfl, rfl⟩

theorem lift_glink_inl (k : ℕ) (a b : D) :
    (R.lift k).toHypermap.glink (Sum.inl a) (Sum.inl b) ↔ R.toHypermap.glink a b :=
  or_congr Sum.inl_injective.eq_iff (or_congr Sum.inl_injective.eq_iff Sum.inl_injective.eq_iff)

theorem lift_glink_inr (k : ℕ) (a b : Fin k × Bool) :
    (R.lift k).toHypermap.glink (Sum.inr a) (Sum.inr b) ↔ pairLink a b := by
  constructor
  · rintro (h | h | h)
    · exact Or.inl (Sum.inr_injective h)
    · exact Or.inr (Sum.inr_injective h)
    · exact Or.inl (Sum.inr_injective h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

theorem lift_not_glink_inl_inr (k : ℕ) (a : D) (b : Fin k × Bool) :
    ¬ (R.lift k).toHypermap.glink (Sum.inl a) (Sum.inr b) := by
  rintro (h | h | h) <;> exact absurd h Sum.inl_ne_inr

theorem lift_not_glink_inr_inl (k : ℕ) (a : Fin k × Bool) (b : D) :
    ¬ (R.lift k).toHypermap.glink (Sum.inr a) (Sum.inl b) := by
  rintro (h | h | h) <;> exact absurd h Sum.inr_ne_inl

theorem numVertices_lift (k : ℕ) : (R.lift k).numVertices = R.numVertices + 2 * k := by
  have h := nComp_sum (e := frel (R.lift k).toHypermap.node) (e₁ := frel R.toHypermap.node)
    (e₂ := frel ⇑(1 : Equiv.Perm (Fin k × Bool))) (R.lift k).toHypermap.cnode_sym
    (fun _ _ => Sum.inl_injective.eq_iff) (fun _ _ => Sum.inr_injective.eq_iff)
    (fun _ _ => Sum.inl_ne_inr) (fun _ _ => Sum.inr_ne_inl)
  have h2 : fcard (⇑(1 : Equiv.Perm (Fin k × Bool))) Set.univ = 2 * k := by
    have h3 := orb_one (D := Fin k × Bool)
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h3
    exact h3.trans (Nat.mul_comm k 2)
  exact h.trans (congrArg (fun n => R.numVertices + n) h2)

theorem numFaces_lift (k : ℕ) : (R.lift k).numFaces = R.numFaces + k := by
  have h := nComp_sum (e := frel (R.lift k).toHypermap.face) (e₁ := frel R.toHypermap.face)
    (e₂ := frel (flipPair (k := k))) (R.lift k).toHypermap.cface_sym
    (fun _ _ => Sum.inl_injective.eq_iff) (fun _ _ => Sum.inr_injective.eq_iff)
    (fun _ _ => Sum.inl_ne_inr) (fun _ _ => Sum.inr_ne_inl)
  exact h.trans (congrArg (fun n => R.numFaces + n) (fcard_flipPair k))

theorem numEdges_lift (k : ℕ) : (R.lift k).numEdges = R.numEdges + k := by
  have h := nComp_sum (e := frel (R.lift k).toHypermap.edge) (e₁ := frel R.toHypermap.edge)
    (e₂ := frel (flipPair (k := k))) (R.lift k).toHypermap.cedge_sym
    (fun _ _ => Sum.inl_injective.eq_iff) (fun _ _ => Sum.inr_injective.eq_iff)
    (fun _ _ => Sum.inl_ne_inr) (fun _ _ => Sum.inr_ne_inl)
  exact h.trans (congrArg (fun n => R.numEdges + n) (fcard_flipPair k))

theorem numComponents_lift (k : ℕ) : (R.lift k).numComponents = R.numComponents + k := by
  have h := nComp_sum (e := (R.lift k).toHypermap.glink) (e₁ := R.toHypermap.glink)
    (e₂ := pairLink (k := k)) (R.lift k).toHypermap.glinkC (R.lift_glink_inl k) (R.lift_glink_inr k)
    (R.lift_not_glink_inl_inr k) (R.lift_not_glink_inr_inl k)
  exact h.trans (congrArg (fun n => R.numComponents + n) (nComp_pairLink k))

theorem genus_lift (k : ℕ) : (R.lift k).toHypermap.genus = R.toHypermap.genus := by
  have h1 := R.genus_formula
  have h2 := (R.lift k).genus_formula
  have hV := R.numVertices_lift k
  have hF := R.numFaces_lift k
  have hE := R.numEdges_lift k
  have hC := R.numComponents_lift k
  omega

theorem planar_lift (k : ℕ) : (R.lift k).Planar ↔ R.Planar := by
  show (R.lift k).toHypermap.genus = 0 ↔ R.toHypermap.genus = 0
  rw [genus_lift]

theorem tail_lift_iff (k : ℕ) (a b : D) :
    (R.lift k).tail (Sum.inl a) = (R.lift k).tail (Sum.inl b) ↔ R.tail a = R.tail b := by
  rw [tail_eq_iff, tail_eq_iff]
  exact connect_inl_iff (e := frel (R.lift k).toHypermap.node) (e₁ := frel R.toHypermap.node)
    (fun _ _ => Sum.inl_injective.eq_iff) (fun _ _ => Sum.inl_ne_inr) a b

theorem fconnect_lift_face_iff (k : ℕ) (a b : D) :
    fconnect (R.lift k).facePerm (Sum.inl a) (Sum.inl b) ↔ fconnect R.facePerm a b :=
  connect_inl_iff (e := frel (R.lift k).facePerm) (e₁ := frel R.facePerm)
    (fun _ _ => Sum.inl_injective.eq_iff) (fun _ _ => Sum.inl_ne_inr) a b

theorem gcomp_lift_iff (k : ℕ) (a b : D) :
    (R.lift k).toHypermap.gcomp (Sum.inl a) (Sum.inl b) ↔ R.toHypermap.gcomp a b :=
  connect_inl_iff (R.lift_glink_inl k) (R.lift_not_glink_inl_inr k) a b

end RotSystem

end SsspFlow
