import FourColor

/-!
Axiom audit of the main results of the vendored planarity development.
Expected output for each: only `propext`, `Classical.choice`, `Quot.sound`.
-/

-- Jordan characterization of planarity (`FourColor/Jordan.lean`, `Jordan/PlanarJordan.lean`)
#print axioms FourColor.Hypermap.planar_iff_jordan
#print axioms FourColor.Hypermap.jordan_of_planar
#print axioms FourColor.Hypermap.planar_of_jordan

-- Euler and genus results (`Jordan/EvenGenus.lean`, `Jordan/EulerTree.lean`)
#print axioms FourColor.Hypermap.evenGenus
#print axioms FourColor.Hypermap.euler_le
#print axioms FourColor.Hypermap.euler_tree

-- Walkup transforms (`Walkup/Genus.lean`, `Walkup/Jordan.lean`, `Walkup/Edge.lean`, `Walkup/Comp.lean`)
#print axioms FourColor.Hypermap.genus_WalkupE_eq
#print axioms FourColor.Hypermap.planar_WalkupE
#print axioms FourColor.Hypermap.planar_WalkupN
#print axioms FourColor.Hypermap.planar_WalkupF
#print axioms FourColor.Hypermap.jordan_WalkupE
#print axioms FourColor.Hypermap.euler_rhs_WalkupE
#print axioms FourColor.Hypermap.euler_lhs_WalkupE

-- Snip (`Snip.lean`)
#print axioms FourColor.Hypermap.planar_snipd
#print axioms FourColor.Hypermap.planar_snipr
#print axioms FourColor.Hypermap.snip_patch

-- Patch (`Patch.lean`)
#print axioms FourColor.Hypermap.Patch.genus_patch
#print axioms FourColor.Hypermap.Patch.planar_patch

-- Sew (`Sew.lean`)
#print axioms FourColor.Hypermap.sew_map_patch
