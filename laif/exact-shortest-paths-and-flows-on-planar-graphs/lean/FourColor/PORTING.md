# Porting notes

Source: https://github.com/RBarish-UTokyo/FourColorTheorem-Lean4
Commit: 20fa34599f5189dd569d96dd22f306c94ab1c446
Licence: Apache-2.0 (see `LICENSE`, `NOTICE`, `LICENSES/`)
Upstream target: Lean `v4.35.0-rc2`, Mathlib `v4.35.0-rc2`
Target here: Lean `leanprover/lean4:v4.36.0-rc1`, Mathlib commit `d875a8de`

Only the planarity part is vendored: `Seq`, `FinGraph`, `Hypermap`, `Walkup`
(`Basic`, `Comp`, `Edge`, `Genus`, `Jordan`), `Jordan` (`EulerTree`, `EvenGenus`,
`PlanarJordan`), `Geometry`, `Color`, `Chromogram`, `Coloring`, `Patch`, `Snip`,
`Sew`, and the root `FourColor.lean` (which imports only these modules).
The option `autoImplicit = false` is set through the `lean_lib` entry in
`lakefile.toml` instead of the upstream package-wide `[leanOptions]` table.

No statement (name, binders, type) of any declaration was changed.

## Changes

(file, declaration, change, reason)

None. All 19 vendored modules and the root `FourColor.lean` compile unchanged
under Lean `v4.36.0-rc1` and Mathlib `d875a8de`; they are byte-identical to the
upstream files at the commit above. The only compiler output is the warning
`imports ... designed for use with the module system`, emitted for Mathlib
imports and harmless.

## Added files (not part of the upstream development)

- `PORTING.md`: this file.
- `Axioms.lean`: `#print axioms` for the main results (`planar_iff_jordan`,
  `jordan_of_planar`, `planar_of_jordan`, `evenGenus`, `euler_le`, `euler_tree`,
  the Walkup genus, planarity, Jordan and Euler lemmas, `planar_snipd`,
  `planar_snipr`, `snip_patch`, `Patch.genus_patch`, `Patch.planar_patch`,
  `sew_map_patch`). It is not imported by `FourColor.lean`; run it with
  `lake env lean FourColor/Axioms.lean`.
- `axioms.txt`: its output. Every listed result depends only on `propext`,
  `Classical.choice` and `Quot.sound`.
