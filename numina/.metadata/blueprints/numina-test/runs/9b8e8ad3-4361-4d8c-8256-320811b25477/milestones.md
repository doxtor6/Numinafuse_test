# Run milestones — numina-test (Colorful Carathéodory split)

## Scope
Refine the blueprint and Lean file to split Bárány's Colorful
Carathéodory theorem into four named helper lemmas plus the main
theorem so each is independently provable.

## Files processed
- `numina/blueprints/numina-test/numina-test.tex` — rewritten with
  helper lemma blocks, theorem block, and a separate proof block that
  cites the helpers.
- `numina/blueprints/numina-test/source/numina-test-source.tex` —
  mirrored.
- `numina/.metadata/blueprints/numina-test/blueprint.json` and
  `declarations/` — refreshed.
- `NuminafuseTest/Blueprint.lean` — rewritten with five sorry'd
  declarations (4 helpers + `MainTheorem`); builds with 5 expected
  sorry warnings, no errors.

## Declarations registered
- `lem:cc_finite_reduction` → `NuminafuseTest.Blueprint.finite_reduction`
- `lem:cc_min_simplex` → `NuminafuseTest.Blueprint.exists_min_rainbow`
  (uses `lem:cc_finite_reduction`)
- `lem:cc_kkt` → `NuminafuseTest.Blueprint.kkt_inner_ge`
- `lem:cc_replacement` → `NuminafuseTest.Blueprint.replacement_strictly_closer`
  (uses `lem:cc_kkt`)
- `thm:colorful_caratheodory` → `NuminafuseTest.Blueprint.MainTheorem`
  (uses all four helpers)

## Lean stub signatures (paraphrased)
- `finite_reduction`: from `∀ i, 0 ∈ conv (C i)` produce a finite
  `T i ⊆ C i` with `0 ∈ conv (T i)`.
- `exists_min_rainbow`: for finitely many nonempty colour classes,
  the infimum of `‖q‖` over compatible rainbow simplices is attained.
- `kkt_inner_ge`: at the closest point `q` of `conv S` (S finite),
  `⟪q, q⟫ ≤ ⟪q, s⟫` for every `s ∈ S`.
- `replacement_strictly_closer`: with the KKT condition and a vertex
  swap to a point `c` with `⟪q, c⟫ ≤ 0`, produce a strictly closer
  point in the new rainbow simplex.
- `MainTheorem`: the full Colorful Carathéodory statement.

Notation: `⟪x, y⟫` is `inner ℝ x y`, enabled via
`open scoped RealInnerProductSpace`.

## Build status
- `lean_diagnostic_messages` on `NuminafuseTest/Blueprint.lean`:
  success, 5 sorry warnings (one per declaration), no errors.

## Next actionable items
- Prove `finite_reduction` (Mathlib's `convexHull_eq_union_convexHull_finite_subsets`
  / Carathéodory finite-reduction is the main ingredient).
- Prove `kkt_inner_ge` (Mathlib's `norm_eq_iInf_iff_real_inner_le_zero`
  for closest-point projection in a convex set).
- Prove `exists_min_rainbow` (finitely many tuples, infimum of `‖·‖`
  on each compact convex hull is attained, then take the minimum).
- Prove `replacement_strictly_closer` (analytic — track distance
  along a segment from `q` toward `c` and use `⟪q, c⟫ ≤ 0 < ⟪q, q⟫`).
- Assemble `MainTheorem` from helpers (the "some `c ∈ T_i` has
  `⟪q, c⟫ ≤ 0`" step uses convex-combination expansion and a
  pigeonhole-style minimum on finitely many points).
