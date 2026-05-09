# Bárány's Colorful Carathéodory — milestone log

## Status

- Blueprint: `numina/blueprints/numina-test/numina-test.tex` (5 declarations,
  parsed cleanly).
- Lean: `NuminafuseTest/Blueprint.lean` builds; 3 of 5 declarations proved,
  2 remaining sorries.
- Build: success, 1 unused-variable warning (cosmetic, in `kkt_inner_ge`),
  2 expected `sorry` warnings.

## Proved (3/5)

- `lem:cc_finite_reduction` -> `NuminafuseTest.Blueprint.finite_reduction`.
  Uses `Caratheodory.minCardFinsetOfMemConvexHull` for finite reduction.
- `lem:cc_min_simplex` -> `NuminafuseTest.Blueprint.exists_min_rainbow`.
  Uses `Fintype.piFinset` for compatible-tuple enumeration and
  `Set.Finite.isCompact_convexHull` + `IsCompact.exists_isMinOn` for
  per-tuple norm minimization, then `Finset.exists_min_image` over tuples.
  Includes a `set_option synthInstance.maxHeartbeats 80000` for the compact
  hull synthesis.
- `lem:cc_kkt` -> `NuminafuseTest.Blueprint.kkt_inner_ge`.
  Wraps Mathlib's `norm_eq_iInf_iff_real_inner_le_zero` (Hilbert projection
  variational inequality) and rewrites via `inner_sub_right`.

## Remaining sorries (2/5)

### `lem:cc_replacement` -> `NuminafuseTest.Blueprint.strict_improvement`

Statement (final, existential form):

    ∀ (T : Fin (d+1) → Set (EuclideanSpace ℝ (Fin d))),
      (∀ i, (T i).Finite) →
      (∀ i, 0 ∈ convexHull ℝ (T i)) →
      ∀ (p : Fin (d+1) → EuclideanSpace ℝ (Fin d)),
        (∀ i, p i ∈ T i) →
        ∀ (q : EuclideanSpace ℝ (Fin d)),
          q ∈ convexHull ℝ (Set.range p) → q ≠ 0 →
          (∀ j, ⟪q, q⟫ ≤ ⟪q, p j⟫) →
          ∃ p' q', (∀ i, p' i ∈ T i) ∧
            q' ∈ convexHull ℝ (Set.range p') ∧ ‖q'‖ < ‖q‖

History: an earlier "for any i and any c" universal form was
unsound — counterexample with d = 2,
p = ((1,0),(1,1),(10,10)), q = (1,0), i = 0, c = (-0.001, 100):
new convex hull has every y ≥ 1, so min ‖·‖² ≥ 1 = ‖q‖², no
strict improvement. The corrected statement quantifies existentially
in i and chooses both i and c using the hypothesis that
0 ∈ convexHull (T i).

Proof outline (Bárány):
1. Since 0 ∈ convexHull (T i) for every i, expanding 0 as a convex
   combination over T i and pairing with q yields some i and c ∈ T i
   with ⟪q, c⟫ ≤ 0.
2. Combine with KKT (⟪q, p i⟫ ≥ ⟪q, q⟫ > 0) to get that the
   segment from p i to c crosses the hyperplane {x : ⟪q, x⟫ = ⟪q, q⟫}
   at some interior point, and shows the segment intersects the open
   ball of radius ‖q‖.
3. Among the d+2 augmented points range p ∪ {c}, by Carathéodory in
   ℝ^d, any point of conv(d+2 pts) is in conv of d+1 of them; pick
   the redundant vertex to drop and form p'.

Difficulty in Lean: step 3 (Carathéodory dimension reduction with
explicit vertex selection so that the resulting tuple remains
compatible per-colour) is intricate. Mathlib has
`Caratheodory.minCardFinsetOfMemConvexHull` but it does not directly
preserve the per-colour assignment. A practical Lean route is
likely:
  - Choose i, c via convex-combination unpacking.
  - Reparameterize: build q'' on the segment {(1-t) p i + t c : t ∈ [0,1]}
    and show ‖q''‖ < ‖q‖ for the optimal t (a 1-D quadratic
    minimization in t closed-form).
  - Define p' = Function.update p i c; the new convex hull contains
    q'' since q'' is a convex combination of p i and c, both of
    which lie in conv(range p').
  - This avoids Carathéodory entirely if p' = update p i c; the
    Carathéodory reduction is only needed if one wanted to keep
    p i in the tuple, which is unnecessary.

So the cleaner Lean strategy collapses to:
  - Find i, c ∈ T i with ⟪q, c⟫ ≤ 0 (existence from KKT and
    0 ∈ conv(T i)).
  - Set p' = update p i c, t* = argmin_{t ∈ [0,1]} ‖(1-t) q + t c'‖²
    where c' is some explicit point built from p i, c, q.
  - Prove ‖q'‖ < ‖q‖ via 1-D calculus (positive coefficient on a
    quadratic with negative initial derivative).
  - Each step is concrete in Mathlib.

### `thm:colorful_caratheodory` -> `NuminafuseTest.Blueprint.MainTheorem`

Once `strict_improvement` is in hand, the main theorem is direct:
combine `finite_reduction`, `exists_min_rainbow`, and contradiction via
`strict_improvement`. The argument is short (~30 lines of Lean) and
the blueprint proof block already spells it out.

## Next session

- Dispatch a focused prover on `strict_improvement` using the
  "1-D segment minimization via update p i c" strategy outlined above.
- After `strict_improvement` is proved, dispatch a small prover for
  `MainTheorem` (or do it directly).
- Mark both proved.
