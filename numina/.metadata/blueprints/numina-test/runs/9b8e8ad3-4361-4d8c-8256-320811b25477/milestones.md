# Run milestones — numina-test (Colorful Carathéodory refinement)

## Scope
The user replaced the previous problem (de Bruijn--Erdős) with the
Bárány Colorful Carathéodory theorem in `NuminafuseTest/Blueprint.lean`
and asked for the blueprint .tex to be updated to match. Refinement
only — no formalization or proving was requested.

## Files processed
- `NuminafuseTest/Blueprint.lean` — read (left as-is; contains the
  user's new sorry'd `MainTheorem`).
- `numina/blueprints/numina-test/numina-test.tex` — rewritten.
- `numina/blueprints/numina-test/source/numina-test-source.tex` —
  mirrored.
- `numina/.metadata/blueprints/numina-test/blueprint.json` and
  `declarations/` — refreshed.

## Declarations registered (post-refresh)
- `thm:colorful_caratheodory` — main theorem; carries
  `\lean{NuminafuseTest.Blueprint.MainTheorem}` and
  `\leanfile{NuminafuseTest/Blueprint.lean}`. No `\leanok` (proof body
  is `sorry`).

The previous declarations (`def:k_coloring`, `def:finite_subgraph`,
`thm:de_bruijn_erdos`) are no longer in the LaTeX and were removed
from `blueprint.json` / `declarations/` by the metadata refresh.

## Lean signature (for reference)
```
theorem MainTheorem (d : ℕ)
    (C : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)))
    (hC : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (C i)) :
    ∃ p : Fin (d + 1) → EuclideanSpace ℝ (Fin d),
      (∀ i, p i ∈ C i) ∧
      (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (Set.range p) := by
  sorry
```

## What was changed in the LaTeX
- Discarded the de Bruijn--Erdős theorem block and its two
  prerequisite definitions.
- Wrote a new `\begin{theorem}` block for Bárány's Colorful
  Carathéodory theorem with:
  - `\label{thm:colorful_caratheodory}`.
  - `\lean{NuminafuseTest.Blueprint.MainTheorem}` and
    `\leanfile{NuminafuseTest/Blueprint.lean}` so the metadata refresh
    links the blueprint to the existing Lean stub.
  - A statement that names the d+1 colour classes \(C_0, \dots, C_d\)
    in \(\mathbb{R}^d\), the hypothesis \(0 \in \operatorname{conv}(C_i)\),
    and the conclusion that some rainbow choice has \(0\) in its
    convex hull.
- No prerequisite definitions added: \(\mathbb{R}^d\), convex hull,
  and finite point families are standard Mathlib notions, so a single
  theorem block with self-contained notation is the cleanest blueprint.

## Next actionable items (awaiting user direction)
- Decide whether to attempt a proof of `MainTheorem` (Mathlib has
  `convexHull`, `Convex.convexHull_eq_image`, and various
  Carathéodory-style results, but the colourful version may not be
  there off the shelf).
- If proof attempt is requested, a search for `colorful` /
  `Caratheodory` in Mathlib should be the first step.
