# Run milestones — numina-test (de Bruijn--Erdős refinement)

## Scope
Refine the new blueprint problem (de Bruijn--Erdős theorem) into proper
leanblueprint format. Refinement only — no formalization or proving was
requested.

## Files processed
- numina/blueprints/numina-test/numina-test.tex (rewritten)
- numina/blueprints/numina-test/source/numina-test-source.tex (mirrored)

## Declarations registered
- `def:k_coloring` — k-coloring of a graph.
- `def:finite_subgraph` — finite induced subgraph on a finite vertex set.
- `thm:de_bruijn_erdos` — main theorem; `\uses{def:k_coloring,
  def:finite_subgraph}`.

The previous algebraic-connectivity declarations (def:laplacian,
def:algebraic_connectivity, def:complete_bipartite, lem:lambda2_k2_nm2,
thm:lambda2_bound_m_2nm2, thm:k2nminus2_maximizer) are no longer in the
blueprint LaTeX and were removed from `blueprint.json` /
`declarations/` by the metadata refresh.

## What was changed
- Replaced the bare `\begin{theorem}...\end{theorem}` (no document
  wrapper, no labels, no prerequisite definitions) with:
  - Document wrapper.
  - Two prerequisite `\begin{definition}` blocks with stable labels
    (`def:k_coloring`, `def:finite_subgraph`).
  - Theorem environment with `\label{thm:de_bruijn_erdos}` and
    `\uses{def:k_coloring, def:finite_subgraph}`.
- The k-coloring definition explicitly states the proper-coloring
  constraint (`c(u) ≠ c(v)` for adjacent `u, v`) so that the theorem's
  hypothesis is unambiguous.
- The finite-subgraph definition uses the induced-subgraph convention
  (edge set restricted to the chosen finite vertex set), which is the
  standard interpretation in the de Bruijn--Erdős statement.

## Open considerations (not in the requested scope)
- The Lean file `NuminafuseTest/Blueprint.lean` still contains the
  earlier algebraic-connectivity stubs (laplacian, algebraicConnectivity,
  completeBipartite, lambda2_K2_nm2, lambda2_bound_m_2nm2,
  k2nminus2_maximizer) plus the two committed Piece-1 helper lemmas
  (sort_map_eq_of_multiset_eq, sort_eigenvalues_eq_sort_of_perm). These
  are now unreferenced by the blueprint. Left in place because the user
  has not asked for them to be removed; they may want to keep them or
  reuse pieces. Removing them would be a separate, explicit ask.
- `NuminafuseTest.lean` still imports `NuminafuseTest.Blueprint`. No
  build effect.

## Next actionable items (awaiting user direction)
- Decide whether to clear / replace `NuminafuseTest/Blueprint.lean` with
  fresh stubs for the new de Bruijn--Erdős declarations.
- Formalize `def:k_coloring`, `def:finite_subgraph`,
  `thm:de_bruijn_erdos` as Lean stubs (Mathlib has
  `SimpleGraph.Colorable` and `SimpleGraph.induce`, and likely a
  de Bruijn--Erdős statement somewhere — worth searching before
  re-stating).
- Attempt the proof (Mathlib provides
  `SimpleGraph.Colorable` and a compactness argument is available via
  `Filter.Ultrafilter` / `Pi.compactSpace` over a finite color set).
