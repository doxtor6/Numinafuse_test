# Run milestones — numina-test (de Bruijn--Erdős proof attempt)

## Scope
Formalize and prove the de Bruijn--Erdős theorem for graph k-colorability:
if every finite subgraph of a simple graph G is k-colorable, then G itself
is k-colorable.

## Result
Both Lean declarations are closed and sorry-free; build is clean.

## Mathlib leverage
- `SimpleGraph.Coloring α G := G →g completeGraph α` (id 185459).
- `SimpleGraph.Colorable n G := Nonempty (G.Coloring (Fin n))` (id 185476).
- `SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom` (id 186535) —
  Mathlib's de Bruijn--Erdős for graph homomorphisms; specialized to
  `F := SimpleGraph.completeGraph (Fin k)` to obtain colorability.

## Files written
- `NuminafuseTest/Blueprint.lean`: rewritten to contain
  - `abbrev KColoring G k := G.Coloring (Fin k)`
  - `theorem deBruijnErdos` with full proof (no sorry).
- `numina/blueprints/numina-test/numina-test.tex`: updated by
  `mark_declaration_proved` to carry `\lean{...}`, `\leanfile{...}`,
  `\leanok` for `def:k_coloring` and `thm:de_bruijn_erdos`.
- `numina/blueprints/numina-test/source/numina-test-source.tex`:
  manually mirrored the `\lean{...}`, `\leanfile{...}`, `\leanok` tags.

## Build verification
- `mcp__lean-lsp__lean_diagnostic_messages` on
  `NuminafuseTest/Blueprint.lean` → success, 0 items.
- One iteration of `Unknown identifier 'completeGraph'` was fixed by
  qualifying as `SimpleGraph.completeGraph`.

## Declaration status
- `def:k_coloring` → `proved`, leanDeclaration
  `NuminafuseTest.Blueprint.KColoring`.
- `thm:de_bruijn_erdos` → `proved`, leanDeclaration
  `NuminafuseTest.Blueprint.deBruijnErdos`.
- `def:finite_subgraph` left without a Lean linkage: the formal
  statement uses `G.Subgraph` plus `verts.Finite` directly (the
  blueprint's "finite induced subgraph" is realized inline rather than
  as a single named declaration). Status unchanged.

## Notes for future work
- The proof goes via graph homomorphisms: `Coloring (Fin k)` is by
  definition `G →g completeGraph (Fin k)`, so a colorability hypothesis
  unwraps with `.some` on each subgraph and feeds straight into
  `nonempty_hom_of_forall_finite_subgraph_hom`. No compactness or
  ultrafilter machinery had to be re-developed.
- If the user later wants `def:finite_subgraph` to point at a concrete
  Lean term, two natural choices are `SimpleGraph.Subgraph.coe` (used
  in the proof) or `SimpleGraph.induce` on a `Set V`. Either would
  match the blueprint description.
