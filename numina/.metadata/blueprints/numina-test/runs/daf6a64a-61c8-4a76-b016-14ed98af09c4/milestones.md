# Run milestones — numina-test refinement

## Files processed
- numina/blueprints/numina-test/numina-test.tex (refined)
- numina/blueprints/numina-test/source/numina-test-source.tex (mirrored)

## Declarations now in blueprint
1. `def:laplacian` — Laplacian matrix L(G) = D(G) - A(G).
2. `def:algebraic_connectivity` — orders Laplacian eigenvalues; defines λ₂(G).
   Uses: `def:laplacian`.
3. `def:complete_bipartite` — K_{a,b} for a,b ≥ 1.
4. `lem:lambda2_k2_nm2` — λ₂(K_{2,n-2}) = 2 for n ≥ 4.
   Uses: `def:algebraic_connectivity`, `def:complete_bipartite`.
5. `conj:lambda2_bound_m_2nm2` — λ₂(G) ≤ 2 whenever |E(G)| = 2(n-2), n ≥ 4.
   Uses: `def:algebraic_connectivity`.
6. `thm:k2nminus2_maximizer` — K_{2,n-2} is a maximizer (conditional on the
   conjecture). Uses: `def:algebraic_connectivity`, `def:complete_bipartite`,
   `lem:lambda2_k2_nm2`, `conj:lambda2_bound_m_2nm2`.

## What was changed
- Replaced informal `\paragraph{Notation.}` and `\paragraph{Complete bipartite graph.}`
  with `\begin{definition}` blocks that have stable `\label`s.
- Promoted the algebraic-connectivity definition out of the notation block so
  it can be referenced individually.
- Split the original conjecture (which mixed three claims: an inequality, a
  computation, and a maximizer corollary) into:
  - `lem:lambda2_k2_nm2` (computation),
  - `conj:lambda2_bound_m_2nm2` (the actual unproved bound),
  - `thm:k2nminus2_maximizer` (corollary that combines the two).
- Added `\uses{...}` dependencies between every node, so the leanblueprint
  dependency graph is well-formed.

## Next steps (not yet executed; awaiting user)
- Run `leanblueprint` (or `mcp__blueprint-tools__initialize_blueprint_metadata`)
  to register the new declarations in `blueprint.json`.
- Once Lean environment is ready, formalize each declaration in turn:
  Laplacian → algebraic connectivity → K_{a,b} → lemma → theorem (the
  conjecture itself is left unproven by design).
- Decide whether to keep `conj:lambda2_bound_m_2nm2` as a conjecture or
  upgrade to `theorem` if a proof becomes available.

## Open review points
- Definition of K_{a,b} requires a,b ≥ 1; the lemma/theorem use n ≥ 4 so
  that n-2 ≥ 2 ≥ 1, which is consistent.
- `blueprint.json` currently has empty `entries` — refresh metadata after
  build environment is ready.
