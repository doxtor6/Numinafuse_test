# Run milestones — numina-test

## Files processed
- numina/blueprints/numina-test/numina-test.tex (refined into proper leanblueprint format)
- numina/blueprints/numina-test/source/numina-test-source.tex (mirrored)
- NuminafuseTest/Blueprint.lean (created; six stubs)
- NuminafuseTest.lean (added `import NuminafuseTest.Blueprint`)

## Declarations and current status

| Label                          | Lean name                                              | Status      | Body                          |
| ------------------------------ | ------------------------------------------------------ | ----------- | ----------------------------- |
| `def:laplacian`                | `NuminafuseTest.Blueprint.laplacian`                   | proved      | wraps `SimpleGraph.lapMatrix ℝ` |
| `def:algebraic_connectivity`   | `NuminafuseTest.Blueprint.algebraicConnectivity`       | in_progress | concrete (sorry-free), see below |
| `def:complete_bipartite`       | `NuminafuseTest.Blueprint.completeBipartite`           | proved      | wraps `completeBipartiteGraph (Fin a) (Fin b)` |
| `lem:lambda2_k2_nm2`           | `NuminafuseTest.Blueprint.lambda2_K2_nm2`              | in_progress | `sorry` (attempted, deferred — see below) |
| `thm:lambda2_bound_m_2nm2`     | `NuminafuseTest.Blueprint.lambda2_bound_m_2nm2`        | in_progress | `sorry` (not attempted) |
| `thm:k2nminus2_maximizer`      | `NuminafuseTest.Blueprint.k2nminus2_maximizer`         | proved      | one-liner: `h2 ▸ h1` from the two upstream lemmas as black boxes |

`def:algebraic_connectivity` definition body (sorry-free, but status is still
`in_progress` because its blueprint dependents are unproved):

```lean
noncomputable def algebraicConnectivity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  let h : (G.lapMatrix ℝ).IsHermitian := G.isHermitian_lapMatrix (R := ℝ)
  let eigs : V → ℝ := h.eigenvalues
  let s : List ℝ := ((Finset.univ : Finset V).val.map eigs).sort (· ≤ ·)
  s.getD 1 0
```

## What was changed in the blueprint LaTeX
- Replaced informal `\paragraph{Notation.}` and `\paragraph{Complete bipartite graph.}`
  with `\begin{definition}` blocks that have stable `\label`s.
- Promoted algebraic-connectivity out of the notation block.
- Split the original single conjecture (which mixed three claims) into:
  - `lem:lambda2_k2_nm2` (the computation),
  - `thm:lambda2_bound_m_2nm2` (the bound; was `conj:` but renamed to
    `thm:` because the leanblueprint parser does not recognize the
    `conjecture` environment),
  - `thm:k2nminus2_maximizer` (corollary).
- Added `\uses{...}` dependencies between all nodes.

## Build status
Module `NuminafuseTest.Blueprint` builds with `error_count = 0` and three
expected `sorry` warnings (lines 46, 52, 61 — `lambda2_K2_nm2`,
`lambda2_bound_m_2nm2`, `k2nminus2_maximizer`).

## Attempt log

### Attempt 1 — `lem:lambda2_k2_nm2`  (FAILED, deferred)
Sub-agent: `prompts:prover` (cap ~15 turns).
Outcome: file left in clean baseline state with `by sorry`; no scratch
file kept; no helper lemmas committed.

What was tried:
- `lean-explore` semantic searches for `eigenvalues lapMatrix
  completeBipartiteGraph`, `algebraic connectivity`, `spectrum
  Laplacian`, `lapMatrix eigenvalue eigenvector specific graph`,
  `List.sort getD eigenvalues`. No usable hits.

Blocker:
Mathlib has no spectrum results for any specific graph family
(complete bipartite, complete multipartite, etc.). To prove
`λ₂(K_{2, n-2}) = 2` exactly, one must:
1. Establish the full eigenvalue multiset of
   `lapMatrix (completeBipartite 2 (n-2))` as
   `{0, 2 (×(n-3)), n-2, n}`, and
2. Sort that multiset and project index 1.

Most promising entry point identified by the prover:
`Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀` —
relates the sorted eigenvalue list to the sorted roots of the
characteristic polynomial. This would handle step 2 once step 1 is
done, but step 1 (computing the parametric characteristic polynomial)
has no shortcut and is itself a multi-day formalization (Schur-complement
block expansion or explicit eigenvector construction).

Suggested follow-up plan (multi-day, out of scope of one prover call):
1. Prove `lapMatrix_completeBipartite_charpoly`:
   `charpoly (lapMatrix (completeBipartite a b))
      = X * (X - (a+b)) * (X - a)^(b-1) * (X - b)^(a-1)`.
   Likely route: block-matrix Schur complement, or direct eigenvector
   construction (constant-on-each-part vectors + zero-sum-within-part
   vectors).
2. Combine with `Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀`
   to translate to a sorted-eigenvalue identity.
3. Specialize to `a = 2, b = n - 2`, sort
   `{0, n, 2 (×(n-3)), n-2}`, take index 1.

Alternative if time-boxed: scope down to a fixed small `n` (e.g.
`n = 4`) where the matrix is 4×4 and `decide`-style or explicit
computation can apply.

### Attempts 2 and 3 — `thm:lambda2_bound_m_2nm2`, `thm:k2nminus2_maximizer`
Not attempted. The bound theorem is the genuinely hard part of the
original conjecture (it is the unproved bound itself); the maximizer
corollary is a short combination of `lem:lambda2_k2_nm2` and
`thm:lambda2_bound_m_2nm2` once both are available.

## Next actionable items
- Build out spectral infrastructure for `K_{a,b}` Laplacians (the
  multi-day plan above), then return to `lem:lambda2_k2_nm2`.
- Or, scope `lem:lambda2_k2_nm2` to a fixed small `n` and finish that case.
- `thm:lambda2_bound_m_2nm2` requires real research-level
  combinatorial-spectral input; not a near-term formalization target.

## Open review points
- `def:algebraic_connectivity` is sorry-free but still
  `status = in_progress`. The convention here is up to the user — could
  be marked `proved` since its body is concrete, but its dependents are
  unfinished.
- `NuminafuseTest/NuminaTest.lean` (pre-existing, identical-shape stubs
  under namespace `NuminafuseTest`) was left untouched. Down-stream
  cleanup may want to reconcile or delete it.
- Definition of `K_{a,b}` requires `a, b ≥ 1`; lemma/theorem use
  `n ≥ 4` so `n - 2 ≥ 2 ≥ 1` — consistent.
