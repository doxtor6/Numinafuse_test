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

### Attempt 2 — `lem:lambda2_k2_nm2`  (FAILED, deferred again)
Sub-agent: `prompts:prover` (cap ~12 turns; search-only, no edits committed).
Outcome: file unchanged; clean failure with concrete Mathlib survey.

Mathlib API confirmed (none usable for this lemma):
- `Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff` — needs equal `charpoly`s.
- `Matrix.IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal` —
  gives only an existence-of-permutation, not an ordered identification.
- `Matrix.IsHermitian.charpoly_eq` — wrong direction
  (`charpoly = ∏ (X - eigenvalues i)`, doesn't help us go from a
  target charpoly back to ordered eigenvalues).
- `Matrix.IsHermitian.eigenvalues₀_antitone` — eigenvalues are
  monotone in the index, but doesn't connect to the value-sorted
  `List.sort (· ≤ ·)` used by `algebraicConnectivity`.
- `Matrix.charpoly_diagonal`,
  `Matrix.charpoly_fromBlocks_zero₁₂` / `zero₂₁`,
  `Matrix.BlockTriangular.charpoly` — nothing computes the charpoly
  of a specific bipartite Laplacian.
- No `algebraicConnectivity` definition or related theorem exists in
  Mathlib at all.

The unordered-spectrum vs sorted-list mismatch is the real obstacle:
even a clean explicit eigenbasis only delivers an *unordered* multiset
equality `Finset.univ.val.map hA.eigenvalues = {0, 2 (×(n-3)), n-2, n}`,
and one still needs a separate lemma to translate that to
`((Finset.univ.val.map eigs).sort (· ≤ ·)).getD 1 0 = 2`. That
translation lemma also does not exist in Mathlib.

### Suggested rescopings (not yet decided by user)
1. **Rephrase via unordered spectrum.** Change the blueprint
   statement from "λ₂ = 2" (defined via sorted list, index 1) to
   something like "the eigenvalue multiset of `lapMatrix
   (completeBipartite 2 (n-2))` is `{0, 2 (×(n-3)), n-2, n}`". This
   skips the sort/getD step entirely and is provable directly from an
   explicit eigenbasis. Loses the "second-smallest = 2" framing but
   is mathematically equivalent.
2. **Build the missing infrastructure.** Add two helper lemmas:
   - `Matrix.IsHermitian.eigenvalues_multiset_eq_of_orthonormal_eigenbasis`
     identifying `Finset.univ.val.map hA.eigenvalues` from an
     explicit eigenbasis.
   - `algebraicConnectivity_eq_of_eigenvalues_multiset_eq` connecting
     the multiset spectrum to `s.getD 1 0` for the sorted list.
   Then prove `K_{a,b}` charpoly or eigenbasis. Estimated multi-day.
3. **Drop `lem:lambda2_k2_nm2` from the blueprint** and merge its
   content into `thm:k2nminus2_maximizer` as a single conjectural
   theorem (defeats the point of the refinement, but unblocks).

### Attempt 3 — `thm:lambda2_bound_m_2nm2`
Not attempted. This is the original conjecture — research-level
combinatorial-spectral content. Not a target for a prover subagent.

### Attempt 4 — `thm:k2nminus2_maximizer`  (PROVED)
Manually closed in three lines: combine the two upstream sorry'd
lemmas as black boxes (`λ₂(G) ≤ 2 = λ₂(K_{2,n-2})`). The corollary's
own body is sorry-free; the upstream sorries still attach to
`lambda2_K2_nm2` and `lambda2_bound_m_2nm2` only.

### Attempt 5 — `lem:lambda2_k2_nm2`  (FAILED, deferred)
Sub-agent: `prompts:prover` (cap ~12 turns; user-supplied informal
proof now in the blueprint as roadmap). Outcome: file unchanged.

Refined Mathlib survey (more specific than attempts 1-2):
- `Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀` (id 131121)
  exists but sorts charpoly roots in DESCENDING order, equating with
  `List.ofFn hA.eigenvalues₀`.
- `Matrix.IsHermitian.eigenvalues₀_antitone` is monotone in the index,
  not in value.
- `List.Perm.eq_of_sortedLE` (id 201659) and `List.SortedLE.reverse`
  (id 201623) are the assembly pieces for a sort/getD bridge lemma.
- `Matrix.IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal`
  (id 379568) provides only `∃ σ, eigenvalues ∘ σ = f` — unordered.

Concrete decomposition for a future formalization PR:

  (i) Sort/getD bridge — likely ~40 lines, *not* multi-day:
      `IsHermitian.sort_eigenvalues_ascending_eq :
       (Finset.univ.val.map hA.eigenvalues).sort (· ≤ ·)
         = (List.ofFn hA.eigenvalues₀).reverse`
      via `sort_roots_charpoly_eq_eigenvalues₀` + permutation +
      `Perm.eq_of_sortedLE`.

  (ii) Spectrum identification for K_{2,m}'s Laplacian — *this* is
       the multi-day piece (~150-300 lines), due to the need for an
       explicit orthonormal basis of `{y ∈ ℝ^m : Σ y_i = 0}` (Helmert
       or Gram-Schmidt over `EuclideanSpace.basisFun`), then a
       `Matrix.IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal`
       application.
       Alternative: charpoly via Schur-complement block determinant of
       `[[m·I_2, -J_{2,m}], [-J_{m,2}, 2·I_m]]`. Mathlib has the block
       determinant API (`Matrix.det_fromBlocks_zero₁₂`/`zero₂₁` and the
       Schur complement form) but no specialization for this matrix.

  (iii) Final wrapper for `lambda2_K2_nm2` — ~30 lines combining (i)
        and (ii) plus an arithmetic case-split showing the
        second-smallest of `{0, 2 (×(m-1)), m, m+2}` is `2` for
        `m ≥ 2`.

So the previous "multi-day" estimate stands, but the bottleneck is now
specifically (ii). (i) is a self-contained ~40-line lemma worth
landing into a Mathlib branch independently.

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
