/-
Stubs for the `numina-test` blueprint: algebraic connectivity of complete
bipartite graphs.  Statements only — all bodies are `sorry`.
-/
import Mathlib

open scoped BigOperators

namespace NuminafuseTest.Blueprint

/-- Laplacian matrix `L(G) = D(G) - A(G)` of a simple graph `G` on a finite
vertex type, valued in `ℝ`.  This is just `SimpleGraph.lapMatrix` specialized
to `ℝ`. -/
noncomputable def laplacian {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  G.lapMatrix ℝ

/-- The algebraic connectivity `λ₂(G)` of a simple graph `G` on a finite
vertex type: the second-smallest eigenvalue of the Laplacian `L(G)`,
indexed so that `0 = λ₁(G) ≤ λ₂(G) ≤ ⋯ ≤ λₙ(G)`.

The Laplacian is real symmetric and positive semidefinite, so its
eigenvalues are real and nonnegative.  This stub returns a real number;
the exact construction (sorting the eigenvalues and selecting the second
smallest) is left as `sorry`. -/
noncomputable def algebraicConnectivity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  let h : (G.lapMatrix ℝ).IsHermitian := G.isHermitian_lapMatrix (R := ℝ)
  let eigs : V → ℝ := h.eigenvalues
  let s : List ℝ := ((Finset.univ : Finset V).val.map eigs).sort (· ≤ ·)
  s.getD 1 0

/-- The complete bipartite graph `K_{a,b}` on the vertex type
`Fin a ⊕ Fin b`. -/
def completeBipartite (a b : ℕ) : SimpleGraph (Fin a ⊕ Fin b) :=
  completeBipartiteGraph (Fin a) (Fin b)

instance completeBipartite.decidableAdj (a b : ℕ) :
    DecidableRel (completeBipartite a b).Adj := by
  intro u v
  unfold completeBipartite
  cases u <;> cases v <;> simp <;> infer_instance

/-- Piece 1 — sort/multiset bridge (sorry-free helper, useful for the eventual proof).

If two functions `f g : V → ℝ` produce the same multiset of values on
`Finset.univ`, they have the same sorted list. -/
private lemma sort_map_eq_of_multiset_eq {V : Type*} [Fintype V]
    (f g : V → ℝ)
    (h : ((Finset.univ : Finset V).val.map f) = ((Finset.univ : Finset V).val.map g)) :
    (((Finset.univ : Finset V).val.map f).sort (· ≤ ·) =
        ((Finset.univ : Finset V).val.map g).sort (· ≤ ·)) := by
  rw [h]

/-- Variant of Piece 1: if eigenvalues equal a function up to permutation, sort is preserved.
This is the bridge from the conclusion of
`Matrix.IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal`
to the sorted eigenvalue list used in `algebraicConnectivity`. -/
private lemma sort_eigenvalues_eq_sort_of_perm {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℝ} (hA : A.IsHermitian)
    {f : V → ℝ} (σ : V ≃ V) (hσ : hA.eigenvalues ∘ σ = f) :
    ((Finset.univ : Finset V).val.map hA.eigenvalues).sort (· ≤ ·)
      = ((Finset.univ : Finset V).val.map f).sort (· ≤ ·) := by
  apply sort_map_eq_of_multiset_eq
  have h1 : (Finset.univ : Finset V).val.map (hA.eigenvalues ∘ σ) =
      (Finset.univ : Finset V).val.map hA.eigenvalues := by
    rw [show (hA.eigenvalues ∘ σ) = (hA.eigenvalues ∘ (σ : V → V)) from rfl]
    rw [← Multiset.map_map]
    congr 1
    exact Multiset.map_univ_val_equiv σ
  rw [← hσ, h1]

/-- For every integer `n ≥ 4`, the algebraic connectivity of `K_{2, n-2}`
equals `2`. -/
theorem lambda2_K2_nm2 (n : ℕ) (hn : 4 ≤ n) :
    algebraicConnectivity (completeBipartite 2 (n - 2)) = 2 := by
  sorry

/-- Edge-count bound on algebraic connectivity: if `G` is a simple graph on
`n ≥ 4` vertices with exactly `2(n-2)` edges, then `λ₂(G) ≤ 2`. -/
theorem lambda2_bound_m_2nm2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 4 ≤ Fintype.card V)
    (hE : G.edgeFinset.card = 2 * (Fintype.card V - 2)) :
    algebraicConnectivity G ≤ 2 := by
  sorry

/-- `K_{2, n-2}` maximizes algebraic connectivity among simple graphs on
`n ≥ 4` vertices with exactly `2(n-2)` edges. -/
theorem k2nminus2_maximizer {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 4 ≤ Fintype.card V)
    (hE : G.edgeFinset.card = 2 * (Fintype.card V - 2)) :
    algebraicConnectivity G ≤
      algebraicConnectivity (completeBipartite 2 (Fintype.card V - 2)) := by
  have h1 : algebraicConnectivity G ≤ 2 := lambda2_bound_m_2nm2 G hn hE
  have h2 : algebraicConnectivity (completeBipartite 2 (Fintype.card V - 2)) = 2 :=
    lambda2_K2_nm2 (Fintype.card V) hn
  exact h2 ▸ h1

end NuminafuseTest.Blueprint
