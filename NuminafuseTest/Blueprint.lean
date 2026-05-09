/-
Formalization of the de Bruijn--Erdős theorem for graph `k`-colorability:
if every finite subgraph of a simple graph `G` is `k`-colorable, then `G`
itself is `k`-colorable. The proof specializes
`SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom` to homomorphisms
into the complete graph on `Fin k`.
-/
import Mathlib

namespace NuminafuseTest.Blueprint

/-- A `k`-coloring of a simple graph `G` is a graph homomorphism into the
complete graph on `Fin k`. Equivalently, a proper vertex coloring of `G`
using at most `k` colors. This is `SimpleGraph.Coloring G (Fin k)`. -/
abbrev KColoring {V : Type*} (G : SimpleGraph V) (k : ℕ) : Type _ :=
  G.Coloring (Fin k)

/-- **De Bruijn--Erdős theorem.** Let `G` be a simple graph (possibly on
an infinite vertex type) and `k ≥ 1`. If every finite subgraph of `G` is
`k`-colorable, then `G` itself is `k`-colorable. -/
theorem deBruijnErdos {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (h : ∀ G' : G.Subgraph, G'.verts.Finite → G'.coe.Colorable k) :
    G.Colorable k := by
  classical
  exact ⟨(G.nonempty_hom_of_forall_finite_subgraph_hom
      (F := SimpleGraph.completeGraph (Fin k))
      (fun G' hG' => (h G' hG').some)).some⟩

end NuminafuseTest.Blueprint
