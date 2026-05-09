/-
Bárány's Colorful Carathéodory theorem in `EuclideanSpace ℝ (Fin d)`.

The proof is split into four helpers (finite reduction, existence of
a minimum-distance rainbow simplex, KKT optimality at the closest
point, and a vertex-replacement step that strictly decreases the
distance), assembled in `MainTheorem`.
-/
import Mathlib

open scoped RealInnerProductSpace

namespace NuminafuseTest.Blueprint

/-- **Finite reduction.** If the origin is in the convex hull of each
colour class `C i`, then the origin is already in the convex hull of a
finite subset `T i ⊆ C i`. -/
theorem finite_reduction {d : ℕ}
    (C : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)))
    (hC : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (C i)) :
    ∃ T : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)),
      (∀ i, T i ⊆ C i) ∧ (∀ i, (T i).Finite) ∧
      (∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (T i)) := by
  classical
  refine ⟨fun i => (Caratheodory.minCardFinsetOfMemConvexHull (hC i) : Set _),
    fun i => ?_, fun i => ?_, fun i => ?_⟩
  · exact Caratheodory.minCardFinsetOfMemConvexHull_subseteq (hC i)
  · exact (Caratheodory.minCardFinsetOfMemConvexHull (hC i)).finite_toSet
  · exact Caratheodory.mem_minCardFinsetOfMemConvexHull (hC i)

/-- **Existence of a distance-minimising rainbow simplex.** Given
finitely many nonempty colour classes, the infimum of `‖q‖` over all
points `q` lying in the convex hull of some compatible rainbow tuple
is attained. -/
theorem exists_min_rainbow {d : ℕ}
    (T : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)))
    (hT_fin : ∀ i, (T i).Finite) (hT_ne : ∀ i, (T i).Nonempty) :
    ∃ (p : Fin (d + 1) → EuclideanSpace ℝ (Fin d))
      (q : EuclideanSpace ℝ (Fin d)),
      (∀ i, p i ∈ T i) ∧ q ∈ convexHull ℝ (Set.range p) ∧
      ∀ (p' : Fin (d + 1) → EuclideanSpace ℝ (Fin d)),
        (∀ i, p' i ∈ T i) →
        ∀ q' ∈ convexHull ℝ (Set.range p'), ‖q‖ ≤ ‖q'‖ := by
  sorry

/-- **KKT optimality at the closest point.** If `q` minimises `‖x‖`
on the convex hull of a finite set `S` and lies in that hull, then
`⟪q, q⟫ ≤ ⟪q, s⟫` for every `s ∈ S`. -/
theorem kkt_inner_ge {d : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Finite)
    (q : EuclideanSpace ℝ (Fin d)) (hq : q ∈ convexHull ℝ S)
    (hmin : ∀ x ∈ convexHull ℝ S, ‖q‖ ≤ ‖x‖) :
    ∀ s ∈ S, ⟪q, q⟫ ≤ ⟪q, s⟫ := by
  sorry

/-- **Vertex replacement decreases the distance.** Given a rainbow
tuple `p` and a point `q` in its convex hull with `q ≠ 0` satisfying
the KKT condition `⟪q, q⟫ ≤ ⟪q, p j⟫` for every `j`, swapping any
single vertex `p i` for a point `c` with `⟪q, c⟫ ≤ 0` yields a new
rainbow tuple whose convex hull contains a point strictly closer to
the origin than `q`. -/
theorem replacement_strictly_closer {d : ℕ}
    (p : Fin (d + 1) → EuclideanSpace ℝ (Fin d))
    (q : EuclideanSpace ℝ (Fin d))
    (hq_mem : q ∈ convexHull ℝ (Set.range p))
    (hq_ne : q ≠ 0)
    (hkkt : ∀ j, ⟪q, q⟫ ≤ ⟪q, p j⟫)
    (i : Fin (d + 1))
    (c : EuclideanSpace ℝ (Fin d))
    (hc : ⟪q, c⟫ ≤ 0) :
    ∃ q' ∈ convexHull ℝ (Set.range (Function.update p i c)), ‖q'‖ < ‖q‖ := by
  sorry

/-- **Bárány's Colorful Carathéodory theorem (1982).** Given `d + 1`
subsets `C 0, …, C d` of the Euclidean space `ℝ^d` each containing the
origin in its convex hull, there is a "rainbow" choice `p i ∈ C i`
whose convex hull also contains the origin. -/
theorem MainTheorem (d : ℕ)
    (C : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)))
    (hC : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (C i)) :
    ∃ p : Fin (d + 1) → EuclideanSpace ℝ (Fin d),
      (∀ i, p i ∈ C i) ∧ (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (Set.range p) := by
    sorry

end NuminafuseTest.Blueprint
