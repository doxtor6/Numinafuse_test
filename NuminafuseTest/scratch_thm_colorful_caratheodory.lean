/-
Scratch attempt at Colorful Caratheodory (Bárány 1982).
-/
import Mathlib

namespace NuminafuseTest.Blueprint

open scoped InnerProductSpace
open Set Finset

/-- Reduction: if `0 ∈ conv(C_i)` for each color `i`, there exist finite subsets
`T_i ⊆ C_i` with `0 ∈ conv(T_i)`. -/
lemma exists_finite_subsets {d : ℕ}
    (C : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)))
    (hC : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (C i)) :
    ∃ T : Fin (d + 1) → Finset (EuclideanSpace ℝ (Fin d)),
      (∀ i, (T i : Set _) ⊆ C i) ∧
      (∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ ((T i) : Set _)) := by
  classical
  choose T hsub h0 using fun i => by
    have h := hC i
    rw [convexHull_eq_union_convexHull_finite_subsets] at h
    simp only [Set.mem_iUnion, exists_prop] at h
    exact h
  exact ⟨T, hsub, h0⟩

theorem MainTheorem (d : ℕ)
    (C : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)))
    (hC : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (C i)) :
    ∃ p : Fin (d + 1) → EuclideanSpace ℝ (Fin d),
      (∀ i, p i ∈ C i) ∧ (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (Set.range p) := by
    sorry

end NuminafuseTest.Blueprint
