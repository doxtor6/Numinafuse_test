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
  classical
  -- Finset of compatible tuples.
  let tF : ∀ i, Finset (EuclideanSpace ℝ (Fin d)) := fun i => (hT_fin i).toFinset
  let S : Finset (Fin (d + 1) → EuclideanSpace ℝ (Fin d)) := Fintype.piFinset tF
  have hS_ne : S.Nonempty := by
    rw [Fintype.piFinset_nonempty]
    intro i
    exact (Set.Finite.toFinset_nonempty _).mpr (hT_ne i)
  have hmem_S : ∀ p, p ∈ S ↔ ∀ i, p i ∈ T i := by
    intro p
    simp [S, tF, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
  -- For each compatible tuple p, range p is finite, hull is compact.
  have hRange_fin : ∀ p : Fin (d + 1) → EuclideanSpace ℝ (Fin d),
      (Set.range p).Finite := by
    intro p
    exact Set.finite_range p
  have hHull_compact : ∀ p : Fin (d + 1) → EuclideanSpace ℝ (Fin d),
      IsCompact (convexHull ℝ (Set.range p)) := by
    intro p
    set_option synthInstance.maxHeartbeats 80000 in
    exact Set.Finite.isCompact_convexHull ℝ (hRange_fin p)
  have hHull_ne : ∀ p : Fin (d + 1) → EuclideanSpace ℝ (Fin d),
      (convexHull ℝ (Set.range p)).Nonempty := by
    intro p
    exact (Set.range_nonempty p).convexHull
  -- For each p, choose q minimizing the norm on the hull.
  have hMinExists : ∀ p : Fin (d + 1) → EuclideanSpace ℝ (Fin d),
      ∃ q ∈ convexHull ℝ (Set.range p),
        ∀ x ∈ convexHull ℝ (Set.range p), ‖q‖ ≤ ‖x‖ := by
    intro p
    obtain ⟨q, hq_mem, hq_min⟩ :=
      (hHull_compact p).exists_isMinOn (hHull_ne p)
        (continuous_norm.continuousOn)
    exact ⟨q, hq_mem, hq_min⟩
  -- Pick such a q for each p.
  let qOf : (Fin (d + 1) → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) :=
    fun p => Classical.choose (hMinExists p)
  have qOf_mem : ∀ p, qOf p ∈ convexHull ℝ (Set.range p) := fun p =>
    (Classical.choose_spec (hMinExists p)).1
  have qOf_min : ∀ p, ∀ x ∈ convexHull ℝ (Set.range p), ‖qOf p‖ ≤ ‖x‖ := fun p =>
    (Classical.choose_spec (hMinExists p)).2
  -- Now minimize ‖qOf p‖ over p ∈ S.
  obtain ⟨p_star, hp_star_S, hp_star_min⟩ :=
    S.exists_min_image (fun p => ‖qOf p‖) hS_ne
  refine ⟨p_star, qOf p_star, ?_, qOf_mem p_star, ?_⟩
  · exact (hmem_S p_star).mp hp_star_S
  · intro p' hp' q' hq'
    have hp'_S : p' ∈ S := (hmem_S p').mpr hp'
    calc ‖qOf p_star‖ ≤ ‖qOf p'‖ := hp_star_min p' hp'_S
      _ ≤ ‖q'‖ := qOf_min p' q' hq'

/-- **KKT optimality at the closest point.** If `q` minimises `‖x‖`
on the convex hull of a finite set `S` and lies in that hull, then
`⟪q, q⟫ ≤ ⟪q, s⟫` for every `s ∈ S`. -/
theorem kkt_inner_ge {d : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Finite)
    (q : EuclideanSpace ℝ (Fin d)) (hq : q ∈ convexHull ℝ S)
    (hmin : ∀ x ∈ convexHull ℝ S, ‖q‖ ≤ ‖x‖) :
    ∀ s ∈ S, ⟪q, q⟫ ≤ ⟪q, s⟫ := by
  set K : Set (EuclideanSpace ℝ (Fin d)) := convexHull ℝ S
  have hK : Convex ℝ K := convex_convexHull ℝ S
  have hnorm : (‖(0 : EuclideanSpace ℝ (Fin d)) - q‖ =
      ⨅ w : K, ‖(0 : EuclideanSpace ℝ (Fin d)) - w‖) := by
    have hbdd : BddBelow (Set.range
        (fun w : K => ‖(0 : EuclideanSpace ℝ (Fin d)) - w‖)) :=
      ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
    have hne : Nonempty K := ⟨⟨q, hq⟩⟩
    apply le_antisymm
    · refine le_ciInf ?_
      intro w
      have : ‖q‖ ≤ ‖(w : EuclideanSpace ℝ (Fin d))‖ := hmin _ w.2
      simpa [zero_sub, norm_neg] using this
    · refine ciInf_le_of_le hbdd ⟨q, hq⟩ ?_
      simp
  have hkey :=
    (norm_eq_iInf_iff_real_inner_le_zero (F := EuclideanSpace ℝ (Fin d)) hK hq).1 hnorm
  intro s hs
  have hsK : s ∈ K := subset_convexHull ℝ S hs
  have h := hkey s hsK
  have h1 : ⟪(0 : EuclideanSpace ℝ (Fin d)) - q, s - q⟫ = -(⟪q, s⟫ - ⟪q, q⟫) := by
    rw [zero_sub, inner_neg_left, inner_sub_right]
  rw [h1] at h
  linarith

/-- **Strict improvement step (Bárány).** Given a family of finite
colour classes `T i` each containing the origin in its convex hull,
a compatible rainbow tuple `p` (with `p i ∈ T i`), and a point `q`
in its convex hull with `q ≠ 0` satisfying the KKT condition
`⟪q, q⟫ ≤ ⟪q, p j⟫` for every `j`, there exists a new compatible
rainbow tuple `p'` whose convex hull contains a point strictly
closer to the origin than `q`. The proof finds an index `i` and a
point `c ∈ T i` with `⟪q, c⟫ ≤ 0` (extracted from the convex
combination expressing `0 ∈ conv (T i)`), and combines this with
the KKT inequality and Carathéodory's theorem on the augmented
`d + 2`-point hull. -/
theorem strict_improvement {d : ℕ}
    (T : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)))
    (hT_fin : ∀ i, (T i).Finite)
    (hT_zero : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (T i))
    (p : Fin (d + 1) → EuclideanSpace ℝ (Fin d))
    (hp : ∀ i, p i ∈ T i)
    (q : EuclideanSpace ℝ (Fin d))
    (hq_mem : q ∈ convexHull ℝ (Set.range p))
    (hq_ne : q ≠ 0)
    (hkkt : ∀ j, ⟪q, q⟫ ≤ ⟪q, p j⟫) :
    ∃ (p' : Fin (d + 1) → EuclideanSpace ℝ (Fin d))
      (q' : EuclideanSpace ℝ (Fin d)),
      (∀ i, p' i ∈ T i) ∧ q' ∈ convexHull ℝ (Set.range p') ∧ ‖q'‖ < ‖q‖ := by
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
