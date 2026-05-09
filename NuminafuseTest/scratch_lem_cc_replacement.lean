/-
Bárány's Colorful Carathéodory theorem in `EuclideanSpace ℝ (Fin d)`.

Scratch file for proving `strict_improvement`.
-/
import Mathlib

open scoped RealInnerProductSpace

namespace NuminafuseTest.Blueprint

/-- **Finite reduction.** -/
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

theorem kkt_inner_ge {d : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Finite)
    (q : EuclideanSpace ℝ (Fin d)) (hq : q ∈ convexHull ℝ S)
    (hmin : ∀ x ∈ convexHull ℝ S, ‖q‖ ≤ ‖x‖) :
    ∀ s ∈ S, ⟪q, q⟫ ≤ ⟪q, s⟫ := by
  sorry

/-- **Strict improvement step.** -/
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
  classical
  -- Step 1: Carathéodory dimension reduction.
  -- Get a finset s ⊆ range p, affinely independent, with q ∈ conv s.
  set s : Finset (EuclideanSpace ℝ (Fin d)) :=
    Caratheodory.minCardFinsetOfMemConvexHull hq_mem with hs_def
  have hs_sub : (s : Set _) ⊆ Set.range p :=
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hq_mem
  have hq_s : q ∈ convexHull ℝ (s : Set _) :=
    Caratheodory.mem_minCardFinsetOfMemConvexHull hq_mem
  have hs_ai : AffineIndependent ℝ ((↑) : s → EuclideanSpace ℝ (Fin d)) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hq_mem
  -- Cardinality bound.
  have hs_card_le : s.card ≤ d + 1 := by
    have h := hs_ai.card_le_finrank_succ
    have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : s → EuclideanSpace ℝ (Fin d))))
        ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) :=
      Submodule.finrank_le _
    have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
    have hcard : Fintype.card s = s.card := Fintype.card_coe s
    omega
  -- Step 2: find an index i : Fin (d+1) with p i ∉ s (after some case work).
  have key : ∃ i : Fin (d + 1), q ∈ convexHull ℝ ((Set.range p) \ {p i}) := by
    -- Case A: |s| < d + 1.
    by_cases h_lt : s.card < d + 1
    · -- Pigeonhole: some i with p i ∉ s.
      have : ¬ (∀ i : Fin (d + 1), p i ∈ s) := by
        intro hall
        -- Then range p ⊆ s, but |range p| ≤ s.card < d+1, but range p has at most d+1 elts
        -- We need: range p ⊆ s implies surjection of Fin(d+1) → s, so s.card ≥ |range p|... that's not enough.
        -- Actually, if every p i ∈ s, then range p ⊆ s, so we'd have d+1 elements in s if p is injective... not needed.
        -- Wait, we want a contradiction. |s| < d+1 and we want some p i ∉ s.
        -- If all p i ∈ s, then range p ⊆ s as sets. We don't get contradiction from this.
        -- Different angle: we need to find i with p i ∉ s OR if all p i ∈ s, it's still fine
        -- because then s ⊇ range p so range p has ≤ s.card < d+1 elements, but Fin(d+1) is finite.
        -- We can still have all p i ∈ s; then... hmm we need a different argument.
        -- Actually, if all p i ∈ s, then conv(range p) ⊆ conv s, but we have q ∈ conv s already.
        -- Let me reconsider. We want some i with p i ∉ s. If all p i ∈ s, this fails.
        -- But |s| < d+1: this means s misses something. In the worst case, all p i are in s,
        -- but s has fewer than d+1 elements — so |range p| ≤ |s| < d+1, meaning p has duplicates.
        -- If p has duplicates, say p i = p j with i ≠ j, then we can replace p i with c.
        -- Hmm, actually we just need: ∃ i, q ∈ conv(range p \ {p i}).
        -- If p has a duplicate p i = p j (i ≠ j), then range p \ {p i} still contains all the same
        -- distinct values as range p (since p j is still there). So range p \ {p i} = range p \ ∅... no wait,
        -- range p \ {p i} just removes the element p i which equals p j. So range p \ {p i} = range p \ {p j}
        -- and range p \ {p i} could be a proper subset.
        -- Actually if p i = p j, then range p \ {p i} doesn't contain p i (= p j). Hmm.
        -- Let me think again. range p = {p 0, p 1, ..., p d}. If p i = p j with i ≠ j,
        -- range p \ {p i} = range p \ {p j} = {p k : k ≠ i, k ≠ j} ∪ ... no.
        -- range p \ {p i} = {x ∈ range p : x ≠ p i} = {p k : p k ≠ p i}.
        -- If p i = p j, then p j ∉ range p \ {p i}. So we lose p j too!
        -- So this duplicate case isn't helpful.
        -- BACK TO BASICS: we want q ∈ conv(range p') where p' i = c.
        -- range p' = {p' k : k} = (range p \ {p i if p i appears only at i}) ∪ {c}.
        -- More carefully: range p' = {p k : k ≠ i} ∪ {c}.
        -- So we need q ∈ conv({p k : k ≠ i} ∪ {c}).
        -- If we can show q ∈ conv({p k : k ≠ i}), great.
        -- So really we want: ∃ i, q ∈ conv({p k : k ≠ i}).
        sorry
      sorry
    · sorry
  sorry

end NuminafuseTest.Blueprint
