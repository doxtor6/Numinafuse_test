import NuminafuseTest.Blueprint

open scoped RealInnerProductSpace

namespace NuminafuseTest.Blueprint

theorem mainTheorem' (d : ℕ)
    (C : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)))
    (hC : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (C i)) :
    ∃ p : Fin (d + 1) → EuclideanSpace ℝ (Fin d),
      (∀ i, p i ∈ C i) ∧ (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (Set.range p) := by
  obtain ⟨T, hT_sub, hT_fin, hT_zero⟩ := finite_reduction C hC
  have hT_ne : ∀ i, (T i).Nonempty := by
    intro i
    rcases Set.eq_empty_or_nonempty (T i) with hempty | hne
    · exfalso
      have h0 := hT_zero i
      rw [hempty, convexHull_empty] at h0
      exact h0.elim
    · exact hne
  obtain ⟨pStar, qStar, hpStar_mem, hqStar_in, hqStar_min⟩ :=
    exists_min_rainbow T hT_fin hT_ne
  have hqStar_zero : qStar = 0 := by
    by_contra hqStar_ne
    have hkkt_set : ∀ s ∈ Set.range pStar, ⟪qStar, qStar⟫ ≤ ⟪qStar, s⟫ :=
      kkt_inner_ge (Set.range pStar) (Set.finite_range pStar) qStar hqStar_in
        (fun x hx => hqStar_min pStar hpStar_mem x hx)
    have hkkt : ∀ j, ⟪qStar, qStar⟫ ≤ ⟪qStar, pStar j⟫ := fun j =>
      hkkt_set (pStar j) ⟨j, rfl⟩
    obtain ⟨p', q', hp'_mem, hq'_in, hq'_lt⟩ :=
      strict_improvement T hT_fin hT_zero pStar hpStar_mem qStar hqStar_in hqStar_ne hkkt
    have hge : ‖qStar‖ ≤ ‖q'‖ := hqStar_min p' hp'_mem q' hq'_in
    linarith
  refine ⟨pStar, fun i => hT_sub i (hpStar_mem i), ?_⟩
  rw [← hqStar_zero]
  exact hqStar_in

end NuminafuseTest.Blueprint
