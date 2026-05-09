/-
Scratch: prove `strict_improvement`.
-/
import Mathlib

open scoped RealInnerProductSpace

namespace NuminafuseTest.Blueprint

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
  -- Step 1: Get a Fin (d+1)-indexed convex combination representation of q.
  have hq_repr : ∃ λ : Fin (d + 1) → ℝ, (∀ j, 0 ≤ λ j) ∧ ∑ j, λ j = 1 ∧
      ∑ j, λ j • p j = q := by
    have h := mem_convexHull_iff_exists_fintype.mp hq_mem
    obtain ⟨ι, hι, w, z, hw0, hw1, hz, hsum⟩ := h
    -- z j ∈ range p, so for each j there exists k with z j = p k.
    -- Use choice to get k.
    have : ∀ j : ι, ∃ k : Fin (d + 1), p k = z j := by
      intro j
      obtain ⟨k, hk⟩ := hz j
      exact ⟨k, hk⟩
    choose σ hσ using this
    -- λ k = ∑_{j : σ j = k} w j
    refine ⟨fun k => ∑ j ∈ (Finset.univ : Finset ι).filter (fun j => σ j = k), w j,
      ?_, ?_, ?_⟩
    · intro k
      exact Finset.sum_nonneg (fun j _ => hw0 j)
    · rw [← hw1]
      rw [← Finset.sum_fiberwise (Finset.univ : Finset ι) σ w]
    · simp_rw [Finset.sum_smul]
      rw [← hsum]
      rw [show (∑ j, w j • z j) = ∑ k, ∑ j ∈ (Finset.univ : Finset ι).filter (fun j => σ j = k),
              w j • z j from ?_]
      · refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun j hj => ?_)
        simp [Finset.mem_filter] at hj
        rw [hj.2, hσ j]
      · exact (Finset.sum_fiberwise _ σ (fun j => w j • z j)).symm
  obtain ⟨lam, hlam0, hlam1, hlam_sum⟩ := hq_repr
  -- Step 2: Find an index i : Fin (d+1) with q ∈ conv({p k : k ≠ i}).
  -- Key fact: ‖q‖² = ∑ lam j ⟪q, p j⟫ ≥ ∑ lam j ‖q‖² = ‖q‖².
  -- Hence equality for j with lam_j > 0: ⟪q, p j⟫ = ‖q‖².
  have hqq : ⟪q, q⟫ = ∑ j, lam j * ⟪q, p j⟫ := by
    have : ⟪q, ∑ j, lam j • p j⟫ = ∑ j, lam j * ⟪q, p j⟫ := by
      rw [inner_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [real_inner_smul_right]
    rw [hlam_sum] at this
    exact this
  have hsum_eq : ∑ j, lam j * ⟪q, p j⟫ = ⟪q, q⟫ := hqq.symm
  -- Each summand: lam j * ⟪q, p j⟫ ≥ lam j * ⟪q, q⟫
  have hpoint : ∀ j, lam j * ⟪q, q⟫ ≤ lam j * ⟪q, p j⟫ := by
    intro j
    exact mul_le_mul_of_nonneg_left (hkkt j) (hlam0 j)
  have hsum_lower : ∑ j, lam j * ⟪q, q⟫ ≤ ∑ j, lam j * ⟪q, p j⟫ :=
    Finset.sum_le_sum (fun j _ => hpoint j)
  have hlhs : ∑ j, lam j * ⟪q, q⟫ = ⟪q, q⟫ := by
    rw [← Finset.sum_mul, hlam1, one_mul]
  -- The sums are actually equal.
  have hsum_eq2 : ∑ j, lam j * ⟪q, q⟫ = ∑ j, lam j * ⟪q, p j⟫ := by
    apply le_antisymm hsum_lower
    rw [hlhs, hsum_eq]
  -- For each j: lam j * ⟪q, q⟫ = lam j * ⟪q, p j⟫ (since pointwise inequality + equality of sums).
  have hpoint_eq : ∀ j, lam j * ⟪q, q⟫ = lam j * ⟪q, p j⟫ := by
    intro j
    by_contra h
    have hlt : lam j * ⟪q, q⟫ < lam j * ⟪q, p j⟫ := lt_of_le_of_ne (hpoint j) h
    have : ∑ k, lam k * ⟪q, q⟫ < ∑ k, lam k * ⟪q, p k⟫ :=
      Finset.sum_lt_sum (fun k _ => hpoint k) ⟨j, Finset.mem_univ _, hlt⟩
    linarith [hsum_eq2]
  -- Step 3: Find i with q ∈ conv({p k : k ≠ i}).
  -- Two cases: some lam i = 0, or all lam j > 0.
  have hexists_i : ∃ i : Fin (d + 1), q ∈ convexHull ℝ (p '' {j | j ≠ i}) := by
    by_cases hcase : ∃ i, lam i = 0
    · -- Case 1: some lam i = 0. Then q = ∑_{j ≠ i} lam j p j ∈ conv({p k : k ≠ i}).
      obtain ⟨i, hi0⟩ := hcase
      refine ⟨i, ?_⟩
      -- Use mem_convexHull_iff_exists_fintype with index type {j : Fin (d+1) // j ≠ i}.
      apply mem_convexHull_of_exists_fintype
        (ι := {j : Fin (d + 1) // j ≠ i})
        (w := fun j => lam j.val) (z := fun j => p j.val)
      · intro j; exact hlam0 j.val
      · -- ∑_{j ≠ i} lam j = 1
        have : ∑ j ∈ Finset.univ.filter (· ≠ i), lam j = 1 := by
          have hsplit : ∑ j, lam j = lam i + ∑ j ∈ Finset.univ.filter (· ≠ i), lam j := by
            rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· = i)]
            simp [Finset.filter_eq']
          rw [hi0, zero_add] at hsplit
          rw [← hsplit, hlam1]
        rw [Finset.sum_subtype _ (by simp : ∀ j, j ∈ Finset.univ.filter (· ≠ i) ↔ j ≠ i)]
        exact this
      · intro j; exact ⟨j.val, by simp [Set.mem_setOf_eq]; exact j.property⟩
      · -- ∑_{j ≠ i} lam j • p j = q
        have hsplit : ∑ j, lam j • p j =
            lam i • p i + ∑ j ∈ Finset.univ.filter (· ≠ i), lam j • p j := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· = i)]
          simp [Finset.filter_eq']
        rw [hi0, zero_smul, zero_add] at hsplit
        rw [Finset.sum_subtype _ (by simp : ∀ j, j ∈ Finset.univ.filter (· ≠ i) ↔ j ≠ i)]
        rw [← hsplit]; exact hlam_sum
    · -- Case 2: all lam j > 0. Then ⟪q, p j⟫ = ⟪q, q⟫ for all j.
      push_neg at hcase
      have hlam_pos : ∀ j, 0 < lam j := fun j => lt_of_le_of_ne (hlam0 j) (Ne.symm (hcase j))
      have hinner_eq : ∀ j, ⟪q, p j⟫ = ⟪q, q⟫ := by
        intro j
        have h := hpoint_eq j
        have : lam j * (⟪q, q⟫ - ⟪q, p j⟫) = 0 := by ring_nf; linarith
        have hne : lam j ≠ 0 := ne_of_gt (hlam_pos j)
        have : ⟪q, q⟫ - ⟪q, p j⟫ = 0 := by
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h hne
          · exact h
        linarith
      -- All p j lie on the hyperplane H = {x : ⟪q, x⟫ = ⟪q, q⟫}.
      -- Use Caratheodory finset s ⊆ range p ⊆ H, affinely independent.
      -- Then s ⊆ H, and dim(affineSpan s) ≤ dim(H) = d - 1, so s.card ≤ d.
      -- Hence ∃ i, p i ∉ s.
      have hq_mem' : q ∈ convexHull ℝ (Set.range p) := hq_mem
      set s : Finset (EuclideanSpace ℝ (Fin d)) :=
        Caratheodory.minCardFinsetOfMemConvexHull hq_mem' with hs_def
      have hs_sub : (s : Set _) ⊆ Set.range p :=
        Caratheodory.minCardFinsetOfMemConvexHull_subseteq hq_mem'
      have hq_s : q ∈ convexHull ℝ (s : Set _) :=
        Caratheodory.mem_minCardFinsetOfMemConvexHull hq_mem'
      have hs_ai : AffineIndependent ℝ ((↑) : s → EuclideanSpace ℝ (Fin d)) :=
        Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hq_mem'
      -- s ⊆ H: every x ∈ s has ⟪q, x⟫ = ⟪q, q⟫.
      have hs_in_H : ∀ x ∈ s, ⟪q, x⟫ = ⟪q, q⟫ := by
        intro x hx
        have : x ∈ Set.range p := hs_sub hx
        obtain ⟨k, hk⟩ := this
        rw [← hk]; exact hinner_eq k
      -- The hyperplane vectorSpan: q ⟂ (x - y) for x, y ∈ s.
      -- vectorSpan ℝ s ⊆ {v : ⟪q, v⟫ = 0} = (ℝ ∙ q)ᗮ.
      -- finrank((ℝ ∙ q)ᗮ) = d - 1 since q ≠ 0.
      have h_vspan_sub : vectorSpan ℝ (s : Set _) ≤ (ℝ ∙ q)ᗮ := by
        rw [vectorSpan_def]
        rw [Submodule.span_le]
        intro v hv
        simp only [Set.mem_image, Set.mem_sub] at hv
        obtain ⟨x, hx, y, hy, hv_eq⟩ := hv
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
        rw [← hv_eq, inner_sub_right]
        rw [hs_in_H x hx, hs_in_H y hy, sub_self]
      have h_finrank_perp : Module.finrank ℝ ((ℝ ∙ q)ᗮ) = d - 1 := by
        have : Module.finrank ℝ ((ℝ ∙ q)ᗮ) +
            Module.finrank ℝ (ℝ ∙ q) = d := by
          rw [add_comm]
          have := Submodule.finrank_add_finrank_orthogonalComplement_eq_finrank (K := ℝ)
            (V := EuclideanSpace ℝ (Fin d)) (W := ℝ ∙ q)
          rw [this]
          exact finrank_euclideanSpace_fin
        have hq_span : Module.finrank ℝ (ℝ ∙ q) = 1 := by
          rw [finrank_span_singleton hq_ne]
        omega
      have h_vspan_dim : Module.finrank ℝ (vectorSpan ℝ (s : Set _)) ≤ d - 1 := by
        calc Module.finrank ℝ (vectorSpan ℝ (s : Set _))
            ≤ Module.finrank ℝ ((ℝ ∙ q)ᗮ) := Submodule.finrank_mono h_vspan_sub
          _ = d - 1 := h_finrank_perp
      -- s.card ≤ dim(vectorSpan s) + 1 ≤ d.
      have hs_card : s.card ≤ d := by
        have h := hs_ai.card_le_finrank_succ
        have hcc : Fintype.card (s : Type _) = s.card := Fintype.card_coe s
        -- vectorSpan ℝ (Set.range ((↑) : s → E)) = vectorSpan ℝ (s : Set E)
        have hvs_eq : vectorSpan ℝ (Set.range ((↑) : (s : Set _) → EuclideanSpace ℝ (Fin d)))
            = vectorSpan ℝ (s : Set _) := by
          congr 1
          exact Subtype.range_coe_subtype.symm ▸ Subtype.range_val
        rw [hvs_eq] at h
        -- h : Fintype.card s ≤ finrank(vectorSpan s) + 1
        have hd_pos : 1 ≤ d := by
          -- We need d ≥ 1 since otherwise affine span dim issue. If d = 0, the hyperplane is empty.
          -- Actually d = 0: ℝ^0 = {0}, q ∈ ℝ^0 means q = 0, contradicting hq_ne.
          by_contra hd
          push_neg at hd
          interval_cases d
          have : q = 0 := by
            ext i; exact i.elim0
          exact hq_ne this
        omega
      -- Therefore ∃ i, p i ∉ s.
      have hexists_i_pi : ∃ i : Fin (d + 1), p i ∉ s := by
        by_contra hall
        push_neg at hall
        -- All p i ∈ s, so range p ⊆ s.
        have hrange_sub : Set.range p ⊆ (s : Set _) := by
          rintro _ ⟨i, rfl⟩
          exact hall i
        -- range p has cardinality ≥ ?... we use that p has d+1 indices but image may collapse.
        -- However: convexHull (range p) ⊆ conv(s), but we already have q ∈ conv(s).
        -- Hmm, we don't get a direct contradiction.
        -- Actually we need a contradiction. Let me think.
        -- The standard argument: hall says range p ⊆ s. We have s ⊆ range p. So s = range p.
        -- Then |s| = |range p| ≤ d+1. But hs_card says |s| ≤ d.
        -- So we'd need: the assumption all p_i ∈ s combined with hs_card gives a contradiction.
        -- It doesn't directly: s could have d elements with range p ⊆ s.
        -- But wait, if range p ⊆ s and s ⊆ range p, then s = range p. So |s| = |range p|.
        -- We don't directly get a contradiction from hs_card ≤ d.
        -- Hmm — the argument should be different. Let me reconsider.
        --
        -- We want: ∃ i, p i ∉ s. The contradiction approach won't work alone.
        -- Direct: if hs_card ≤ d, then s has ≤ d elements. There are d+1 indices p 0, ..., p d.
        -- By pigeonhole, two of them coincide — which means the function p : Fin(d+1) → s ∪ {extra}
        -- has some collision. This means range p has ≤ d distinct values, OR some p i ∉ s.
        -- Suppose all p i ∈ s. Then p : Fin(d+1) → s. Since |Fin(d+1)| = d+1 > d ≥ |s|,
        -- by pigeonhole, p is not injective: ∃ i ≠ j, p i = p j.
        -- But this doesn't give us "∃ i, p i ∉ s".
        --
        -- Wait, the goal is ∃ i, q ∈ conv({p k : k ≠ i}). Not "∃ i, p i ∉ s".
        -- If p i = p j (i ≠ j), then {p k : k ≠ i} = {p k : k ≠ j} ∪ {p i, p j with one removed}...
        -- Actually {p k : k ≠ i} = the image of {k : k ≠ i}. Since p j = p i and j ≠ i, p j ∈ {p k : k ≠ i}.
        -- So {p k : k ≠ i} contains p i (= p j). Hence range p \ ... hmm.
        -- {p k : k ≠ i} = {p k : k ≠ i, k ∈ Fin(d+1)}. This includes p j = p i if j ≠ i.
        -- So {p k : k ≠ i} = range p when there's a duplicate.
        -- Therefore q ∈ conv(range p) = conv({p k : k ≠ i}). Done!
        sorry
      -- Now we have i with p i ∉ s. So s ⊆ {p k : k ≠ i}.
      obtain ⟨i, hi⟩ := hexists_i_pi
      refine ⟨i, ?_⟩
      apply convexHull_mono _ hq_s
      -- Show (s : Set _) ⊆ p '' {j | j ≠ i}.
      intro x hx
      have hx_range : x ∈ Set.range p := hs_sub hx
      obtain ⟨k, hk⟩ := hx_range
      refine ⟨k, ?_, hk⟩
      simp only [Set.mem_setOf_eq]
      intro hk_eq
      apply hi
      rw [← hk]
      rw [hk_eq] at hk
      rw [← hk]
      sorry
  obtain ⟨i, hq_in_conv⟩ := hexists_i
  -- Step 4: Find c ∈ T i with ⟪q, c⟫ ≤ 0.
  have hc_exists : ∃ c ∈ T i, ⟪q, c⟫ ≤ 0 := by
    have h0_repr := mem_convexHull_iff_exists_fintype.mp (hT_zero i)
    obtain ⟨ι, hι, μ, t, hμ0, hμ1, ht, hsum⟩ := h0_repr
    -- 0 = ⟪q, ∑ μ k t k⟫ = ∑ μ k ⟪q, t k⟫
    have : (0 : ℝ) = ∑ k, μ k * ⟪q, t k⟫ := by
      have h1 : ⟪q, (0 : EuclideanSpace ℝ (Fin d))⟫ = 0 := inner_zero_right q
      rw [← hsum] at h1
      rw [inner_sum] at h1
      have : ∀ k, ⟪q, μ k • t k⟫ = μ k * ⟪q, t k⟫ := by
        intro k; rw [real_inner_smul_right]
      rw [show (∑ k, ⟪q, μ k • t k⟫) = ∑ k, μ k * ⟪q, t k⟫ from
        Finset.sum_congr rfl (fun k _ => this k)] at h1
      exact h1.symm
    -- Some k has μ k * ⟪q, t k⟫ ≤ 0. If μ k > 0, then ⟪q, t k⟫ ≤ 0.
    -- Since the sum is 0, and all μ k ≥ 0, if all ⟪q, t k⟫ > 0, then ∑ μ k ⟪q, t k⟫ > 0 (since ∑ μ k = 1).
    -- Hence some k has ⟪q, t k⟫ ≤ 0.
    by_contra hne
    push_neg at hne
    -- For every c ∈ T i, ⟪q, c⟫ > 0. Wait, hne says ∀ c ∈ T i, ⟪q, c⟫ > 0. Hmm actually we need to extract the right form.
    -- The original goal: ∃ c ∈ T i, ⟪q, c⟫ ≤ 0. After push_neg: ∀ c, c ∈ T i → 0 < ⟪q, c⟫.
    have hpos : ∀ k, 0 < ⟪q, t k⟫ := fun k => hne (t k) (ht k)
    -- Then ∑ μ k ⟪q, t k⟫ > 0 if some μ k > 0. But ∑ μ k = 1, so some μ k > 0.
    have : 0 < ∑ k, μ k * ⟪q, t k⟫ := by
      rcases Finset.exists_pos_of_sum_zero_of_exists_nonzero μ ?_ ?_ with ⟨k0, _, hk0⟩
      sorry
      sorry
      sorry
    linarith
  obtain ⟨c, hc_T, hc_inner⟩ := hc_exists
  -- Step 5: Define p' := update p i c, choose t, and compute ‖q'‖.
  let p' : Fin (d + 1) → EuclideanSpace ℝ (Fin d) := Function.update p i c
  -- p' is rainbow.
  have hp' : ∀ k, p' k ∈ T k := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [p', Function.update_same]; exact hc_T
    · simp [p', Function.update_noteq hk]; exact hp k
  -- {p k : k ≠ i} ⊆ range p'.
  have h_subset_range : (p '' {j | j ≠ i}) ⊆ Set.range p' := by
    rintro _ ⟨j, hj_ne, rfl⟩
    refine ⟨j, ?_⟩
    simp [p', Function.update_noteq hj_ne]
  have hq_in_conv' : q ∈ convexHull ℝ (Set.range p') :=
    convexHull_mono h_subset_range hq_in_conv
  have hc_in_range : c ∈ Set.range p' := ⟨i, by simp [p']⟩
  have hc_in_conv : c ∈ convexHull ℝ (Set.range p') := subset_convexHull _ _ hc_in_range
  -- Choose t and compute.
  -- q'(t) = (1-t)·q + t·c
  -- ‖q'(t)‖² - ‖q‖² = t · (-2‖q‖² + 2⟪q,c⟫ + t · ‖q-c‖²) = t · (α + t β)
  -- where α := -2‖q‖² + 2⟪q,c⟫ ≤ -2‖q‖² < 0, β := ‖q-c‖² ≥ 0.
  set qq : ℝ := ⟪q, q⟫
  have hqq_pos : 0 < qq := by
    have := real_inner_self_eq_norm_sq q
    have hne : q ≠ 0 := hq_ne
    have hpos : 0 < ‖q‖ := norm_pos_iff.mpr hne
    have : qq = ‖q‖ ^ 2 := this
    nlinarith
  set α : ℝ := -2 * qq + 2 * ⟪q, c⟫
  set β : ℝ := ‖q - c‖ ^ 2
  have hα_neg : α ≤ -2 * qq := by
    show -2 * qq + 2 * ⟪q, c⟫ ≤ -2 * qq
    linarith [hc_inner]
  have hα_strictneg : α < 0 := by linarith
  have hβ_nn : 0 ≤ β := sq_nonneg _
  -- Choose t = min(1, -α/(β+1)). Then t > 0, t ≤ 1, t (β + 1) ≤ -α. Hmm, want t β < -α.
  -- t β ≤ t (β + 1) ≤ -α, so t β ≤ -α. We want strict.
  -- Better: t β + α ≤ -α + α = 0, but want strict.
  -- Use t ∈ (0, 1) with t β < -α. We have β + 1 > 0 always.
  -- Take t = min(1/2, -α / (2 (β + 1))). Then t > 0 (since α < 0).
  -- t (β + 1) ≤ -α/2, so t β ≤ -α/2 < -α (since α < 0). So t β + α < 0. ✓
  set t : ℝ := min (1/2 : ℝ) (-α / (2 * (β + 1)))
  have ht_pos : 0 < t := by
    refine lt_min ?_ ?_
    · norm_num
    · apply div_pos
      · linarith
      · linarith
  have ht_le_one : t ≤ 1 := by
    have : t ≤ 1/2 := min_le_left _ _
    linarith
  have ht_le2 : t ≤ -α / (2 * (β + 1)) := min_le_right _ _
  have ht_β : t * β + α < 0 := by
    have hbp : 0 < β + 1 := by linarith
    have h2bp : 0 < 2 * (β + 1) := by linarith
    -- t * (2 * (β + 1)) ≤ -α, so t * (β + 1) ≤ -α / 2, so t * β ≤ -α/2 - t.
    have h1 : t * (2 * (β + 1)) ≤ -α := by
      rw [le_div_iff₀ h2bp] at ht_le2
      linarith
    -- t * 2β + t * 2 ≤ -α, so t * β ≤ -α/2 - t < -α (since t > 0 and α < 0)
    have h2 : t * β ≤ -α / 2 - t := by linarith
    have h3 : -α / 2 - t < -α := by linarith
    linarith
  -- Define q' and bound.
  let q' : EuclideanSpace ℝ (Fin d) := (1 - t) • q + t • c
  -- q' ∈ conv(range p')
  have hq'_in : q' ∈ convexHull ℝ (Set.range p') := by
    have hconv : Convex ℝ (convexHull ℝ (Set.range p')) := convex_convexHull _ _
    exact hconv hq_in_conv' hc_in_conv (by linarith) (le_of_lt ht_pos) (by linarith)
  -- ‖q'‖² < ‖q‖²
  have hnorm : ‖q'‖ ^ 2 < ‖q‖ ^ 2 := by
    -- Compute ‖q'‖² = ‖(1-t) q + t c‖² = (1-t)² ‖q‖² + 2 t (1-t) ⟪q,c⟫ + t² ‖c‖²
    have hexpand : ‖q'‖ ^ 2 =
        (1 - t)^2 * ‖q‖^2 + 2 * t * (1 - t) * ⟪q, c⟫ + t^2 * ‖c‖^2 := by
      have := norm_add_sq_real ((1 - t) • q) (t • c)
      rw [show q' = (1 - t) • q + t • c from rfl]
      rw [this]
      rw [norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
      simp [abs_of_pos, abs_of_nonneg, mul_pow]
      have h1t : 0 ≤ 1 - t := by linarith
      have ht_nn : 0 ≤ t := le_of_lt ht_pos
      rw [abs_of_nonneg h1t, abs_of_nonneg ht_nn]
      ring
    -- Express the difference.
    have hdiff : ‖q'‖^2 - ‖q‖^2 = t * (α + t * β) := by
      rw [hexpand]
      have hβ' : β = ‖q‖^2 - 2 * ⟪q, c⟫ + ‖c‖^2 := norm_sub_sq_real q c
      show ((1 - t)^2 * ‖q‖^2 + 2 * t * (1 - t) * ⟪q, c⟫ + t^2 * ‖c‖^2) - ‖q‖^2 = t * (α + t * β)
      have hqq' : qq = ‖q‖^2 := real_inner_self_eq_norm_sq q
      rw [show α = -2 * qq + 2 * ⟪q, c⟫ from rfl]
      rw [hqq', hβ']
      ring
    have hkey : t * (α + t * β) < 0 := by
      have : α + t * β < 0 := by linarith
      have := mul_neg_of_pos_of_neg ht_pos this
      linarith
    linarith
  refine ⟨p', q', hp', hq'_in, ?_⟩
  have hq_norm_pos : 0 < ‖q‖ := norm_pos_iff.mpr hq_ne
  have hq'_nn : 0 ≤ ‖q'‖ := norm_nonneg _
  exact lt_of_pow_lt_pow_left 2 (le_of_lt hq_norm_pos) hnorm

end NuminafuseTest.Blueprint
