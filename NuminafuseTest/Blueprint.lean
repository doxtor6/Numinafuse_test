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
  classical
  -- Step 1: Get a Fin (d+1)-indexed convex combination representation of q.
  obtain ⟨lam, hlam0, hlam1, hlam_sum⟩ : ∃ lam : Fin (d + 1) → ℝ, (∀ j, 0 ≤ lam j) ∧
      ∑ j, lam j = 1 ∧ ∑ j, lam j • p j = q := by
    obtain ⟨ι, hι, w, z, hw0, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hq_mem
    have hexists : ∀ j : ι, ∃ k : Fin (d + 1), p k = z j := by
      intro j; obtain ⟨k, hk⟩ := hz j; exact ⟨k, hk⟩
    choose σ hσ using hexists
    refine ⟨fun k => ∑ j ∈ Finset.univ.filter (fun j => σ j = k), w j, ?_, ?_, ?_⟩
    · intro k; exact Finset.sum_nonneg (fun j _ => hw0 j)
    · rw [← hw1]
      exact Finset.sum_fiberwise Finset.univ σ w
    · rw [← hsum]
      simp_rw [Finset.sum_smul]
      rw [← Finset.sum_fiberwise Finset.univ σ (fun j => w j • z j)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have h := (Finset.mem_filter.mp hj).2
      rw [show p k = z j from by rw [← hσ j, h]]
  -- Step 2: KKT and convex combination give pointwise equality.
  set qq : ℝ := ⟪q, q⟫ with hqq_def
  have hqq_pos : 0 < qq := by
    rw [hqq_def, real_inner_self_eq_norm_sq]
    have hpos : 0 < ‖q‖ := norm_pos_iff.mpr hq_ne
    positivity
  have hsum_qp : qq = ∑ j, lam j * ⟪q, p j⟫ := by
    have h1 : ⟪q, ∑ j, lam j • p j⟫ = ∑ j, lam j * ⟪q, p j⟫ := by
      rw [inner_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [real_inner_smul_right]
    rw [hlam_sum] at h1
    exact h1
  have hpoint : ∀ j, lam j * qq ≤ lam j * ⟪q, p j⟫ := fun j =>
    mul_le_mul_of_nonneg_left (hkkt j) (hlam0 j)
  have hsum_lower : ∑ j, lam j * qq ≤ ∑ j, lam j * ⟪q, p j⟫ :=
    Finset.sum_le_sum (fun j _ => hpoint j)
  have hlhs : ∑ j, lam j * qq = qq := by rw [← Finset.sum_mul, hlam1, one_mul]
  have hsum_eq2 : ∑ j, lam j * qq = ∑ j, lam j * ⟪q, p j⟫ := by
    apply le_antisymm hsum_lower
    rw [hlhs, hsum_qp]
  have hpoint_eq : ∀ j, lam j * qq = lam j * ⟪q, p j⟫ := by
    intro j
    by_contra h
    have hlt : lam j * qq < lam j * ⟪q, p j⟫ := lt_of_le_of_ne (hpoint j) h
    have : ∑ k, lam k * qq < ∑ k, lam k * ⟪q, p k⟫ :=
      Finset.sum_lt_sum (fun k _ => hpoint k) ⟨j, Finset.mem_univ _, hlt⟩
    linarith [hsum_eq2]
  -- Step 3: Find i with q ∈ conv({p k : k ≠ i}).
  have hexists_i : ∃ i : Fin (d + 1), q ∈ convexHull ℝ (p '' {j | j ≠ i}) := by
    by_cases hcase : ∃ i, lam i = 0
    · -- Case 1: some lam i = 0.
      obtain ⟨i, hi0⟩ := hcase
      refine ⟨i, ?_⟩
      apply mem_convexHull_of_exists_fintype
        (ι := {j : Fin (d + 1) // j ≠ i})
        (w := fun j => lam j.val) (z := fun j => p j.val)
      · intro j; exact hlam0 j.val
      · have h1 := Fintype.sum_subtype_add_sum_subtype (fun j : Fin (d + 1) => j ≠ i) lam
        have hcard : Fintype.card {j : Fin (d + 1) // ¬ j ≠ i} = 1 := by simp
        have h2 : ∑ j : {j : Fin (d + 1) // ¬ j ≠ i}, lam j.val = lam i := by
          have hcong : ∀ j : {j : Fin (d + 1) // ¬ j ≠ i}, lam j.val = lam i := fun j => by
            congr 1; have := j.property; push_neg at this; exact this
          rw [show (∑ j : {j : Fin (d + 1) // ¬ j ≠ i}, lam j.val) =
                  ∑ _j : {j : Fin (d + 1) // ¬ j ≠ i}, lam i from
              Finset.sum_congr rfl (fun j _ => hcong j)]
          rw [Finset.sum_const, Finset.card_univ, hcard, one_smul]
        rw [h2, hi0, add_zero] at h1
        rw [h1]; exact hlam1
      · intro j
        refine ⟨j.val, ?_, rfl⟩
        exact j.property
      · have h1 := Fintype.sum_subtype_add_sum_subtype
          (fun j : Fin (d + 1) => j ≠ i) (fun j => lam j • p j)
        have hcard : Fintype.card {j : Fin (d + 1) // ¬ j ≠ i} = 1 := by simp
        have h2 : ∑ j : {j : Fin (d + 1) // ¬ j ≠ i}, lam j.val • p j.val = lam i • p i := by
          have hcong : ∀ j : {j : Fin (d + 1) // ¬ j ≠ i},
              lam j.val • p j.val = lam i • p i := fun j => by
            have := j.property; push_neg at this; rw [this]
          rw [show (∑ j : {j : Fin (d + 1) // ¬ j ≠ i}, lam j.val • p j.val) =
                  ∑ _j : {j : Fin (d + 1) // ¬ j ≠ i}, lam i • p i from
              Finset.sum_congr rfl (fun j _ => hcong j)]
          rw [Finset.sum_const, Finset.card_univ, hcard, one_smul]
        rw [h2, hi0, zero_smul, add_zero] at h1
        rw [h1]; exact hlam_sum
    · -- Case 2: all lam j > 0.
      push_neg at hcase
      have hlam_pos : ∀ j, 0 < lam j := fun j => lt_of_le_of_ne (hlam0 j) (Ne.symm (hcase j))
      have hinner_eq : ∀ j, ⟪q, p j⟫ = qq := by
        intro j
        have h := hpoint_eq j
        have hne : lam j ≠ 0 := ne_of_gt (hlam_pos j)
        have h2 : lam j * (⟪q, p j⟫ - qq) = 0 := by linarith
        have h3 : ⟪q, p j⟫ - qq = 0 := by
          rcases mul_eq_zero.mp h2 with h | h
          · exact absurd h hne
          · exact h
        linarith
      set s : Finset (EuclideanSpace ℝ (Fin d)) :=
        Caratheodory.minCardFinsetOfMemConvexHull hq_mem with hs_def
      have hs_sub : (s : Set _) ⊆ Set.range p :=
        Caratheodory.minCardFinsetOfMemConvexHull_subseteq hq_mem
      have hq_s : q ∈ convexHull ℝ (s : Set _) :=
        Caratheodory.mem_minCardFinsetOfMemConvexHull hq_mem
      have hs_ai : AffineIndependent ℝ ((↑) : s → EuclideanSpace ℝ (Fin d)) :=
        Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hq_mem
      have hs_in_H : ∀ x ∈ s, ⟪q, x⟫ = qq := by
        intro x hx
        obtain ⟨k, hk⟩ := hs_sub hx
        rw [← hk]; exact hinner_eq k
      let Kperp : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
        (Submodule.span ℝ ({q} : Set _) : Submodule ℝ _).orthogonal
      have h_vspan_sub :
          vectorSpan ℝ (s : Set (EuclideanSpace ℝ (Fin d))) ≤ Kperp := by
        rw [vectorSpan_def, Submodule.span_le]
        intro v hv
        obtain ⟨x, hx, y, hy, hv_eq⟩ := hv
        show v ∈ Submodule.orthogonal _
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
        have hvxy : v = x - y := by
          rw [← hv_eq]; rfl
        rw [hvxy, inner_sub_left]
        rw [show ⟪x, q⟫ = ⟪q, x⟫ from (real_inner_comm x q).symm,
            show ⟪y, q⟫ = ⟪q, y⟫ from (real_inner_comm y q).symm]
        rw [hs_in_H x hx, hs_in_H y hy, sub_self]
      have h_finrank_perp : Module.finrank ℝ Kperp = d - 1 := by
        have hsum :
            Module.finrank ℝ (Submodule.span ℝ ({q} : Set (EuclideanSpace ℝ (Fin d)))) +
            Module.finrank ℝ Kperp = d := by
          have heq := Submodule.finrank_add_finrank_orthogonal
            (Submodule.span ℝ ({q} : Set (EuclideanSpace ℝ (Fin d))))
          rw [heq]
          exact finrank_euclideanSpace_fin
        have hq_span : Module.finrank ℝ
            (Submodule.span ℝ ({q} : Set (EuclideanSpace ℝ (Fin d)))) = 1 :=
          finrank_span_singleton hq_ne
        omega
      have hd_pos : 1 ≤ d := by
        by_contra hd
        push_neg at hd
        have hd0 : d = 0 := Nat.lt_one_iff.mp hd
        apply hq_ne
        subst hd0
        ext k
        exact (Fin.elim0 k : (q : EuclideanSpace ℝ (Fin 0)) k = 0)
      have h_vspan_dim :
          Module.finrank ℝ (vectorSpan ℝ (s : Set (EuclideanSpace ℝ (Fin d)))) ≤ d - 1 := by
        calc Module.finrank ℝ (vectorSpan ℝ (s : Set (EuclideanSpace ℝ (Fin d))))
            ≤ Module.finrank ℝ Kperp :=
              Submodule.finrank_mono h_vspan_sub
          _ = d - 1 := h_finrank_perp
      have hs_card : s.card ≤ d := by
        have h := hs_ai.card_le_finrank_succ
        have hcc : Fintype.card s = s.card := Fintype.card_coe s
        have hrange_eq : Set.range (Subtype.val : s → EuclideanSpace ℝ (Fin d))
            = (s : Set (EuclideanSpace ℝ (Fin d))) := Subtype.range_coe_subtype.trans rfl
        rw [hrange_eq] at h
        omega
      by_cases hinj : Function.Injective p
      · have hexists_pi_notmem : ∃ i : Fin (d + 1), p i ∉ s := by
          by_contra hall
          push_neg at hall
          have hrange_card : (Set.range p).ncard = d + 1 := by
            rw [Set.ncard_range_of_injective hinj]
            simp
          have hrange_sub : Set.range p ⊆ (s : Set _) := by
            rintro _ ⟨i, rfl⟩; exact hall i
          have hcard_le : (Set.range p).ncard ≤ s.card := by
            rw [← Set.ncard_coe_finset s]
            exact Set.ncard_le_ncard hrange_sub (s.finite_toSet)
          omega
        obtain ⟨i, hi⟩ := hexists_pi_notmem
        refine ⟨i, ?_⟩
        apply convexHull_mono _ hq_s
        intro x hx
        obtain ⟨k, hk⟩ := hs_sub hx
        refine ⟨k, ?_, hk⟩
        intro hk_eq
        apply hi
        subst hk_eq
        rw [hk]; exact hx
      · rw [Function.Injective] at hinj
        push_neg at hinj
        obtain ⟨i, j, hpij, hij⟩ := hinj
        refine ⟨i, ?_⟩
        have hrange_eq : Set.range p ⊆ p '' {k | k ≠ i} := by
          rintro _ ⟨k, rfl⟩
          by_cases hk : k = i
          · subst hk
            refine ⟨j, ?_, hpij.symm⟩
            simp; exact fun heq => hij heq.symm
          · refine ⟨k, ?_, rfl⟩
            simp [hk]
        exact convexHull_mono hrange_eq hq_mem
  obtain ⟨i, hq_in_conv⟩ := hexists_i
  -- Step 4: Find c ∈ T i with ⟪q, c⟫ ≤ 0.
  have hc_exists : ∃ c ∈ T i, ⟪q, c⟫ ≤ 0 := by
    obtain ⟨ι', hι', μ, t, hμ0, hμ1, ht, hsum⟩ :=
      mem_convexHull_iff_exists_fintype.mp (hT_zero i)
    have hsum_inner : (0 : ℝ) = ∑ k, μ k * ⟪q, t k⟫ := by
      have h1 : ⟪q, (0 : EuclideanSpace ℝ (Fin d))⟫ = 0 := inner_zero_right q
      rw [← hsum] at h1
      rw [inner_sum] at h1
      rw [show (∑ k, ⟪q, μ k • t k⟫) = ∑ k, μ k * ⟪q, t k⟫ from
        Finset.sum_congr rfl (fun k _ => by rw [real_inner_smul_right])] at h1
      exact h1.symm
    by_contra hne
    push_neg at hne
    have hpos : ∀ k, 0 < ⟪q, t k⟫ := fun k => hne (t k) (ht k)
    have hexists_pos : ∃ k, 0 < μ k := by
      by_contra hk_pos
      push_neg at hk_pos
      have heqzero : ∀ k, μ k = 0 := fun k => le_antisymm (hk_pos k) (hμ0 k)
      have hsum_zero : ∑ k, μ k = 0 := by
        rw [show (∑ k, μ k) = ∑ k, (0 : ℝ) from Finset.sum_congr rfl (fun k _ => heqzero k)]
        simp
      linarith
    obtain ⟨k0, hk0⟩ := hexists_pos
    have hsum_pos : 0 < ∑ k, μ k * ⟪q, t k⟫ := by
      have hnn : ∀ k ∈ (Finset.univ : Finset ι'), 0 ≤ μ k * ⟪q, t k⟫ := fun k _ =>
        mul_nonneg (hμ0 k) (le_of_lt (hpos k))
      have hk0_pos : 0 < μ k0 * ⟪q, t k0⟫ := mul_pos hk0 (hpos k0)
      exact Finset.sum_pos' hnn ⟨k0, Finset.mem_univ _, hk0_pos⟩
    linarith
  obtain ⟨c, hc_T, hc_inner⟩ := hc_exists
  -- Step 5: Define p' := update p i c, choose t, and bound the norm.
  let p' : Fin (d + 1) → EuclideanSpace ℝ (Fin d) := Function.update p i c
  have hp' : ∀ k, p' k ∈ T k := by
    intro k
    show Function.update p i c k ∈ T k
    by_cases hk : k = i
    · subst hk
      rw [Function.update_self]; exact hc_T
    · rw [Function.update_of_ne hk]; exact hp k
  have h_subset_range : (p '' {j | j ≠ i}) ⊆ Set.range p' := by
    rintro _ ⟨j, hj_ne, rfl⟩
    refine ⟨j, ?_⟩
    show Function.update p i c j = p j
    rw [Function.update_of_ne]
    exact hj_ne
  have hq_in_conv' : q ∈ convexHull ℝ (Set.range p') :=
    convexHull_mono h_subset_range hq_in_conv
  have hc_in_range : c ∈ Set.range p' := ⟨i, by show Function.update p i c i = c; simp⟩
  have hc_in_conv : c ∈ convexHull ℝ (Set.range p') := subset_convexHull _ _ hc_in_range
  set α : ℝ := -2 * qq + 2 * ⟪q, c⟫ with hα_def
  set β : ℝ := ‖q - c‖ ^ 2 with hβ_def
  have hα_neg : α ≤ -2 * qq := by show -2 * qq + 2 * ⟪q, c⟫ ≤ -2 * qq; linarith [hc_inner]
  have hα_strictneg : α < 0 := by linarith
  have hβ_nn : 0 ≤ β := sq_nonneg _
  set tval : ℝ := min (1/2 : ℝ) (-α / (2 * (β + 1))) with htval_def
  have ht_pos : 0 < tval := by
    refine lt_min ?_ ?_
    · norm_num
    · apply div_pos
      · linarith
      · linarith
  have ht_le_one : tval ≤ 1 := by
    have : tval ≤ 1/2 := min_le_left _ _
    linarith
  have ht_le2 : tval ≤ -α / (2 * (β + 1)) := min_le_right _ _
  have ht_β : tval * β + α < 0 := by
    have hbp : 0 < β + 1 := by linarith
    have h2bp : 0 < 2 * (β + 1) := by linarith
    have h1 : tval * (2 * (β + 1)) ≤ -α := by
      rw [le_div_iff₀ h2bp] at ht_le2
      linarith
    have h2 : tval * β ≤ -α / 2 - tval := by linarith
    linarith
  let q' : EuclideanSpace ℝ (Fin d) := (1 - tval) • q + tval • c
  have hq'_in : q' ∈ convexHull ℝ (Set.range p') := by
    have hconv : Convex ℝ (convexHull ℝ (Set.range p')) := convex_convexHull _ _
    exact hconv hq_in_conv' hc_in_conv (by linarith) (le_of_lt ht_pos) (by linarith)
  have hnorm_sq : ‖q'‖ ^ 2 < ‖q‖ ^ 2 := by
    have hqq' : qq = ‖q‖^2 := real_inner_self_eq_norm_sq q
    have hexpand : ‖q'‖ ^ 2 =
        (1 - tval)^2 * ‖q‖^2 + 2 * tval * (1 - tval) * ⟪q, c⟫ + tval^2 * ‖c‖^2 := by
      have hraw := norm_add_sq_real ((1 - tval) • q) (tval • c)
      change ‖((1 - tval) • q + tval • c)‖^2 = _
      rw [hraw]
      rw [norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
      have h1t : 0 ≤ 1 - tval := by linarith
      have ht_nn : 0 ≤ tval := le_of_lt ht_pos
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1t, abs_of_nonneg ht_nn]
      ring
    have hβ' : β = ‖q‖^2 - 2 * ⟪q, c⟫ + ‖c‖^2 := norm_sub_sq_real q c
    have hdiff : ‖q'‖^2 - ‖q‖^2 = tval * (α + tval * β) := by
      rw [hexpand]
      rw [show α = -2 * qq + 2 * ⟪q, c⟫ from rfl]
      rw [hqq', hβ']
      ring
    have hkey : tval * (α + tval * β) < 0 := by
      have hint : α + tval * β < 0 := by linarith
      exact mul_neg_of_pos_of_neg ht_pos hint
    linarith
  refine ⟨p', q', hp', hq'_in, ?_⟩
  have hq_norm_pos : 0 < ‖q‖ := norm_pos_iff.mpr hq_ne
  have hq'_nn : 0 ≤ ‖q'‖ := norm_nonneg _
  exact (sq_lt_sq₀ hq'_nn (le_of_lt hq_norm_pos)).mp hnorm_sq

/-- **Bárány's Colorful Carathéodory theorem (1982).** Given `d + 1`
subsets `C 0, …, C d` of the Euclidean space `ℝ^d` each containing the
origin in its convex hull, there is a "rainbow" choice `p i ∈ C i`
whose convex hull also contains the origin. -/
theorem MainTheorem (d : ℕ)
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
