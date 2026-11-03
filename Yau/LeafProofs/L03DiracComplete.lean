import Yau.LeafProofs.L03DiracCutoffEstimate

open MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

theorem multiplyGradedForm_l2_distance_tendsto (g : SmoothMetric M)
    (μ : Measure M.Carrier) (A : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A) (η : ℕ → M.Carrier → ℝ)
    (hη : ∀ j, SmoothFn (η j)) (hηrange : ∀ j y, η j y ∈ Set.Icc (0 : ℝ) 1)
    (ht : ∀ y, Tendsto (fun j => η j y) atTop (𝓝 1)) :
    Tendsto (fun j => OperatorCandidates.gradedDistanceSq g.form μ (multiplyGradedForm (η j) A) A)
      atTop (𝓝 0) := by
  simpa only [OperatorCandidates.gradedDistanceSq, multiplyGradedForm, Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.univ : Finset (Fin (2 * n + 1))) (fun i _ =>
      multiplyRealForm_l2_distance_tendsto g μ (A i.val) (hA.2 i.val) η hη hηrange ht)

/-- Quantitative cutoffs remove the compact-input restriction from the
actual Friedrichs graph closure. -/
theorem diracMaximalGraph_to_minimal_of_cutoffs (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M)
    (hmax : OperatorCandidates.DiracMaximalGraph g.form μ A W)
    (η : ℕ → M.Carrier → ℝ) (hη : ∀ j, SmoothFn (η j))
    (hcη : ∀ j, HasCompactSupport (η j))
    (hηrange : ∀ j y, η j y ∈ Set.Icc (0 : ℝ) 1)
    (htη : ∀ y, Tendsto (fun j => η j y) atTop (𝓝 1))
    (γ : ℕ → ℝ) (hγ : ∀ j, 0 ≤ γ j)
    (htγ : Tendsto γ atTop (𝓝 0))
    (hgrad : ∀ j y, L18Aux.scalarGradientPair g.form (η j) (η j) y ≤ γ j ^ 2) :
    OperatorCandidates.DiracMinimalGraph g.form μ A W := by
  choose V hV using fun j =>
    diracMaximalGraph_compact_multiplier_exists_minimal_output g μ hμ A W hmax (η j) (hη j) (hcη j)
  have hηW (j : ℕ) := gradedL2_multiply_smooth_compact g μ (η j) (hη j) (hcη j) W hmax.2.1
  have hR (j : ℕ) := gradedL2_sub g μ (V j) (multiplyGradedForm (η j) W) (hV j).2.1 (hηW j)
  have hbound (j : ℕ) := diracMaximalGraph_multiplier_error_norm_le g μ hμ A W (V j) hmax
    (η j) (hη j) (hcη j) (hV j) (γ j) (hγ j) (hgrad j) (hR j)
  have htR : Tendsto (fun j => realizeGradedL2 g μ (V j) (hV j).2.1 -
      realizeGradedL2 g μ (multiplyGradedForm (η j) W) (hηW j)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have htbound : Tendsto (fun j => diracCutoffDimensionConstant n * γ j *
        ‖realizeGradedL2 g μ A hmax.1‖) atTop (𝓝 0) := by
      simpa only [mul_zero, zero_mul] using (tendsto_const_nhds.mul htγ).mul_const
        ‖realizeGradedL2 g μ A hmax.1‖
    apply squeeze_zero (fun j => norm_nonneg _) _ htbound
    intro j
    rw [← realizeGradedL2_sub g μ (V j) (multiplyGradedForm (η j) W) (hV j).2.1 (hηW j) (hR j)]
    exact hbound j
  have htW := (tendsto_realizeGradedL2_iff g μ (fun j => multiplyGradedForm (η j) W) W hηW hmax.2.1).mpr
    (multiplyGradedForm_l2_distance_tendsto g μ W hmax.2.1 η hη hηrange htη)
  have htV : Tendsto (fun j => realizeGradedL2 g μ (V j) (hV j).2.1) atTop
      (𝓝 (realizeGradedL2 g μ W hmax.2.1)) := by
    simpa only [sub_add_cancel, zero_add] using htR.add htW
  exact diracMinimalGraph_of_tendsto g μ (fun j => multiplyGradedForm (η j) A) V A W hV hmax.1 hmax.2.1
    (multiplyGradedForm_l2_distance_tendsto g μ A hmax.1 η hη hηrange htη)
    ((tendsto_realizeGradedL2_iff g μ V W (fun j => (hV j).2.1) hmax.2.1).mp htV)

/-- The full original maximal Dirac graph lies in its original compact
smooth minimal closure. All localization and cutoff inputs are constructed. -/
theorem diracMaximalGraph_implies_minimal (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M)
    (hmax : OperatorCandidates.DiracMaximalGraph g.form μ A W) :
    OperatorCandidates.DiracMinimalGraph g.form μ A W := by
  classical
  cases isEmpty_or_nonempty M.Carrier with
  | inl hEmpty =>
      haveI := hEmpty
      have hA : A = 0 := by funext j y; exact isEmptyElim y
      have hW : W = 0 := by funext j y; exact isEmptyElim y
      rw [hA, hW]
      exact diracCorePair_minimal (diracCorePair_zero g μ hμ)
  | inr hNonempty =>
      let x : M.Carrier := Classical.choice hNonempty
      obtain ⟨C, hC, hCut⟩ := L18Aux.exists_uniform_scalar_energy_cutoffs n
      have h (j : ℕ) := hCut M g x ((j : ℝ) + 1) (by positivity)
      choose η hη using h
      have htη (y : M.Carrier) : Tendsto (fun j => η j y) atTop (𝓝 1) := by
        obtain ⟨N, hN⟩ := exists_nat_gt (inducedDistance g.form x y)
        have heq : (fun j => η j y) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
          filter_upwards [eventually_ge_atTop N] with j hj
          apply (hη j).2.2.2.2.1 y
          have hcast : (N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
          linarith
        exact (tendsto_congr' heq).mpr tendsto_const_nhds
      apply diracMaximalGraph_to_minimal_of_cutoffs g μ hμ A W hmax η
        (fun j => (hη j).2.1) (fun j => (hη j).2.2.1)
        (fun j => (hη j).2.2.2.1) htη (fun j => C / ((j : ℝ) + 1))
        (fun j => div_nonneg hC.le (by positivity))
      · exact tendsto_const_nhds.div_atTop
          (Filter.tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
      · intro j y
        exact (hη j).2.2.2.2.2.2 y

/-- Exact closure of the Dirac component of L03, with its original
full-degree compact core and original weak maximal domain. -/
theorem diracEssentialSelfAdjointness : OperatorCandidates.DiracEssentialSelfAdjointness := by
  intro n M g _ _ μ hμ A W
  exact ⟨diracMinimalGraph_implies_maximal g μ hμ A W,
    diracMaximalGraph_implies_minimal g μ hμ A W⟩

end Yau.LeafProofs.L03
