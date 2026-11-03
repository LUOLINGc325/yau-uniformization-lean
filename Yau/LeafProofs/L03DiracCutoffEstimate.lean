import Yau.LeafProofs.L03DiracCutoffSymbols

open MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

def diracCutoffDimensionConstant (n : ℕ) : ℝ := Real.sqrt (4 * (2 * n + 1 : ℕ) : ℝ)

theorem diracCutoffDimensionConstant_nonneg (n : ℕ) :
    0 ≤ diracCutoffDimensionConstant n := Real.sqrt_nonneg _

theorem diracCutoffDimensionConstant_sq (n : ℕ) :
    diracCutoffDimensionConstant n ^ 2 = (4 * (2 * n + 1 : ℕ) : ℝ) :=
  Real.sq_sqrt (by positivity)

/-- The actual compact-test commutator has an L² norm bound depending
only on the physical first derivative of the multiplier. -/
theorem diracCutoffCommutator_l2_norm_le (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (γ : ℝ) (hγ : 0 ≤ γ)
    (hgrad : ∀ y, L18Aux.scalarGradientPair g.form η η y ≤ γ ^ 2)
    (B : OperatorCandidates.GradedRealForm M) (hB : ∀ j, SmoothRealForm (B j))
    (hcB : ∀ j, CompactlySupportedRealForm (B j))
    (hBL2 : OperatorCandidates.GradedL2 g.form μ B)
    (hCL2 : OperatorCandidates.GradedL2 g.form μ (diracCutoffCommutator g.form η B)) :
    ‖realizeGradedL2 g μ (diracCutoffCommutator g.form η B) hCL2‖ ≤
      diracCutoffDimensionConstant n * γ * ‖realizeGradedL2 g μ B hBL2‖ := by
  have hi := integral_mono
    (gradedInner_integrable g μ _ _ hCL2 hCL2)
    ((gradedInner_integrable g μ B B hBL2 hBL2).const_mul
      ((4 * (2 * n + 1 : ℕ) : ℝ) * γ ^ 2))
    (fun y => (diracCutoffCommutator_graded_normSq_le g μ hμ η hη B hB y).trans (by
      have he := gradedInner_self_nonneg g.form B y
      have hd : (0 : ℝ) ≤ (4 * (2 * n + 1 : ℕ) : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hgrad y) hd) he))
  rw [integral_const_mul, ← realizeGradedL2_norm_sq g μ _ hCL2,
    ← realizeGradedL2_norm_sq g μ B hBL2] at hi
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (diracCutoffDimensionConstant_nonneg n) hγ) (norm_nonneg _))).mp
  calc
    _ ≤ (4 * (2 * n + 1 : ℕ) : ℝ) * γ ^ 2 * ‖realizeGradedL2 g μ B hBL2‖ ^ 2 := hi
    _ = _ := by rw [mul_pow, mul_pow, diracCutoffDimensionConstant_sq]

/-- The output of any compact multiplier of a raw maximal pair obeys
the same first-derivative error estimate. Its output was constructed by
chart Friedrichs approximation; no derivative of the raw input is assumed. -/
theorem diracMaximalGraph_multiplier_error_norm_le (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W V : OperatorCandidates.GradedRealForm M)
    (hmax : OperatorCandidates.DiracMaximalGraph g.form μ A W)
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (hmin : OperatorCandidates.DiracMinimalGraph g.form μ (multiplyGradedForm η A) V)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hgrad : ∀ y, L18Aux.scalarGradientPair g.form η η y ≤ γ ^ 2)
    (hR : OperatorCandidates.GradedL2 g.form μ (V - multiplyGradedForm η W)) :
    ‖realizeGradedL2 g μ (V - multiplyGradedForm η W) hR‖ ≤
      diracCutoffDimensionConstant n * γ * ‖realizeGradedL2 g μ A hmax.1‖ := by
  apply gradedHilbert_norm_le_of_core_pairings g μ hμ _ _
    (mul_nonneg (mul_nonneg (diracCutoffDimensionConstant_nonneg n) hγ) (norm_nonneg _))
  intro B Z hc
  have hB (j : ℕ) : SmoothRealForm (B j) := (hc.2.2.1 j).1
  have hcB (j : ℕ) : CompactlySupportedRealForm (B j) := (hc.2.2.1 j).2.1
  have hCL2 := diracCutoffCommutator_l2 g μ hμ η hη B hB hcB
  rw [realizeGradedL2_inner, diracMaximalGraph_multiplier_error_pairing g μ hμ A W V hmax η hη hcη hmin B Z hc,
    abs_neg, ← realizeGradedL2_inner g μ A _ hmax.1 hCL2]
  calc
    _ ≤ ‖realizeGradedL2 g μ A hmax.1‖ * ‖realizeGradedL2 g μ (diracCutoffCommutator g.form η B) hCL2‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖realizeGradedL2 g μ A hmax.1‖ *
        (diracCutoffDimensionConstant n * γ * ‖realizeGradedL2 g μ B hc.1‖) :=
      mul_le_mul_of_nonneg_left (diracCutoffCommutator_l2_norm_le g μ hμ η hη γ hγ hgrad B hB hcB hc.1 hCL2)
        (norm_nonneg _)
    _ = _ := by ring

end Yau.LeafProofs.L03
