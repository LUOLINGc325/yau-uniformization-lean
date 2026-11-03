import Yau.LeafProofs.L03GradedCoreDensity

open MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

def multiplyGradedForm (η : M.Carrier → ℝ) (A : OperatorCandidates.GradedRealForm M) :
    OperatorCandidates.GradedRealForm M := fun j => multiplyRealForm η (A j)

theorem gradedL2_multiply_bounded (g : SmoothMetric M) (μ : Measure M.Carrier)
    (η : M.Carrier → ℝ) (hηm : AEStronglyMeasurable η μ) (C : ℝ) (hC : 0 ≤ C)
    (hη : ∀ y, |η y| ≤ C) (A : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A) :
    OperatorCandidates.GradedL2 g.form μ (multiplyGradedForm η A) :=
  (gradedL2_iff g.form μ _).mpr (fun j => l2RealForm_multiply_bounded g μ η hηm C hC hη (A j) (hA.2 j))

theorem gradedL2_multiply_smooth_compact (g : SmoothMetric M) (μ : Measure M.Carrier)
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (A : OperatorCandidates.GradedRealForm M) (hA : OperatorCandidates.GradedL2 g.form μ A) :
    OperatorCandidates.GradedL2 g.form μ (multiplyGradedForm η A) := by
  have hcont := L18Aux.continuous_of_smoothFn hη
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcη
  exact gradedL2_multiply_bounded g μ η hcont.aestronglyMeasurable (max C 0) (le_max_right _ _)
    (fun y => (show |η y| ≤ C by simpa only [Real.norm_eq_abs] using hC y).trans (le_max_left _ _)) A hA

theorem gradedInner_multiply_left (g : HermitianField M) (η : M.Carrier → ℝ)
    (A B : OperatorCandidates.GradedRealForm M) :
    OperatorCandidates.gradedInner g (multiplyGradedForm η A) B =
      fun y => η y * OperatorCandidates.gradedInner g A B y := by
  funext y
  simp only [OperatorCandidates.gradedInner, multiplyGradedForm, multiplyRealForm_inner_left]
  rw [Finset.mul_sum]

theorem gradedInner_multiply_right (g : HermitianField M) (η : M.Carrier → ℝ)
    (A B : OperatorCandidates.GradedRealForm M) :
    OperatorCandidates.gradedInner g A (multiplyGradedForm η B) =
      fun y => η y * OperatorCandidates.gradedInner g A B y := by
  funext y
  simp only [OperatorCandidates.gradedInner, multiplyGradedForm, multiplyRealForm_inner_right]
  rw [Finset.mul_sum]

theorem gradedInner_sub_left (g : HermitianField M) (A B C : OperatorCandidates.GradedRealForm M) :
    OperatorCandidates.gradedInner g (A - B) C =
      OperatorCandidates.gradedInner g A C - OperatorCandidates.gradedInner g B C := by
  funext y
  simp only [OperatorCandidates.gradedInner, Pi.sub_apply, formInner_sub_left, Finset.sum_sub_distrib]

theorem gradedInner_sub_right (g : HermitianField M) (A B C : OperatorCandidates.GradedRealForm M) :
    OperatorCandidates.gradedInner g A (B - C) =
      OperatorCandidates.gradedInner g A B - OperatorCandidates.gradedInner g A C := by
  funext y
  simp only [OperatorCandidates.gradedInner, Pi.sub_apply, formInner_sub_right, Finset.sum_sub_distrib]

/-- The actual compact-test Dirac commutator, computed from the original
fixed exterior and codifferential operators. -/
def diracCutoffCommutator (g : HermitianField M) (η : M.Carrier → ℝ)
    (B : OperatorCandidates.GradedRealForm M) : OperatorCandidates.GradedRealForm M :=
  diracRealForm g (multiplyGradedForm η B) - multiplyGradedForm η (diracRealForm g B)

theorem diracCutoffCommutator_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (B : OperatorCandidates.GradedRealForm M) (hB : ∀ j, SmoothRealForm (B j))
    (hcB : ∀ j, CompactlySupportedRealForm (B j)) :
    OperatorCandidates.GradedL2 g.form μ (diracCutoffCommutator g.form η B) := by
  have hηB (j : ℕ) : SmoothRealForm (multiplyGradedForm η B j) := smoothRealForm_multiply η (B j) hη (hB j)
  have hcηB (j : ℕ) : CompactlySupportedRealForm (multiplyGradedForm η B j) := compactlySupportedRealForm_multiply η (B j) (hcB j)
  have hfirst := (diracRealForm_corePair g μ hμ (multiplyGradedForm η B) hηB hcηB).2.1
  have hDB := diracRealForm_smooth g μ hμ B hB
  have hcDB := diracRealForm_compactlySupported g μ hμ B hB hcB
  have hsecond := gradedL2_of_smooth_compact g μ hμ (multiplyGradedForm η (diracRealForm g.form B))
    (fun j => smoothRealForm_multiply η _ hη (hDB j))
    (fun j => compactlySupportedRealForm_multiply η _ (hcDB j))
  exact gradedL2_sub g μ _ _ hfirst hsecond

/-- The actual output of a compact multiplier differs from the multiplied
original output by the fixed commutator acting on compact smooth tests. -/
theorem diracMaximalGraph_multiplier_error_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W V : OperatorCandidates.GradedRealForm M)
    (hmax : OperatorCandidates.DiracMaximalGraph g.form μ A W)
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (hmin : OperatorCandidates.DiracMinimalGraph g.form μ (multiplyGradedForm η A) V)
    (B Z : OperatorCandidates.GradedRealForm M) (hc : OperatorCandidates.DiracCorePair g.form μ B Z) :
    (∫ y, OperatorCandidates.gradedInner g.form (V - multiplyGradedForm η W) B y ∂μ) =
      -(∫ y, OperatorCandidates.gradedInner g.form A (diracCutoffCommutator g.form η B) y ∂μ) := by
  have hB (j : ℕ) : SmoothRealForm (B j) := (hc.2.2.1 j).1
  have hcB (j : ℕ) : CompactlySupportedRealForm (B j) := (hc.2.2.1 j).2.1
  have hηB (j : ℕ) : SmoothRealForm (multiplyGradedForm η B j) := smoothRealForm_multiply η (B j) hη (hB j)
  have hcηB (j : ℕ) : CompactlySupportedRealForm (multiplyGradedForm η B j) := compactlySupportedRealForm_multiply η (B j) (hcB j)
  have hηCore := diracRealForm_corePair g μ hμ (multiplyGradedForm η B) hηB hcηB
  have hηW := gradedL2_multiply_smooth_compact g μ η hη hcη W hmax.2.1
  have hηDB := gradedL2_of_smooth_compact g μ hμ (multiplyGradedForm η (diracRealForm g.form B))
    (fun j => smoothRealForm_multiply η _ hη (diracRealForm_smooth g μ hμ B hB j))
    (fun j => compactlySupportedRealForm_multiply η _ (diracRealForm_compactlySupported g μ hμ B hB hcB j))
  have h1 := (diracMinimalGraph_implies_maximal g μ hμ (multiplyGradedForm η A) V hmin).2.2 B Z hc
  have h2 := hmax.2.2 (multiplyGradedForm η B) (diracRealForm g.form (multiplyGradedForm η B)) hηCore
  have hp1 : OperatorCandidates.gradedInner g.form (multiplyGradedForm η A) Z =
      OperatorCandidates.gradedInner g.form A (multiplyGradedForm η Z) := by
    rw [gradedInner_multiply_left, gradedInner_multiply_right]
  have hp2 : OperatorCandidates.gradedInner g.form W (multiplyGradedForm η B) =
      OperatorCandidates.gradedInner g.form (multiplyGradedForm η W) B := by
    rw [gradedInner_multiply_right, gradedInner_multiply_left]
  have he1 := h1.2.2
  have he2 := h2.2.2
  rw [hp1, diracCorePair_output_eq g μ hμ B Z hc] at he1
  rw [hp2] at he2
  rw [gradedInner_sub_left]
  simp only [Pi.sub_apply]
  rw [integral_sub h1.2.1 (gradedInner_integrable g μ _ B hηW hc.1)]
  change _ = -(∫ y, OperatorCandidates.gradedInner g.form A
    (diracRealForm g.form (multiplyGradedForm η B) - multiplyGradedForm η (diracRealForm g.form B)) y ∂μ)
  rw [gradedInner_sub_right]
  simp only [Pi.sub_apply]
  rw [integral_sub h2.1 (gradedInner_integrable g μ A _ hmax.1 hηDB), ← he1, ← he2]
  ring

end Yau.LeafProofs.L03
