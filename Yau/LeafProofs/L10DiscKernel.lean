import Yau.LeafProofs.L10GreenMass
import Mathlib.Analysis.Complex.Isometry

/-! Weighted first-derivative integrals and the exact rotation law for the
explicit Dirichlet Green solution. No regularity of the solution is assumed. -/

noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate Topology

namespace Yau.LeafProofs

/-- The actual off-diagonal derivative, multiplied by the density. -/
def discGreenDerivativeIntegrand (f : ℂ → ℂ) (z w : ℂ) : ℂ →L[ℝ] ℂ :=
  (fderiv ℝ (fun y => discGreenKernel y w) z).smulRight (f w)

/-- This integral will be identified with the within derivative of the
solution by the segment FTC argument. -/
def discGreenDerivative (f : ℂ → ℂ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  ∫ w in Metric.ball (0 : ℂ) 1, discGreenDerivativeIntegrand f z w

theorem discGreenDerivativeIntegrand_aestronglyMeasurable {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    AEStronglyMeasurable (discGreenDerivativeIntegrand f z)
      (volume.restrict (Metric.ball (0 : ℂ) 1)) := by
  exact (ContinuousLinearMap.smulRightL ℝ ℂ ℂ).aestronglyMeasurable_comp₂
    (discGreen_gradient_aestronglyMeasurable hz)
    ((hf.mono Metric.ball_subset_closedBall).aestronglyMeasurable measurableSet_ball)

theorem discGreenDerivativeIntegrand_integrable {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    IntegrableOn (discGreenDerivativeIntegrand f z) (Metric.ball (0 : ℂ) 1) volume := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hf
  apply ((discGreen_gradient_integrable hz).norm.mul_const M).mono'
    (discGreenDerivativeIntegrand_aestronglyMeasurable hf hz)
  filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
  rw [discGreenDerivativeIntegrand, ContinuousLinearMap.norm_smulRight_apply]
  exact mul_le_mul_of_nonneg_left (hM w (Metric.ball_subset_closedBall hw)) (norm_nonneg _)

theorem discGreenDerivative_apply {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (v : ℂ) :
    discGreenDerivative f z v = ∫ w in Metric.ball (0 : ℂ) 1,
      fderiv ℝ (fun y => discGreenKernel y w) z v • f w := by
  exact ContinuousLinearMap.integral_apply (discGreenDerivativeIntegrand_integrable hf hz) v

/-- The singular part of the weighted derivative has a uniform linear
small-ball bound. The same density bound works for all pole positions. -/
theorem discGreenDerivativeIntegrand_near_mass {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, ‖f w‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ 1) {r : ℝ} (hr : 0 < r) :
    (∫ w in Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r,
      ‖discGreenDerivativeIntegrand f z w‖) ≤ 2 * M * r := by
  have hi : IntegrableOn (fun w => ‖discGreenDerivativeIntegrand f z w‖)
      (Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r) volume :=
    ((discGreenDerivativeIntegrand_integrable hf hz).mono_set Set.inter_subset_left).norm
  have hg : IntegrableOn (fun w => ‖fderiv ℝ (fun y => discGreenKernel y w) z‖)
      (Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r) volume :=
    ((discGreen_gradient_integrable hz).mono_set Set.inter_subset_left).norm
  calc
    _ ≤ ∫ w in Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r,
        ‖fderiv ℝ (fun y => discGreenKernel y w) z‖ * M := by
      apply integral_mono_ae hi (hg.mul_const M)
      filter_upwards [ae_restrict_mem (measurableSet_ball.inter measurableSet_ball)] with w hw
      rw [discGreenDerivativeIntegrand, ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_left (hbound w (Metric.ball_subset_closedBall hw.1))
        (norm_nonneg _)
    _ = (∫ w in Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r,
        ‖fderiv ℝ (fun y => discGreenKernel y w) z‖) * M := integral_mul_const _ _
    _ ≤ (2 * r) * M := mul_le_mul_of_nonneg_right (discGreen_gradient_near_mass hz hr) hM
    _ = _ := by ring

theorem discGreenSolution_add {f g : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1))
    (hg : ContinuousOn g (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discGreenSolution (f + g) z = discGreenSolution f z + discGreenSolution g z := by
  simp only [discGreenSolution, Pi.add_apply, smul_add]
  exact integral_add (discGreen_solution_integrable hf hz) (discGreen_solution_integrable hg hz)

theorem discGreenSolution_smul (c : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    discGreenSolution (c • f) z = c • discGreenSolution f z := by
  simp only [discGreenSolution, Pi.smul_apply, smul_comm _ c]
  exact integral_smul c _

/-- Multiplication by a unit complex number preserves the actual area
integral and the unit disc. -/
theorem discGreenSolution_rotation (a : Circle) (f : ℂ → ℂ) (z : ℂ) :
    discGreenSolution f ((a : ℂ) * z) =
      discGreenSolution (fun w => f ((a : ℂ) * w)) z := by
  let R : ℂ ≃ₗᵢ[ℝ] ℂ := rotation a
  have hpre : R ⁻¹' Metric.ball (0 : ℂ) 1 = Metric.ball (0 : ℂ) 1 := by
    ext w
    change dist (R w) 0 < 1 ↔ dist w 0 < 1
    rw [dist_zero_right, dist_zero_right, R.norm_map]
  have h := R.measurePreserving.setIntegral_preimage_emb
    R.toMeasurableEquiv.measurableEmbedding
    (fun w => discGreenKernel ((a : ℂ) * z) w • f w) (Metric.ball (0 : ℂ) 1)
  rw [hpre] at h
  unfold discGreenSolution
  rw [← h]
  apply integral_congr_ae
  filter_upwards with w
  simp only [R, rotation_apply, discGreen_rotation _ _ _ (Circle.norm_coe a)]

end Yau.LeafProofs
