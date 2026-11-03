import Yau.Proofs.V02DiscDbar

/-! The canonical dbar solution has a fixed W¹,² bound, deduced from the
actual Green solution's zero-Dirichlet energy estimates. -/

open scoped Topology ContDiff
open Filter MeasureTheory

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.LeafProofs

theorem canonicalGreen_gradient_hessian_estimate {b : ℂ → ℂ}
    (hb : ContDiffOn ℝ ∞ b (Metric.closedBall (0 : ℂ) 1)) :
    (∫ z in Metric.ball (0 : ℂ) 1, discEnergyGradientSq (discGreenSolution b) z) ≤
        ∫ z in Metric.ball (0 : ℂ) 1, ‖b z‖ ^ 2 ∧
      (∫ z in Metric.ball (0 : ℂ) 1, discEnergyHessianSq (discGreenSolution b) z) ≤
        ∫ z in Metric.ball (0 : ℂ) 1, ‖b z‖ ^ 2 := by
  let u := discGreenSolution b
  have hu := discGreenSolution_contDiffOn hb
  have hz : ∀ z ∈ Metric.sphere (0 : ℂ) 1, u z = 0 :=
    fun z hz => discGreenSolution_boundary b hz
  have hr := discMirandaTalenti (Complex.reCLM.contDiff.comp_contDiffOn hu)
    (fun z h => by change (u z).re = 0; rw [hz z h]; rfl)
  have hi := discMirandaTalenti (Complex.imCLM.contDiff.comp_contDiffOn hu)
    (fun z h => by change (u z).im = 0; rw [hz z h]; rfl)
  have hH := discEnergy_complex_hessian_estimate hu hr hi
  have hG := (discEnergy_complex_first_order hu hz).2
  have heq : (∫ z in Metric.ball (0 : ℂ) 1, ‖discEnergyLaplacian u z‖ ^ 2) =
      ∫ z in Metric.ball (0 : ℂ) 1, ‖b z‖ ^ 2 := by
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro z h
    dsimp only
    rw [discEnergyLaplacian_eq_planar h, discGreenSolution_laplacian hb h]
  rw [heq] at hG hH
  exact ⟨hG, hH⟩

theorem discEnergyPartial_sub {f g : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1))
    (hg : ContDiffOn ℝ ∞ g (Metric.closedBall (0 : ℂ) 1))
    (v : ℂ) {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discEnergyPartial (fun w => f w - g w) v z =
      discEnergyPartial f v z - discEnergyPartial g v z := by
  unfold discEnergyPartial
  rw [fderivWithin_fun_sub (disc_closedBall_uniqueDiffOn z hz)
    ((hf.differentiableOn (by simp)) z hz) ((hg.differentiableOn (by simp)) z hz)]
  rfl

theorem discEnergyPartial_const_mul {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1))
    (c v : ℂ) {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discEnergyPartial (fun w => c * f w) v z = c * discEnergyPartial f v z :=
  discEnergyPartial_clm ((ContinuousLinearMap.mul ℝ ℂ) c) hf v hz

theorem discDbarSolution_partial {b : ℂ → ℂ}
    (hb : ContDiffOn ℝ ∞ b (Metric.closedBall (0 : ℂ) 1))
    (v : ℂ) {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discEnergyPartial (discDbarSolution b) v z =
      2 * (discEnergyPartial (discEnergyPartial (discGreenSolution b) 1) v z -
        Complex.I * discEnergyPartial (discEnergyPartial (discGreenSolution b) Complex.I) v z) := by
  have hu := discGreenSolution_contDiffOn hb
  have hp := discEnergyPartial_contDiffOn hu 1
  have hq := discEnergyPartial_contDiffOn hu Complex.I
  unfold discDbarSolution
  rw [discEnergyPartial_const_mul (hp.sub (contDiffOn_const.mul hq)) 2 v hz,
    discEnergyPartial_sub hp (contDiffOn_const.mul hq) v hz,
    discEnergyPartial_const_mul hq Complex.I v hz]

theorem norm_two_wirtinger_sq_le (p q : ℂ) :
    ‖(2 : ℂ) * (p - Complex.I * q)‖ ^ 2 ≤ 8 * (‖p‖ ^ 2 + ‖q‖ ^ 2) := by
  have hn : ‖(2 : ℂ) * (p - Complex.I * q)‖ ≤ 2 * (‖p‖ + ‖q‖) := by
    calc
      _ = 2 * ‖p - Complex.I * q‖ := by simp [norm_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa using norm_sub_le p (Complex.I * q))
        (by norm_num)
  nlinarith [norm_nonneg ((2 : ℂ) * (p - Complex.I * q)), norm_nonneg p,
    norm_nonneg q, sq_nonneg (‖p‖ - ‖q‖)]

theorem discDbarSolution_norm_sq_le (b : ℂ → ℂ) (z : ℂ) :
    ‖discDbarSolution b z‖ ^ 2 ≤ 8 * discEnergyGradientSq (discGreenSolution b) z :=
  norm_two_wirtinger_sq_le _ _

theorem discDbarSolution_gradient_sq_le {b : ℂ → ℂ}
    (hb : ContDiffOn ℝ ∞ b (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discEnergyGradientSq (discDbarSolution b) z ≤
      8 * discEnergyHessianSq (discGreenSolution b) z := by
  unfold discEnergyGradientSq
  rw [discDbarSolution_partial hb 1 hz, discDbarSolution_partial hb Complex.I hz]
  have hx := norm_two_wirtinger_sq_le
    (discEnergyPartial (discEnergyPartial (discGreenSolution b) 1) 1 z)
    (discEnergyPartial (discEnergyPartial (discGreenSolution b) Complex.I) 1 z)
  have hy := norm_two_wirtinger_sq_le
    (discEnergyPartial (discEnergyPartial (discGreenSolution b) 1) Complex.I z)
    (discEnergyPartial (discEnergyPartial (discGreenSolution b) Complex.I) Complex.I z)
  unfold discEnergyHessianSq
  linarith

theorem discDbarSolution_W12_estimate {b : ℂ → ℂ}
    (hb : ContDiffOn ℝ ∞ b (Metric.closedBall (0 : ℂ) 1)) :
    (∫ z in Metric.ball (0 : ℂ) 1, ‖discDbarSolution b z‖ ^ 2) +
      (∫ z in Metric.ball (0 : ℂ) 1, discEnergyGradientSq (discDbarSolution b) z) ≤
        16 * (∫ z in Metric.ball (0 : ℂ) 1, ‖b z‖ ^ 2) := by
  have hu := discGreenSolution_contDiffOn hb
  have hQ := discDbarSolution_contDiffOn hb
  have hG := discEnergy_integrableOn (discEnergyGradientSq_continuousOn hu)
  have hH := discEnergy_integrableOn (discEnergyHessianSq_continuousOn hu)
  have hnorm := integral_mono_ae
    (discEnergy_integrableOn (hQ.continuousOn.norm.pow 2)) (hG.const_mul 8)
    (Filter.Eventually.of_forall (discDbarSolution_norm_sq_le b))
  have hgrad := integral_mono_ae
    (discEnergy_integrableOn (discEnergyGradientSq_continuousOn hQ)) (hH.const_mul 8) (by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
      exact discDbarSolution_gradient_sq_le hb (Metric.ball_subset_closedBall hz))
  rw [integral_const_mul] at hnorm hgrad
  change (∫ z in Metric.ball (0 : ℂ) 1, ‖discDbarSolution b z‖ ^ 2) ≤
    8 * (∫ z in Metric.ball (0 : ℂ) 1, discEnergyGradientSq (discGreenSolution b) z) at hnorm
  have he := canonicalGreen_gradient_hessian_estimate hb
  linarith [he.1, he.2]

end Yau.Blueprint.V02Proof
