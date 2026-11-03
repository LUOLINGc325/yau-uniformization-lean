import Yau.LeafProofs.L05AutonomousBallMeanCutoff
import Yau.LeafProofs.L05AutonomousBallMeanTest
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_ballMean_test_source_integrable {n : ℕ} (hn : 0 < n) (omega : ℝ)
    {r eta : ℝ} (hr : 0 < r) (heta : 0 < eta)
    {f : Space n → ℝ} (hf : ∀ x∈closedBall 0 r, ContDiffAt ℝ 2 f x) :
    Integrable (fun x : Space n => autoGreenTest (2*n) omega r eta ‖x‖*autoBallMeanLaplacian f x) := by
  have hPhi : ContDiff ℝ 2 (autoGreenTest (2*n) omega r eta) :=
    (auto_green_test_contDiff (by omega : 2 ≤ 2*n) omega hr heta).of_le (by norm_num)
  have hS := auto_green_test_tsupport (d := 2*n) omega r heta
  have hG := auto_ballMean_radial_test_contDiff (n := n) heta hPhi hS
  have hGc := auto_ballMean_radial_test_compact (n := n) hS
  have hInt := auto_ballMean_integrable_mul_compact (f := autoBallMeanLaplacian f)
    (g := fun x : Space n => autoGreenTest (2*n) omega r eta ‖x‖) (by
      apply (auto_ballMean_laplacian_continuousOn hf).mono
      intro x hx
      exact closedBall_subset_closedBall (by linarith : r-eta ≤ r)
        (auto_ballMean_radial_test_tsupport hS hx)) hG.continuous hGc
  simpa only [mul_comm] using hInt

theorem auto_ballMean_test_source_tendsto {n : ℕ} (hn : 0 < n) {omega r : ℝ}
    (hOmega : 0 < omega) (hr : 0 < r)
    {f : Space n → ℝ} (hf : ∀ x∈closedBall 0 r, ContDiffAt ℝ 2 f x) :
    Tendsto (fun eta : ℝ => ∫ x : Space n,
      autoGreenTest (2*n) omega r eta ‖x‖*autoBallMeanLaplacian f x) (𝓝[>] 0)
      (𝓝 (∫ x : Space n, autoRadialGreen (2*n) omega r ‖x‖*autoBallMeanLaplacian f x)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x : Space n => ‖autoRadialGreen (2*n) omega r ‖x‖*autoBallMeanLaplacian f x‖)
  · filter_upwards [self_mem_nhdsWithin] with eta heta
    exact (auto_ballMean_test_source_integrable hn omega hr heta hf).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun eta => ae_of_all volume fun x => by
      obtain ⟨h0,h1⟩ := auto_green_test_nonneg_le (d := 2*n) (by omega) (eta := eta) (s := ‖x‖) hOmega hr
      simp only [norm_mul,Real.norm_eq_abs,
        abs_of_nonneg h0,abs_of_nonneg (auto_radialGreen_nonneg (r := r) (by omega : 0 < 2*n) hOmega ‖x‖)]
      exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  · exact (auto_ballMean_kernel_source_integrable hn omega hr hf).norm
  · exact ae_of_all volume fun x => (auto_green_test_tendsto omega r ‖x‖).mul_const (autoBallMeanLaplacian f x)

theorem auto_ballMean_test_ibp {n : ℕ} (hn : 0 < n) (omega : ℝ)
    {r eta : ℝ} (hr : 0 < r) (heta : 0 < eta)
    {f : Space n → ℝ} (hf : ∀ x∈closedBall 0 r, ContDiffAt ℝ 2 f x) :
    (∫ x : Space n, autoGreenTest (2*n) omega r eta ‖x‖*autoBallMeanLaplacian f x)=
      ∫ x : Space n, f x*autoBallMeanLaplacian (fun y : Space n => autoGreenTest (2*n) omega r eta ‖y‖) x :=
  auto_ballMean_radial_test_ibp heta (by linarith : r-eta ≤ r)
    ((auto_green_test_contDiff (by omega : 2 ≤ 2*n) omega hr heta).of_le (by norm_num))
    (auto_green_test_tsupport omega r heta) hf

end Yau.LeafProofs.L05AutonomousAux
