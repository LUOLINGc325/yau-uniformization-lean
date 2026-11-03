import Yau.Proofs.C04BoundedGeometryChartsManifoldComplexSmooth
import Yau.Proofs.C04BoundedGeometryChartsNormalChartIntertwining

/-! The actual exponential composed with the normalized same inverse is a complex smooth chart map. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem normalChartMap_holomorphic (g : SmoothMetric M) (hk : KahlerClosed g.form)
    (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (R : ℝ) (hR : 0 < R) (d : ℝ) (hd : 0 < d) (hdR : d ≤ R / 4)
    (hEinv : ∀ y ∈ Metric.closedBall (0 : ComplexVector n) R,
      (realMapDeriv (unitaryExponential g p U) y).IsInvertible)
    (F : ComplexVector n → ComplexVector n) (hF : ContDiff ℝ ∞ F)
    (hclose : ∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ),
      ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ))
    (hcomplex : ∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ∀ v,
      fderiv ℝ F x (realPullbackJ (unitaryExponential g p U) (d • x) v) =
        Complex.I • fderiv ℝ F x v)
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (he : (e : ComplexVector n → ComplexVector n) = F)
    (hs : e.source = Metric.ball 0 (1 / 2 : ℝ))
    (ht : Metric.closedBall (0 : ComplexVector n) (3 / 16 : ℝ) ⊆ e.target)
    (heSmooth : ContDiffOn ℝ ∞ e.symm e.target)
    (heNorm : ∀ w ∈ e.target, ‖e.symm w‖ ≤ (4 / 3 : ℝ) * ‖w‖) :
    ContMDiffOn (ComplexModel n) (ComplexModel n) ∞
      (normalChartMap g p U e (fderiv ℝ F 0) d) (Metric.ball (0 : ComplexVector n) (d / 16)) := by
  let L := fderiv ℝ F 0
  have hL : ‖L‖ ≤ (5 / 4 : ℝ) := coordinate_fderiv_zero_norm F (hclose 0 (Metric.mem_ball_self (by norm_num)))
  have hLc : ∀ v, L (Complex.I • v) = Complex.I • L v :=
    coordinate_fderiv_zero_complex g hk p U d F hcomplex
  have h8 : Metric.ball (0 : ComplexVector n) (1 / 8 : ℝ) ⊆ e.target := by
    intro w hw
    exact ht (Metric.closedBall_subset_closedBall (by norm_num : (1 / 8 : ℝ) ≤ 3 / 16)
      (Metric.ball_subset_closedBall hw))
  have hparam : ContDiffOn ℝ ∞ (normalizedInverseParameter e L d) (Metric.ball (0 : ComplexVector n) (d / 16)) :=
    normalizedInverseParameter_smoothOn e L hL hd h8 heSmooth
  apply contMDiffOn_complex_of_real_chart_I Metric.isOpen_ball _
    (normalChartMap_real_smoothOn g p U e L hL hd h8 heSmooth)
  intro c z hz hc v
  have hα : DifferentiableAt ℝ (normalizedInverseParameter e L d) z :=
    (hparam.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
  have hw : d⁻¹ • L z ∈ e.target := h8 (normalizedInverseParameter_argument_mem L hL hd hz)
  have hψ : e.symm (d⁻¹ • L z) ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ) := by
    rw [← hs]
    exact e.map_target hw
  have hiF := Yau.LeafProofs.L21Aux.isInvertible_of_norm_sub_id_lt_one
    (fderiv ℝ F (e.symm (d⁻¹ • L z))) ((hclose _ hψ).trans_lt (by norm_num))
  have hαR : normalizedInverseParameter e L d z ∈ Metric.closedBall (0 : ComplexVector n) R := by
    have hn : ‖z‖ < d / 16 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hnorm := normalizedInverseParameter_norm_le e L hL hd h8 heNorm hz
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith
  exact normalChartMap_chart_intertwines g p U e F he hF L hLc hd.ne' c z v hc hα hw hiF
    (hcomplex _ hψ) (hEinv _ hαR)

end Yau.Proofs.C04ChartsAux
