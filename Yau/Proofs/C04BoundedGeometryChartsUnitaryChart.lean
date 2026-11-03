import Yau.Proofs.C04BoundedGeometryChartsChartCenter
import Yau.Proofs.C04BoundedGeometryChartsChartOrder
import Yau.Proofs.C04BoundedGeometryChartsChartInvertible

/-! The actual normalized exponential chart satisfies the frozen unitary-chart contract. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem normalChartMap_unitary (g : SmoothMetric M) (hk : KahlerClosed g.form)
    (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j)
    (R : ℝ) (hR : 0 < R) (d : ℝ) (hd : 0 < d) (hdR : d ≤ R / 4)
    (hA : ∀ y ∈ Metric.closedBall (0 : ComplexVector n) R,
      ‖radialCoframe g p U y - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ))
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
    (he0 : e.symm 0 = 0) (heSmooth : ContDiffOn ℝ ∞ e.symm e.target)
    (heNorm : ∀ w ∈ e.target, ‖e.symm w‖ ≤ (4 / 3 : ℝ) * ‖w‖) :
    UnitaryChart g.form p (normalChartMap g p U e (fderiv ℝ F 0) d) (d / 16) (1 / 16) 16 := by
  let L := fderiv ℝ F 0
  have hLclose := hclose 0 (Metric.mem_ball_self (by norm_num))
  have hL : ‖L‖ ≤ (5 / 4 : ℝ) := coordinate_fderiv_zero_norm F hLclose
  have hiL : L.IsInvertible := Yau.LeafProofs.L21Aux.isInvertible_of_norm_sub_id_lt_one _
    (hLclose.trans_lt (by norm_num))
  have h8 : Metric.ball (0 : ComplexVector n) (1 / 8 : ℝ) ⊆ e.target := by
    intro w hw
    exact ht (Metric.closedBall_subset_closedBall (by norm_num : (1 / 8 : ℝ) ≤ 3 / 16)
      (Metric.ball_subset_closedBall hw))
  have hαsmooth := normalizedInverseParameter_smoothOn e L hL hd h8 heSmooth
  have hhol := normalChartMap_holomorphic g hk p U R hR d hd hdR hEinv
    F hF hclose hcomplex e he hs ht heSmooth heNorm
  have hf (z : ComplexVector n) (hz : z ∈ Metric.ball (0 : ComplexVector n) (d / 16)) :
      MDifferentiableAt (ComplexModel n) (ComplexModel n) (normalChartMap g p U e L d) z :=
    (hhol.contMDiffAt (Metric.isOpen_ball.mem_nhds hz)).mdifferentiableAt (by simp)
  have hα (z : ComplexVector n) (hz : z ∈ Metric.ball (0 : ComplexVector n) (d / 16)) :
      DifferentiableAt ℝ (normalizedInverseParameter e L d) z :=
    (hαsmooth.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
  have hαR (z : ComplexVector n) (hz : z ∈ Metric.ball (0 : ComplexVector n) (d / 16)) :
      normalizedInverseParameter e L d z ∈ Metric.closedBall (0 : ComplexVector n) R := by
    have hn : ‖z‖ < d / 16 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hnorm := normalizedInverseParameter_norm_le e L hL hd h8 heNorm hz
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith
  have hψ (z : ComplexVector n) (hz : z ∈ Metric.ball (0 : ComplexVector n) (d / 16)) :
      e.symm (d⁻¹ • L z) ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ) := by
    rw [← hs]
    exact e.map_target (h8 (normalizedInverseParameter_argument_mem L hL hd hz))
  have h0 : (0 : ComplexVector n) ∈ Metric.ball 0 (d / 16) := Metric.mem_ball_self (by positivity)
  refine ⟨⟨hhol, ?_⟩, normalChartMap_zero g p U e L d he0, ?_, ?_⟩
  · intro z hz
    have hw := h8 (normalizedInverseParameter_argument_mem L hL hd hz)
    have hiF := Yau.LeafProofs.L21Aux.isInvertible_of_norm_sub_id_lt_one
      (fderiv ℝ F (e.symm (d⁻¹ • L z))) ((hclose _ (hψ z hz)).trans_lt (by norm_num))
    exact normalChartMap_complex_deriv_bijective g p U e L d z (hf z hz) (hα z hz)
      (normalizedInverseParameter_deriv_invertible e F he hF L hiL hd.ne' z hw hiF)
      (hEinv _ (hαR z hz))
  · exact normalChartMap_unitary_center g p U hU e F he hF he0
      (h8 (Metric.mem_ball_self (by norm_num))) hiL hd.ne' (hf 0 h0)
  · intro z hz
    exact normalChartMap_pullback_order g p U hU e L d z (hα z hz) (hf z hz) (hA _ (hαR z hz))
      (normalizedInverseParameter_deriv_norm_bounds e F he hF L hLclose hd.ne' z
        (h8 (normalizedInverseParameter_argument_mem L hL hd hz)) (hclose _ (hψ z hz)))

end Yau.Proofs.C04ChartsAux
