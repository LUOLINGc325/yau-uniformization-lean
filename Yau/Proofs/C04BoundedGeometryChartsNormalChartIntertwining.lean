import Yau.Proofs.C04BoundedGeometryChartsNormalChartMap

/-! The actual chart differential commutes with multiplication by i in every genuine target chart. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L21Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem coordinate_fderiv_zero_norm (F : ComplexVector n → ComplexVector n)
    (hclose : ‖fderiv ℝ F 0 - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ)) :
    ‖fderiv ℝ F 0‖ ≤ (5 / 4 : ℝ) := by
  have H := norm_add_le (fderiv ℝ F 0 - ContinuousLinearMap.id ℝ (ComplexVector n))
    (ContinuousLinearMap.id ℝ (ComplexVector n))
  rw [sub_add_cancel] at H
  have hi := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ComplexVector n)
  linarith

theorem coordinate_fderiv_zero_complex (g : SmoothMetric M) (hk : KahlerClosed g.form)
    (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p) (d : ℝ)
    (F : ComplexVector n → ComplexVector n)
    (hcomplex : ∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ∀ v,
      fderiv ℝ F x (realPullbackJ (unitaryExponential g p U) (d • x) v) =
        Complex.I • fderiv ℝ F x v) (v : ComplexVector n) :
    fderiv ℝ F 0 (Complex.I • v) = Complex.I • fderiv ℝ F 0 v := by
  have H := hcomplex 0 (Metric.mem_ball_self (by norm_num)) v
  simpa only [smul_zero, realPullbackJ_zero g hk, stdComplex_apply] using H

theorem normalChartMap_chart_intertwines (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (F : ComplexVector n → ComplexVector n) (he : (e : ComplexVector n → ComplexVector n) = F)
    (hF : ContDiff ℝ ∞ F) (L : ComplexVector n →L[ℝ] ComplexVector n)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v) {d : ℝ} (hd : d ≠ 0)
    (c : M.Carrier) (z v : ComplexVector n)
    (hc : normalChartMap g p U e L d z ∈ (chartAt (ComplexVector n) c).source)
    (hparam : DifferentiableAt ℝ (normalizedInverseParameter e L d) z)
    (hw : d⁻¹ • L z ∈ e.target)
    (hiF : (fderiv ℝ F (e.symm (d⁻¹ • L z))).IsInvertible)
    (hrel : ∀ w, fderiv ℝ F (e.symm (d⁻¹ • L z))
        (realPullbackJ (unitaryExponential g p U) (d • e.symm (d⁻¹ • L z)) w) =
      Complex.I • fderiv ℝ F (e.symm (d⁻¹ • L z)) w)
    (hiE : (realMapDeriv (unitaryExponential g p U) (normalizedInverseParameter e L d z)).IsInvertible) :
    fderiv ℝ (fun y => chartPt c (normalChartMap g p U e L d y)) z (Complex.I • v) =
      Complex.I • fderiv ℝ (fun y => chartPt c (normalChartMap g p U e L d y)) z v := by
  have hα := normalizedInverseParameter_intertwines e F he hF
    (fun y => realPullbackJ (unitaryExponential g p U) (d • y)) L hL hd z hw hiF hrel v
  change fderiv ℝ (normalizedInverseParameter e L d) z (Complex.I • v) =
    realPullbackJ (unitaryExponential g p U) (normalizedInverseParameter e L d z)
      (fderiv ℝ (normalizedInverseParameter e L d) z v) at hα
  rw [normalChartMap_chart_fderiv g p U e L d c z hc hparam]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hα]
  exact unitaryExponential_chart_intertwines g p U c _ _ hc hiE

end Yau.Proofs.C04ChartsAux
