import Yau.Proofs.C04BoundedGeometryChartsInverseComplexIntertwining
import Yau.Proofs.C04BoundedGeometryChartsNormalModels

/-! The actual candidate chart is the exponential composed with the same normalized inverse. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

def normalChartMap (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (L : ComplexVector n →L[ℝ] ComplexVector n) (d : ℝ) (z : ComplexVector n) : M.Carrier :=
  unitaryExponential g p U (normalizedInverseParameter e L d z)

@[simp] theorem normalChartMap_zero (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (L : ComplexVector n →L[ℝ] ComplexVector n) (d : ℝ) (he0 : e.symm 0 = 0) :
    normalChartMap g p U e L d 0 = p := by
  rw [normalChartMap, normalizedInverseParameter_zero e L d he0, unitaryExponential_zero]

theorem normalChartMap_real_smoothOn (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (L : ComplexVector n →L[ℝ] ComplexVector n) (hL : ‖L‖ ≤ (5 / 4 : ℝ)) {d : ℝ} (hd : 0 < d)
    (ht : Metric.ball (0 : ComplexVector n) (1 / 8 : ℝ) ⊆ e.target)
    (he : ContDiffOn ℝ ∞ e.symm e.target) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) ∞
      (normalChartMap g p U e L d) (Metric.ball (0 : ComplexVector n) (d / 16)) := by
  letI := manifold_realSmooth M
  exact (unitaryExponential_smooth g p U).comp_contMDiffOn
    (normalizedInverseParameter_smoothOn e L hL hd ht he).contMDiffOn

theorem normalChartMap_chart_fderiv (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (L : ComplexVector n →L[ℝ] ComplexVector n) (d : ℝ) (c : M.Carrier) (z : ComplexVector n)
    (hc : normalChartMap g p U e L d z ∈ (chartAt (ComplexVector n) c).source)
    (hparam : DifferentiableAt ℝ (normalizedInverseParameter e L d) z) :
    fderiv ℝ (fun y => chartPt c (normalChartMap g p U e L d y)) z =
      (fderiv ℝ (fun y => chartPt c (unitaryExponential g p U y))
        (normalizedInverseParameter e L d z)).comp (fderiv ℝ (normalizedInverseParameter e L d) z) := by
  exact fderiv_comp z ((unitaryExponential_chart_smoothAt g p U c _ hc).differentiableAt (by simp)) hparam

theorem normalChartMap_chart_firstJet (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (F : ComplexVector n → ComplexVector n) (he : (e : ComplexVector n → ComplexVector n) = F)
    (hF : ContDiff ℝ ∞ F) (h0 : e.symm 0 = 0) (ht : (0 : ComplexVector n) ∈ e.target)
    (hi : (fderiv ℝ F 0).IsInvertible) {d : ℝ} (hd : d ≠ 0) :
    HasFDerivAt (fun z => chartPt p (normalChartMap g p U e (fderiv ℝ F 0) d z))
      ((realTangentCoords p p).comp (realUnitaryFrame p U).toContinuousLinearMap) 0 := by
  have hα := normalizedInverseParameter_hasFDerivAt_zero e F he hF h0 ht hi hd
  have hE : HasFDerivAt (fun y => chartPt p (unitaryExponential g p U y))
      ((realTangentCoords p p).comp (realUnitaryFrame p U).toContinuousLinearMap)
      (normalizedInverseParameter e (fderiv ℝ F 0) d 0) := by
    rw [normalizedInverseParameter_zero e _ d h0]
    exact unitaryExponential_chart_firstJet g p U
  have H := hE.comp 0 hα
  simpa only [normalChartMap, Function.comp_def, ContinuousLinearMap.comp_id] using H

end Yau.Proofs.C04ChartsAux
