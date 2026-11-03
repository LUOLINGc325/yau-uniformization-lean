import Yau.Proofs.C04BoundedGeometryChartsCoframeSmooth
import Yau.Proofs.C04BoundedGeometryChartsPhysicalJacobi
import Yau.LeafProofs.L12JacobiRegularity

/-! The actual exponential coframe is the actual Jacobi operator in its fixed initial frame. -/

noncomputable section
open scoped Topology Manifold ContDiff InnerProductSpace

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

def initialPhysicalCoordinates (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) :
    ComplexVector n ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) := by
  letI := underlyingRealTangentNormedAddCommGroup g.form p
  letI := underlyingRealTangentInnerProductSpace g.form p
  exact (realUnitaryFrame p U).trans
    (realInitialOrthonormalFrame g p).repr.toContinuousLinearEquiv

theorem realMapDeriv_unitaryExponential_eq_Jacobi (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v w : ComplexVector n) :
    realMapDeriv (unitaryExponential g p U) v w =
      realGeodesicJacobiField g (radialInitialState p U v) (realUnitaryFrame p U w) 1 := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form p
  letI := underlyingRealTangentInnerProductSpace g.form p
  let x := unitaryExponential g p U v
  have hchart : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) ∞
      (chartPt x) x := contMDiffAt_extChartAt
  have hF : DifferentiableAt ℝ
      (fun a => chartPt x (realExponentialMap g p a)) (realUnitaryFrame p U v) :=
    (hchart.comp _ (realExponentialMap_smooth g p).contMDiffAt).contDiffAt.differentiableAt (by simp)
  have HD := hF.hasFDerivAt.comp v (realUnitaryFrame p U).toContinuousLinearMap.hasFDerivAt
  have HD' : HasFDerivAt (fun a => chartPt x (unitaryExponential g p U a))
      ((fderiv ℝ (fun a => chartPt x (realExponentialMap g p a)) (realUnitaryFrame p U v)).comp
        (realUnitaryFrame p U).toContinuousLinearMap) v := HD
  have Heq : realTangentCoords x x (realMapDeriv (unitaryExponential g p U) v w) =
      realTangentCoords x x
        (realGeodesicJacobiField g (radialInitialState p U v) (realUnitaryFrame p U w) 1) := by
    have H₁ := congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L w)
      (realMapDeriv_coordinates g p U x v (mem_chart_source _ _))
    rw [HD'.fderiv] at H₁
    exact H₁.trans (realExponentialDifferential_coords g p x (realUnitaryFrame p U v)
      (realUnitaryFrame p U w) (mem_chart_source _ _)).symm
  have H := congrArg (realFrameCLM x x) Heq
  simpa only [realFrameCLM_realTangentCoords x x (mem_chart_source _ _)] using H

set_option maxRecDepth 2048 in
theorem radialCoframe_eq_physicalJacobi (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) :
    radialCoframe g p U v =
      (initialPhysicalCoordinates g p U).symm.toContinuousLinearMap.comp
        ((physicalJacobiOperator g (radialInitialState p U v) 1).comp
          (initialPhysicalCoordinates g p U).toContinuousLinearMap) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  apply ContinuousLinearMap.ext
  intro w
  apply (initialPhysicalCoordinates g p U).injective
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  have hrepr (z : TangentSpace 𝓘(ℝ, ComplexVector n) (unitaryExponential g p U v)) :
      initialPhysicalCoordinates g p U ((radialParallelFrame g p U v).symm z) =
        (realGlobalParallelFrame g (radialInitialState p U v) 1).repr z := by
    change initialPhysicalCoordinates g p U ((initialPhysicalCoordinates g p U).symm
      ((realGlobalParallelFrame g (radialInitialState p U v) 1).repr z)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  change initialPhysicalCoordinates g p U ((radialParallelFrame g p U v).symm
    (realMapDeriv (unitaryExponential g p U) v w)) = _
  rw [hrepr]
  rw [realMapDeriv_unitaryExponential_eq_Jacobi]
  apply PiLp.ext
  intro i
  exact realGeodesicJacobiField_coefficients g (radialInitialState p U v) 1
    (realUnitaryFrame p U w) i

theorem initialPhysicalCoordinates_norm (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j) (w : ComplexVector n) :
    ‖initialPhysicalCoordinates g p U w‖ = Real.sqrt 2 * ‖w‖ := by
  letI := underlyingRealTangentNormedAddCommGroup g.form p
  letI := underlyingRealTangentInnerProductSpace g.form p
  change ‖(realInitialOrthonormalFrame g p).repr (realUnitaryFrame p U w)‖ = _
  rw [LinearIsometryEquiv.norm_map, realUnitaryFrame_norm g.form p U hU]

end Yau.Proofs.C04ChartsAux
