import Yau.Proofs.C04BoundedGeometryChartsFrame
import Yau.Proofs.C04BoundedGeometryChartsSmooth

/-! The actual exponential in a complex unitary initial frame. -/

noncomputable section
open scoped Topology Manifold ContDiff Matrix

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def realTangentJ (p : M.Carrier) :
    TangentSpace 𝓘(ℝ, ComplexVector n) p →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) p :=
  (realTangentEquiv p).symm.toContinuousLinearMap.comp
    (((Complex.I • ContinuousLinearMap.id ℂ (TangentVector M p)).restrictScalars ℝ).comp
      (realTangentEquiv p).toContinuousLinearMap)

theorem realTangentJ_square (p : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) p) :
    realTangentJ p (realTangentJ p v) = -v := by
  apply (realTangentEquiv p).injective
  simp [realTangentJ, smul_smul, Complex.I_sq]

theorem realUnitaryFrame_intertwines (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) :
    realTangentJ p (realUnitaryFrame p U v) = realUnitaryFrame p U (Complex.I • v) := by
  apply (realTangentEquiv p).injective
  change (realTangentEquiv p) ((realTangentEquiv p).symm
      (Complex.I • realTangentEquiv p (realUnitaryFrame p U v))) =
    realTangentEquiv p (realUnitaryFrame p U (Complex.I • v))
  rw [ContinuousLinearEquiv.apply_symm_apply, realTangentEquiv_realUnitaryFrame,
    realTangentEquiv_realUnitaryFrame, map_smul]

def unitaryExponential (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) : M.Carrier :=
  realExponentialMap g p (realUnitaryFrame p U v)

@[simp] theorem unitaryExponential_zero (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) : unitaryExponential g p U 0 = p := by
  simp only [unitaryExponential, map_zero, realExponentialMap_zero]

theorem unitaryExponential_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) :
    letI := manifold_realSmooth M
    ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) ∞ (unitaryExponential g p U) := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form p
  letI := underlyingRealTangentInnerProductSpace g.form p
  exact (realExponentialMap_smooth g p).comp
    (realUnitaryFrame p U).toContinuousLinearMap.contMDiff

theorem unitaryExponential_chart_firstJet (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) :
    HasFDerivAt (fun v => chartPt p (unitaryExponential g p U v))
      ((realTangentCoords p p).comp (realUnitaryFrame p U).toContinuousLinearMap) 0 := by
  let L := (realTangentCoords p p).comp (realUnitaryFrame p U).toContinuousLinearMap
  have hE : (fun v => chartPt p (unitaryExponential g p U v)) =
      realExponentialCoordinates g p ∘ L := by
    funext v
    dsimp [unitaryExponential, realExponentialCoordinates, L]
    rw [realFrameCLM_realTangentCoords p p (mem_chart_source _ _)]
  rw [hE]
  have HD : HasFDerivAt (realExponentialCoordinates g p)
      (ContinuousLinearMap.id ℝ (ComplexVector n)) (L 0) := by
    simpa only [map_zero] using hasFDerivAt_realExponentialCoordinates_zero g p
  have H := HD.comp 0 L.hasFDerivAt
  simpa only [map_zero, ContinuousLinearMap.id_comp] using H

/-- The actual pulled complex structure, using the real differential. -/
def realPullbackJ (E : ComplexVector n → M.Carrier) (z : ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n :=
  (realMapDeriv E z).inverse.comp ((realTangentJ (E z)).comp (realMapDeriv E z))

end Yau.Proofs.C04ChartsAux
