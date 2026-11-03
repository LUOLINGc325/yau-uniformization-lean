import Yau.Proofs.C04BoundedGeometryChartsCoframeSmooth

/-! The connection induced by an actual moving frame along a smooth coordinate map. -/

noncomputable section
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

def coordinateFrameConnection
    (Γ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (Z : ComplexVector n → ComplexVector n)
    (P : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n) (v : ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n :=
  let C := ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) (ComplexVector n)
  (C (P v).inverse).comp
    (fderiv ℝ P v + (C.flip (P v)).comp ((Γ (Z v)).comp (fderiv ℝ Z v)))

theorem coordinateFrameConnection_apply
    (Γ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (Z : ComplexVector n → ComplexVector n)
    (P : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n) (v u w : ComplexVector n) :
    coordinateFrameConnection Γ Z P v u w = (P v).inverse
      (fderiv ℝ P v u w + Γ (Z v) (fderiv ℝ Z v u) (P v w)) := rfl

theorem coordinateFrameConnection_equation
    (Γ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (Z : ComplexVector n → ComplexVector n)
    (P : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n) (v u w : ComplexVector n)
    (hP : (P v).IsInvertible) :
    P v (coordinateFrameConnection Γ Z P v u w) =
      fderiv ℝ P v u w + Γ (Z v) (fderiv ℝ Z v u) (P v w) := by
  rw [coordinateFrameConnection_apply, hP.self_apply_inverse]

theorem coordinateFrameConnection_smoothAt
    (Γ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (Z : ComplexVector n → ComplexVector n)
    (P : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n) (v : ComplexVector n)
    (hΓ : ContDiffAt ℝ ∞ Γ (Z v)) (hZ : ContDiffAt ℝ ∞ Z v)
    (hP : ContDiffAt ℝ ∞ P v) (hi : (P v).IsInvertible) :
    ContDiffAt ℝ ∞ (coordinateFrameConnection Γ Z P) v := by
  let C := ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) (ComplexVector n)
  have hDP := hP.fderiv_right (m := ∞) (by simp)
  have hDZ := hZ.fderiv_right (m := ∞) (by simp)
  have hΓZ := hΓ.comp v hZ
  have hCf : ContDiff ℝ ∞ (fun A : ComplexVector n →L[ℝ] ComplexVector n => C.flip A) := by
    dsimp [C]
    fun_prop
  have hCP := hCf.contDiffAt.comp v hP
  have hPi := hi.contDiffAt_map_inverse.comp v hP
  exact (C.contDiff.contDiffAt.comp v hPi).clm_comp (hDP.add (hCP.clm_comp (hΓZ.clm_comp hDZ)))

def radialConnectionInChart (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (c : M.Carrier) (v : ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n :=
  coordinateFrameConnection (chartChristoffelBilin g.form c)
    (fun w => chartPt c (unitaryExponential g p U w)) (radialFrameCoordinates g p U c) v

def radialConnection (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n :=
  radialConnectionInChart g p U (unitaryExponential g p U v) v

theorem radialConnectionInChart_smoothAt (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (c : M.Carrier) (v : ComplexVector n)
    (hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source) :
    ContDiffAt ℝ ∞ (radialConnectionInChart g p U c) v := by
  letI := manifold_realSmooth M
  have hz : chartPt c (unitaryExponential g p U v) ∈ chartTarget c :=
    (extChartAt (ComplexModel n) c).map_source (by simpa only [extChartAt_source] using hc)
  apply coordinateFrameConnection_smoothAt
  · exact (chartChristoffelBilin_contDiffOn g c).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)
  · exact unitaryExponential_chart_smoothAt g p U c v hc
  · exact radialFrameCoordinates_smoothAt g p U c v hc
  · exact radialFrameCoordinates_invertible g p U c v hc

end Yau.Proofs.C04ChartsAux
