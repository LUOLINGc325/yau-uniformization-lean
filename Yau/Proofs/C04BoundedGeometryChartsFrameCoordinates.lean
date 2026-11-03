import Yau.Proofs.C04BoundedGeometryChartsFrameRegularity

/-! Smooth operator coordinates of the actual radial parallel frame. -/

noncomputable section
open scoped Topology Manifold ContDiff InnerProductSpace

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

def radialFrameCoordinates (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (c : M.Carrier)
    (v : ComplexVector n) : ComplexVector n →L[ℝ] ComplexVector n :=
  (realTangentCoords c (unitaryExponential g p U v)).comp
    (radialParallelFrame g p U v).toContinuousLinearMap

theorem radialFrameCoordinates_smoothAt (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (c : M.Carrier) (v₀ : ComplexVector n)
    (hc : unitaryExponential g p U v₀ ∈ (chartAt (ComplexVector n) c).source) :
    ContDiffAt ℝ ∞ (radialFrameCoordinates g p U c) v₀ := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let e₀ := realInitialOrthonormalFrame g p
  let α (i : Fin (2 * n)) : ComplexVector n →L[ℝ] ℝ :=
    (EuclideanSpace.proj i).comp
      (e₀.repr.toContinuousLinearMap.comp (realUnitaryFrame p U).toContinuousLinearMap)
  have H : ContDiffAt ℝ ∞
      (fun v => ∑ i : Fin (2 * n), (α i).smulRight
        (realTangentCoords c (unitaryExponential g p U v)
          (realParallelField g (radialInitialState p U v) (e₀ i) 1))) v₀ := by
    apply ContDiffAt.sum
    intro i _
    exact contDiffAt_const.smulRight (radialParallelCoordinates_smoothAt g p U (e₀ i) c v₀ hc)
  convert H using 1
  funext v
  apply ContinuousLinearMap.ext
  intro w
  change realTangentCoords c (unitaryExponential g p U v)
      (parallelUnitaryFrame g p U v 1 w) = _
  rw [parallelUnitaryFrame_expansion]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply]
  rfl

theorem radialFrameCoordinates_invertible (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (c : M.Carrier) (v : ComplexVector n)
    (hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source) :
    (radialFrameCoordinates g p U c v).IsInvertible := by
  let P := radialParallelFrame g p U v
  let Q := P.symm.toContinuousLinearMap.comp
    (realFrameCLM c (unitaryExponential g p U v))
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := Q)
  · apply ContinuousLinearMap.ext
    intro w
    change realTangentCoords c (unitaryExponential g p U v)
      (P (P.symm (realFrameCLM c (unitaryExponential g p U v) w))) = w
    rw [ContinuousLinearEquiv.apply_symm_apply, realTangentCoords_realFrameCLM _ _ hc]
  · apply ContinuousLinearMap.ext
    intro w
    change P.symm (realFrameCLM c (unitaryExponential g p U v)
      (realTangentCoords c (unitaryExponential g p U v) (P w))) = w
    rw [realFrameCLM_realTangentCoords _ _ hc, ContinuousLinearEquiv.symm_apply_apply]

end Yau.Proofs.C04ChartsAux
