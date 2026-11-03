import Yau.Proofs.C04BoundedGeometryChartsFrameConnection
import Yau.Proofs.C04BoundedGeometryChartsTransportScale
import Yau.Proofs.C04BoundedGeometryChartsUniformJacobi

/-! Radial gauge is satisfied by the actual parallel frame, rather than supplied as data. -/

noncomputable section
open Filter
open scoped Topology Manifold ContDiff InnerProductSpace

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

theorem realParallelField_scaled_coordinates (g : SmoothMetric M) (p c : M.Carrier)
    (v w : TangentSpace 𝓘(ℝ, ComplexVector n) p) (t : ℝ) :
    realTangentCoords c
        (realGeodesicFlow g (⟨p, t • v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) 1).proj
        (realParallelField g (⟨p, t • v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) w 1) =
      realTangentCoords c
        (realGeodesicFlow g (⟨p, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) t).proj
        (realParallelField g (⟨p, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) w t) := by
  have H := (realParallelField_totalSpace g
      (⟨p, t • v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) w 1).trans
    ((realParallelLift_scaled_velocity g p v w t).trans
      (realParallelField_totalSpace g
        (⟨p, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) w t).symm)
  exact congrArg (fun q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier =>
    realTangentCoords c q.proj q.2) H

theorem radialFrameCoordinates_scaled (g : SmoothMetric M) (p c : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v w : ComplexVector n) (t : ℝ) :
    radialFrameCoordinates g p U c (t • v) w =
      realTangentCoords c (realGeodesicFlow g (radialInitialState p U v) t).proj
        (parallelUnitaryFrame g p U v t w) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  change realTangentCoords c (unitaryExponential g p U (t • v))
    (parallelUnitaryFrame g p U (t • v) 1 w) = _
  rw [parallelUnitaryFrame_expansion, parallelUnitaryFrame_expansion]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hstate : radialInitialState p U (t • v) =
      (⟨p, t • realUnitaryFrame p U v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := by
    exact congrArg (fun z => (⟨p, z⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier))
      ((realUnitaryFrame p U).map_smul t v)
  change realTangentCoords c (realGeodesicFlow g (radialInitialState p U (t • v)) 1).proj
    (realParallelField g (radialInitialState p U (t • v)) (realInitialOrthonormalFrame g p i) 1) = _
  rw [hstate]
  exact realParallelField_scaled_coordinates g p c (realUnitaryFrame p U v)
    (realInitialOrthonormalFrame g p i) t

theorem radialFrameCoordinates_radial_fderiv (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v w : ComplexVector n) :
    let c := unitaryExponential g p U v
    fderiv ℝ (radialFrameCoordinates g p U c) v v w =
      -chartChristoffelBilin g.form c (chartPt c c)
        (realTangentCoords c c (realGeodesicFlow g (radialInitialState p U v) 1).2)
        (radialFrameCoordinates g p U c v w) := by
  dsimp only
  letI : NormedAddCommGroup (ComplexVector n) := inferInstance
  letI : NormedSpace ℝ (ComplexVector n) := inferInstance
  let c := unitaryExponential g p U v
  have hP := radialFrameCoordinates_smoothAt g p U c v (mem_chart_source _ _)
  have hline := (hasDerivAt_id (1 : ℝ)).smul_const v
  have HD : HasFDerivAt (fun z => radialFrameCoordinates g p U c z w)
      ((fderiv ℝ (radialFrameCoordinates g p U c) v).flip w) ((1 : ℝ) • v) := by
    simpa only [one_smul, ContinuousLinearMap.comp_zero, zero_add] using
      (hP.differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const w v)
  have H := HD.comp_hasDerivAt 1 hline
  have H' := parallelUnitaryFrame_coordinates_hasDerivAt g p U v w 1
  have HR := H'.congr_of_eventuallyEq (Eventually.of_forall
    (fun t => radialFrameCoordinates_scaled g p c U v w t))
  have heq := H.unique HR
  simpa only [one_smul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply,
    parallelUnitaryFrame_one, radialFrameCoordinates, ContinuousLinearEquiv.coe_coe,
    c, unitaryExponential, realExponentialMap, radialInitialState] using heq

theorem unitaryExponential_chart_radial_fderiv (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) :
    let c := unitaryExponential g p U v
    fderiv ℝ (fun w => chartPt c (unitaryExponential g p U w)) v v =
      realTangentCoords c c (realGeodesicFlow g (radialInitialState p U v) 1).2 := by
  dsimp only
  letI : NormedAddCommGroup (ComplexVector n) := inferInstance
  letI : NormedSpace ℝ (ComplexVector n) := inferInstance
  letI := manifold_realSmooth M
  let c := unitaryExponential g p U v
  have hZ := unitaryExponential_chart_smoothAt g p U c v (mem_chart_source _ _)
  have hline := (hasDerivAt_id (1 : ℝ)).smul_const v
  have HD : HasFDerivAt (fun w => chartPt c (unitaryExponential g p U w))
      (fderiv ℝ (fun w => chartPt c (unitaryExponential g p U w)) v) ((1 : ℝ) • v) := by
    simpa only [one_smul] using (hZ.differentiableAt (by simp)).hasFDerivAt
  have H := HD.comp_hasDerivAt 1 hline
  have H' := realGeodesicFlow_baseCoords_hasDerivAt g (radialInitialState p U v) 1
  have heq : (fun t => chartPt c (unitaryExponential g p U (t • v))) =
      (fun t => chartPt c (realGeodesicFlow g (radialInitialState p U v) t).proj) := by
    funext t
    rw [unitaryExponential_radial_flow]
  simp only [Function.comp_def, id_eq] at H
  rw [heq] at H
  simpa only [one_smul, c, unitaryExponential, realExponentialMap, radialInitialState] using H.unique H'

theorem radialConnection_radial (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) :
    radialConnection g p U v v = 0 := by
  apply ContinuousLinearMap.ext
  intro w
  rw [radialConnection, radialConnectionInChart, coordinateFrameConnection_apply,
    radialFrameCoordinates_radial_fderiv, unitaryExponential_chart_radial_fderiv]
  simp only [neg_add_cancel, map_zero, ContinuousLinearMap.zero_apply]

end Yau.Proofs.C04ChartsAux
