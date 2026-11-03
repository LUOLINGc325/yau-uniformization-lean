import Yau.Proofs.C04BoundedGeometryChartsTensorFrameDerivative
import Yau.Proofs.C04BoundedGeometryChartsCurvatureForms
import Yau.Proofs.C04BoundedGeometryChartsRadialTorsion

/-! Ordinary derivatives of the same actual radial curvature jets are covariant derivatives
plus the explicit connection action in each tensor slot. -/

noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

theorem radialCurvatureForm_fderiv (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (m : ℕ) (v u : ComplexVector n)
    (V : Fin (4 + m) → ComplexVector n) :
    fderiv ℝ (radialCurvatureForm g p U m) v u V =
      radialCurvatureForm g p U (m + 1) v (Fin.cons (radialCoframe g p U v u) V) +
        ∑ s : Fin (4 + m), radialCurvatureForm g p U m v
          (Function.update V s (radialConnection g p U v u (V s))) := by
  letI := manifold_realSmooth M
  let c := unitaryExponential g p U v
  let Z := fun x => chartPt c (unitaryExponential g p U x)
  let P := radialFrameCoordinates g p U c
  let F := fun y => tensorEvalCLM (rmJet g.form c m y)
  let N := tensorEvalCLM (rmJet g.form c (m + 1) (Z v))
  have hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  have hz : Z v ∈ chartTarget c := mem_extChartAt_target c
  have hF : DifferentiableAt ℝ F (Z v) :=
    ((tensorEvalCLM_contDiffOn (rmJet g.form c m)
      (rmJet_contDiffOn g.form (metricSmooth_of_smoothMetric g) c m)).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hZ := (unitaryExponential_chart_smoothAt g p U c v hc).differentiableAt (by simp)
  have hP := (radialFrameCoordinates_smoothAt g p U c v hc).differentiableAt (by simp)
  have hN (a : ComplexVector n) : N.curryLeft a =
      fderiv ℝ F (Z v) a - tensorConnectionForm (chartChristoffelBilin g.form c (Z v)) (F (Z v)) a := by
    change (tensorEvalCLM (covariantD g.form c (rmJet g.form c m) (Z v))).curryLeft a = _
    exact tensorEvalCLM_covariantD g.form c (rmJet g.form c m) (Z v) a (by
      intro idx
      exact ((rmJet_contDiffOn g.form (metricSmooth_of_smoothMetric g) c m idx).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp))
  have heq : radialCurvatureForm g p U m =ᶠ[𝓝 v]
      (fun x => (F (Z x)).compContinuousLinearMap (fun _ : Fin (4 + m) => P x)) := by
    filter_upwards [(unitaryExponential_smooth g p U).continuous.continuousAt.preimage_mem_nhds
      ((chartAt (ComplexVector n) c).open_source.mem_nhds hc)] with x hx
    exact radialCurvatureForm_in_chart g p U m c x hx
  have hform (W : Fin (4 + m) → ComplexVector n) :
      radialCurvatureForm g p U m v W = F (Z v) (fun j => P v (W j)) := by
    rw [radialCurvatureForm_in_chart g p U m c v hc,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hPA : P v (radialCoframe g p U v u) = fderiv ℝ Z v u :=
    congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L u)
      (radialFrameCoordinates_comp_coframe g p U c v hc)
  have hnext : radialCurvatureForm g p U (m + 1) v
      (Fin.cons (radialCoframe g p U v u) V) =
        N (Fin.cons (fderiv ℝ Z v u) (fun j => P v (V j))) := by
    rw [radialCurvatureForm_in_chart g p U (m + 1) c v hc,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact hPA
    · rfl
  have hslot (s : Fin (4 + m)) : radialCurvatureForm g p U m v
      (Function.update V s (radialConnection g p U v u (V s))) =
      F (Z v) (Function.update (fun j => P v (V j)) s
        (P v (radialConnection g p U v u (V s)))) := by
    rw [hform, linearMap_map_update]
  rw [heq.fderiv_eq]
  have H := tensorForm_movingFrame_covariantD (chartChristoffelBilin g.form c) F N Z P v u V
    hF hZ hP (radialFrameCoordinates_invertible g p U c v hc) hN
  change _ = N (Fin.cons (fderiv ℝ Z v u) (fun j => P v (V j))) +
    ∑ s : Fin (4 + m), F (Z v) (Function.update (fun j => P v (V j)) s
      (P v (radialConnection g p U v u (V s)))) at H
  rw [H, ← hnext]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  exact (hslot s).symm

end Yau.Proofs.C04ChartsAux
