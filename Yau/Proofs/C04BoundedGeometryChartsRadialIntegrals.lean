import Yau.Proofs.C04BoundedGeometryChartsCurvatureCurry
import Yau.Proofs.C04BoundedGeometryChartsRadialGauge
import Yau.Proofs.C04BoundedGeometryChartsParallelUniqueness
import Yau.Proofs.C04RadialGaugeIntegral
import Yau.Proofs.C04RadialIntegralJets

/-! The genuine connection and coframe are the same radial integral operators at every order. -/
noncomputable section
open MeasureTheory
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem radialCurvatureOperator_curried (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j) (v u w : ComplexVector n) :
    multilinearThreeCurry n (radialCurvatureOperator g p U v) u w =
      C04Aux.radialGaugeCurvature (radialConnection g p U) v u w := by
  apply ContinuousLinearMap.ext
  intro z
  rw [multilinearThreeCurry_apply, radialCurvatureOperator_apply g p U hU]
  rfl

theorem radialConnection_eq_radialIntegral (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j) :
    radialConnection g p U = C04Aux.radialIntegral
      (fun y => multilinearThreeCurry n (radialCurvatureOperator g p U y)) := by
  funext v
  apply ContinuousLinearMap.ext
  intro w
  have hO := (radialCurvatureOperator_smooth g p U hU).continuous
  have hc : Continuous (fun t : ℝ => t •
      multilinearThreeCurry n (radialCurvatureOperator g p U (t • v)) v) := by fun_prop
  have H := C04Aux.radial_connection_integral (radialConnection g p U)
    (radialConnection_smooth g p U) (R := ‖v‖ + 1) (by positivity)
    (fun x hx => radialConnection_radial g p U x) v
    (by simp only [Metric.mem_ball, dist_zero_right]; linarith) w
  change _ = (∫ t in (0 : ℝ)..1, t •
    multilinearThreeCurry n (radialCurvatureOperator g p U (t • v)) v) w
  rw [ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable 0 1) w]
  simpa only [smul_apply, radialCurvatureOperator_curried g p U hU] using H

theorem radialCoframe_eq_radialIntegral (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) :
    radialCoframe g p U = fun y => ContinuousLinearMap.id ℝ (ComplexVector n) +
      C04Aux.radialIntegral (fun y => (radialConnection g p U y).flip) y := by
  funext v
  apply ContinuousLinearMap.ext
  intro w
  have hω := (radialConnection_smooth g p U).continuous
  have hflip : Continuous (fun y => (radialConnection g p U y).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (ComplexVector n) (ComplexVector n) (ComplexVector n)).continuous.comp hω
  have hc : Continuous (fun t : ℝ => t • (radialConnection g p U (t • v)).flip v) :=
    continuous_id.smul ((hflip.comp (continuous_id.smul continuous_const)).clm_apply continuous_const)
  have H := C04Aux.radial_coframe_integral (radialConnection g p U) (radialCoframe g p U)
    (radialConnection_smooth g p U) (radialCoframe_smooth g p U)
    (R := ‖v‖ + 1) (by positivity) (fun x hx => radialConnection_radial g p U x)
    (fun x hx => radialCoframe_radial g p U x)
    (fun x hx u w => radialCoframe_torsion g p U x u w) v
    (by simp only [Metric.mem_ball, dist_zero_right]; linarith) w
  change _ = w + (∫ t in (0 : ℝ)..1, t • (radialConnection g p U (t • v)).flip v) w
  rw [ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable 0 1) w]
  exact H

end Yau.Proofs.C04ChartsAux
