import Yau.LeafProofs.L23FieldMetricParallelPairing

/-! Genuine finite dimensional fiber equivalences of injective physical frames. -/
noncomputable section
open Filter Bundle
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

def realFrameEquiv (y : M.Carrier) :
    ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) y := by
  letI := manifold_realSmooth M
  exact ((trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) y).continuousLinearEquivAt
    ℝ y (mem_chart_source _ _)).symm

theorem realFrameEquiv_toContinuousLinearMap (y : M.Carrier) :
    (realFrameEquiv y).toContinuousLinearMap = realFrameCLM y y := by
  letI := manifold_realSmooth M
  exact Trivialization.symm_continuousLinearEquivAt_eq'
    (trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) y) (mem_chart_source _ _)

theorem physical_frame_pairing_injective (h : HermitianField M) (a y : M.Carrier)
    (R : ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) y)
    (H : ∀ v w : ComplexVector n,
      (underlyingRealRiemannianMetric h).inner y (R v) (R w) =
        realMetricInChart h a (chartPt a a) v w) : Function.Injective R := by
  intro v w hvw
  apply sub_eq_zero.mp
  apply (realMetricInChart_quadratic_eq_zero_iff h a a (mem_chart_source _ _) (v-w)).mp
  have HQ := H (v-w) (v-w)
  rw [map_sub,hvw,sub_self] at HQ
  simpa only [map_zero,ContinuousLinearMap.zero_apply] using HQ.symm

def frameEquivOfInjective (y : M.Carrier)
    (R : ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) y)
    (hR : Function.Injective R) :
    ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) y := by
  let C := (realTangentCoords y y).comp R
  have hC : Function.Injective C := by
    intro v w hEq
    apply hR
    have H := congrArg (realFrameCLM y y) hEq
    simpa only [C,ContinuousLinearMap.comp_apply,realFrameCLM_realTangentCoords y y (mem_chart_source _ _)] using H
  exact ((LinearEquiv.ofInjectiveEndo C.toLinearMap hC).toContinuousLinearEquiv).trans (realFrameEquiv y)

theorem frameEquivOfInjective_toContinuousLinearMap (y : M.Carrier)
    (R : ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) y)
    (hR : Function.Injective R) : (frameEquivOfInjective y R hR).toContinuousLinearMap = R := by
  ext v
  change realFrameEquiv y (realTangentCoords y y (R v)) = R v
  rw [← ContinuousLinearEquiv.coe_coe,realFrameEquiv_toContinuousLinearMap]
  exact realFrameCLM_realTangentCoords y y (mem_chart_source _ _) (R v)

end Yau.LeafProofs.L23Aux
