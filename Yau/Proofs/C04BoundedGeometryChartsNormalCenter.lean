import Yau.Proofs.C04BoundedGeometryChartsRadialIntegrals
import Yau.Proofs.C04BoundedGeometryChartsRadialJ
import Yau.LeafProofs.L21CayleyGraph

/-! Exact center normalization of the actual exponential coframe and pulled complex structure. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

@[simp] theorem radialCoframe_zero (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) :
    radialCoframe g p U 0 = ContinuousLinearMap.id ℝ (ComplexVector n) := by
  rw [radialCoframe_eq_radialIntegral g p U]
  simp only [C04Aux.radialIntegral, smul_zero, map_zero, zero_smul,
    intervalIntegral.integral_zero, add_zero]

@[simp] theorem radialConnection_zero (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j) : radialConnection g p U 0 = 0 := by
  rw [radialConnection_eq_radialIntegral g p U hU]
  simp only [C04Aux.radialIntegral, smul_zero, map_zero, zero_smul, intervalIntegral.integral_zero]

@[simp] theorem realPullbackJ_zero (g : SmoothMetric M) (hk : KahlerClosed g.form)
    (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p) :
    realPullbackJ (unitaryExponential g p U) 0 = Yau.LeafProofs.L21Aux.stdComplex n := by
  apply ContinuousLinearMap.ext
  intro w
  rw [realPullbackJ_eq_radial_conjugation g hk, radialCoframe_zero]
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.inverse_id,
    Yau.LeafProofs.L21Aux.stdComplex_apply]

end Yau.Proofs.C04ChartsAux
