import Yau.Proofs.C04BoundedGeometryChartsCurvatureSmooth

/-! The intrinsic curvature jets as actual smooth multilinear forms in the radial frame. -/

noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

def radialCurvatureForm (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (m : ℕ) (v : ComplexVector n) :
    RealTensorForm n (4 + m) := tensorEvalCLM (radialCurvatureCoefficients g p U m v)

theorem radialCurvatureForm_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (m : ℕ) :
    ContDiff ℝ ∞ (radialCurvatureForm g p U m) :=
  tensorEvalCLMMap.contDiff.comp (radialCurvatureCoefficients_smooth g p U m)

theorem radialCurvatureForm_in_chart (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (m : ℕ) (c : M.Carrier)
    (v : ComplexVector n)
    (hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source) :
    radialCurvatureForm g p U m v =
      (tensorEvalCLM (rmJet g.form c m (chartPt c (unitaryExponential g p U v)))).compContinuousLinearMap
        (fun _ => radialFrameCoordinates g p U c v) := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin (4 + m) => realVec_basis n)
  intro idx
  change radialCurvatureForm g p U m v (fun j => realVec_basis n (idx j)) =
    ((tensorEvalCLM (rmJet g.form c m (chartPt c (unitaryExponential g p U v)))).compContinuousLinearMap
      (fun _ => radialFrameCoordinates g p U c v)) (fun j => realVec_basis n (idx j))
  simp only [realVec_basis_apply, radialCurvatureForm]
  rw [tensorEvalCLM_basis, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    tensorEvalCLM_eq_tensorEvaluation]
  exact radialCurvatureCoefficients_in_chart g p U m c v hc idx

theorem radialCurvatureForm_norm_le (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j)
    (m : ℕ) (v : ComplexVector n) {K : ℝ} (hK : 0 ≤ K)
    (hcurv : curvatureJetNorm g.form m (unitaryExponential g p U v) ≤ K) :
    ‖radialCurvatureForm g p U m v‖ ≤
      ‖tensorEvalCLMMap (n := n) (r := 4 + m)‖ * (K * Real.sqrt 2 ^ (4 + m)) := by
  have hb : 0 ≤ K * Real.sqrt 2 ^ (4 + m) := mul_nonneg hK (pow_nonneg (Real.sqrt_nonneg 2) _)
  have hcoeff : ‖radialCurvatureCoefficients g p U m v‖ ≤ K * Real.sqrt 2 ^ (4 + m) := by
    apply (pi_norm_le_iff_of_nonneg hb).mpr
    intro idx
    exact radialCurvatureCoefficients_abs_le g p U hU m v hK hcurv idx
  exact (tensorEvalCLMMap.le_opNorm _).trans (mul_le_mul_of_nonneg_left hcoeff (norm_nonneg _))

end Yau.Proofs.C04ChartsAux
