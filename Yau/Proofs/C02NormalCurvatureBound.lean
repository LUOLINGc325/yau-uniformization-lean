import Yau.Proofs.C02NormalCurvatureIdentity
import Yau.Proofs.C02TensorCurvatureNorm
import Yau.Proofs.C02CurvatureGaugeNorm

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

local instance curvature_bound_end_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance curvature_bound_end_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance curvature_bound_one_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance curvature_bound_one_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance curvature_bound_two_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance curvature_bound_two_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

theorem normalConnectionCurvature_norm_le (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (x : ComplexVector n) :
    ‖normalConnectionCurvature g p U hU x‖ ≤
      curvatureJetNorm g.form 0 (normalRealMap g p U x) * ‖normalDifferential g p U hU x‖ ^ 2 := by
  have h := curvature_action_norm_le (normalConnectionCurvature g p U hU x)
    (normalCurvatureJet g p U hU 0 x) (normalDifferential g p U hU x)
    (normalConnectionCurvature_pairing g p U hU x)
  exact h.trans (mul_le_mul_of_nonneg_right (normalCurvatureJet_norm_le g p U hU 0 x) (sq_nonneg _))

end Yau.Blueprint.C02Proof
