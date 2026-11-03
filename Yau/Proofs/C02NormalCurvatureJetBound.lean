import Yau.Proofs.C02NormalCurvatureContraction
import Yau.Proofs.C02BilinearJetBound
import Yau.Proofs.C02JetProductBounds
import Yau.Proofs.C02TensorCurvatureJets

/-! All derivatives of the actual connection curvature obey the exact
double binomial product estimate. Its two highest differential terms
therefore have coefficient one each. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}
local instance normal_fj_end_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance normal_fj_end_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance normal_fj_one_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance normal_fj_one_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance normal_fj_two_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance normal_fj_two_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

theorem normalConnectionCurvature_jet_norm_le (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (m : ℕ) (x : ComplexVector n) :
    ‖iteratedFDeriv ℝ m (normalConnectionCurvature g p U hU) x‖ ≤
      binomialJetProduct (binomialJetProduct
        (fun i => ‖iteratedFDeriv ℝ i (normalCurvatureJet g p U hU 0) x‖)
        (fun i => ‖iteratedFDeriv ℝ i (normalDifferential g p U hU) x‖))
        (fun i => ‖iteratedFDeriv ℝ i (normalDifferential g p U hU) x‖) m := by
  have heq : normalConnectionCurvature g p U hU = fun y => tensorMetricDualFour (ComplexVector n)
      (tensorSlotOperatorAll (ComplexVector n) (1 : Fin 4)
        (tensorSlotOperatorAll (ComplexVector n) (0 : Fin 4) (normalCurvatureJet g p U hU 0 y)
          (normalDifferential g p U hU y)) (normalDifferential g p U hU y)) :=
    funext (normalConnectionCurvature_eq_contraction g p U hU)
  rw [heq]
  exact tensorCurvature_jet_norm_le (normalCurvatureJet g p U hU 0) (normalDifferential g p U hU)
    (normalCurvatureJet_smooth g p U hU 0) (normalDifferential_smooth g p U hU) m x

end Yau.Blueprint.C02Proof
