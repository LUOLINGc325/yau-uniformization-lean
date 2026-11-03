import Yau.Proofs.C02NormalCurvatureIdentity
import Yau.Proofs.C02TensorMetricDual
import Yau.Proofs.C02TensorSlotConnection

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

theorem normalConnectionCurvature_eq_contraction (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (x : ComplexVector n) :
    normalConnectionCurvature g p U hU x = tensorMetricDualFour (ComplexVector n)
      (tensorSlotOperatorAll (ComplexVector n) (1 : Fin 4)
        (tensorSlotOperatorAll (ComplexVector n) (0 : Fin 4) (normalCurvatureJet g p U hU 0 x)
          (normalDifferential g p U hU x)) (normalDifferential g p U hU x)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_right ℝ
  intro z
  rw [normalConnectionCurvature_pairing, tensorMetricDualFour_pairing,
    tensorSlotOperatorAll_apply, tensorSlotOperatorAll_apply]
  congr 1
  funext i
  fin_cases i <;> simp

end Yau.Blueprint.C02Proof
