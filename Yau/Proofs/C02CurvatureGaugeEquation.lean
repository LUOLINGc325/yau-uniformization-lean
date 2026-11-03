import Yau.Proofs.C02CurvatureGaugeDerivative
import Yau.Proofs.C02TensorHeadOperator
import Yau.Proofs.C02TensorSlotConnection

/-! The actual covariant-jet differential identity as an equality of
bounded operators, with each contraction represented by a fixed map of
norm at most one. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

theorem normalCurvatureJet_fderiv_equation (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (j : ℕ) (x : ComplexVector n) :
    fderiv ℝ (normalCurvatureJet g p U hU j) x =
      tensorHeadOperator (ComplexVector n) (normalCurvatureJet g p U hU (j + 1) x)
        (normalDifferential g p U hU x) +
      ∑ s : Fin (4 + j), tensorSlotConnectionOperator (ComplexVector n) s
        (normalCurvatureJet g p U hU j x) (normalConnection g p U hU x) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousMultilinearMap.ext
  intro V
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply, sum_apply,
    tensorHeadOperator_apply, tensorSlotConnectionOperator_apply]
  exact normalCurvatureJet_fderiv g p U hU j x u V

end Yau.Blueprint.C02Proof
