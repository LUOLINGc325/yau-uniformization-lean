import Yau.Proofs.C02NormalCurvatureBound
import Yau.Proofs.C02RadialLowOrder
import Yau.Proofs.C02RadialConstants
import Yau.Proofs.C02OperatorInverse

/-! The fixed curvature radius controls the actual normal differential.
The temporary first-exit bound is discharged by its actual radial homotopies. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

theorem normalGauge_low_order (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    {K : ℝ} (hK : 0 ≤ K)
    (hRm : ∀ q, inducedDistance g.form p q ≤ 1 → curvatureJetNorm g.form 0 q ≤ K)
    (x : ComplexVector n) (hx : ‖x‖ ≤ radialGaugeRadius K) :
    ‖normalDifferential g p U hU x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ 9 / 256 ∧
      ‖normalDifferential g p U hU x‖ ≤ 3 / 2 := by
  apply radial_low_order_bootstrap (normalConnection g p U hU) (normalDifferential g p U hU)
    (normalConnectionCurvature g p U hU) (normalDifferential_smooth g p U hU).continuous
    (normalDifferential_zero g p U hU) (normalConnection_homotopy g p U hU)
    (normalDifferential_homotopy g p U hU) (radialGaugeRadius_pos hK).le hK
    (curvature_mul_radialGaugeRadius_sq hK) ?_ x hx
  intro y hy
  have hDist : inducedDistance g.form p (normalRealMap g p U y) ≤ 1 :=
    (normalRealMap_distance_le g p U hU y).trans
      (hy.trans ((radialGaugeRadius_le_quarter hK).trans (by norm_num)))
  exact (normalConnectionCurvature_norm_le g p U hU y).trans
    (mul_le_mul_of_nonneg_right (hRm _ hDist) (sq_nonneg _))

theorem normalGauge_inverse_bound (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    {K : ℝ} (hK : 0 ≤ K)
    (hRm : ∀ q, inducedDistance g.form p q ≤ 1 → curvatureJetNorm g.form 0 q ≤ K)
    (x : ComplexVector n) (hx : ‖x‖ ≤ radialGaugeRadius K) :
    ∃ V : ComplexVector n →L[ℝ] ComplexVector n,
      V.comp (normalDifferential g p U hU x) = ContinuousLinearMap.id ℝ (ComplexVector n) ∧
      (normalDifferential g p U hU x).comp V = ContinuousLinearMap.id ℝ (ComplexVector n) ∧ ‖V‖ ≤ 2 := by
  apply exists_bounded_inverse_of_close_identity
  exact (normalGauge_low_order g p U hU hK hRm x hx).1.trans (by norm_num)

theorem normalGauge_rawDifferential_bijective (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    {K : ℝ} (hK : 0 ≤ K)
    (hRm : ∀ q, inducedDistance g.form p q ≤ 1 → curvatureJetNorm g.form 0 q ≤ K)
    (x : ComplexVector n) (hx : ‖x‖ ≤ radialGaugeRadius K) :
    Function.Bijective (rawNormalDifferential g p U x) := by
  apply rawNormalDifferential_bijective_of_close_identity
  exact (normalGauge_low_order g p U hU hK hRm x hx).1.trans (by norm_num)

end Yau.Blueprint.C02Proof
