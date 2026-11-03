import Yau.Proofs.C02RealPullbackComposition
import Yau.Proofs.C02PullbackMatrixBounds

/-! The numerical Hermitian comparison constants concern the actual
composed chart and the same original Hermitian field. -/

noncomputable section
open scoped Manifold InnerProductSpace Matrix ComplexOrder
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

theorem normal_composition_pullback_bounds
    (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    {G : ComplexVector n → ComplexVector n} {z : ComplexVector n}
    (hG : DifferentiableAt ℝ G z)
    (hΦ : MDifferentiableAt 𝓘(ℂ, ComplexVector n) (ComplexModel n)
      (normalRealMap g p U ∘ G) z)
    (hB : ‖normalDifferential g p U hU (G z) -
      ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ 1 / 4)
    (hLower : ∀ v, (1 / 3 : ℝ) * ‖v‖ ≤ ‖fderiv ℝ G z v‖)
    (hUpper : ∀ v, ‖fderiv ℝ G z v‖ ≤ 6 * ‖v‖) :
    HermLE (((1 / 128 : ℝ) : ℂ) • (1 : Herm n))
      (pullbackMat g.form (normalRealMap g p U ∘ G) z) ∧
    HermLE (pullbackMat g.form (normalRealMap g p U ∘ G) z)
      ((64 : ℂ) • (1 : Herm n)) := by
  apply pullbackMat_bounds_of_quadratic
  · intro v
    have hMetric := normalGaugeMetric_bounds_of_close_identity g p U hU (G z) hB
      (fderiv ℝ G z v)
    have hPhysical := realPullbackMetric_eq_two_re g.form hΦ v v
    rw [realPullbackMetric_normal_composition g p U hU hG] at hPhysical
    have hSquare := mul_self_le_mul_self
      (by positivity : (0 : ℝ) ≤ (1 / 3) * ‖v‖) (hLower v)
    change (1 / 128 : ℝ) * ‖v‖ ^ 2 ≤
      ((g.form ((normalRealMap g p U ∘ G) z)).toFun _ _).re
    nlinarith [sq_nonneg ‖v‖]
  · intro v
    have hMetric := normalGaugeMetric_bounds_of_close_identity g p U hU (G z) hB
      (fderiv ℝ G z v)
    have hPhysical := realPullbackMetric_eq_two_re g.form hΦ v v
    rw [realPullbackMetric_normal_composition g p U hU hG] at hPhysical
    have hSquare := mul_self_le_mul_self (norm_nonneg (fderiv ℝ G z v)) (hUpper v)
    change ((g.form ((normalRealMap g p U ∘ G) z)).toFun _ _).re ≤ 64 * ‖v‖ ^ 2
    nlinarith [sq_nonneg ‖v‖]

end Yau.Blueprint.C02Proof
