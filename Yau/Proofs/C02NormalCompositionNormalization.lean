import Yau.Proofs.C02RealPullbackComposition
import Yau.Proofs.C02NormalDifferentialRadial

/-! At the centre, the physical sqrt(2) normalization recovers exactly
the identity Hermitian matrix in the original contract. -/

noncomputable section
open scoped Manifold InnerProductSpace Matrix
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

theorem complexVector_real_inner (u v : ComplexVector n) :
    ⟪u, v⟫_ℝ = (⟪u, v⟫_ℂ).re := by
  change (∑ i, (v i * star (u i)).re) = (∑ i, v i * star (u i)).re
  exact (map_sum Complex.reCLM (fun i : Fin n => v i * star (u i)) Finset.univ).symm

theorem normal_composition_real_metric_zero
    (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    {G : ComplexVector n → ComplexVector n} (hG0 : G 0 = 0)
    (hG : HasFDerivAt G (Real.sqrt (2 : ℝ) • ContinuousLinearMap.id ℝ (ComplexVector n)) 0)
    (u v : ComplexVector n) :
    realPullbackMetric g.form (normalRealMap g p U ∘ G) 0 u v = 2 * ⟪u, v⟫_ℝ := by
  rw [realPullbackMetric_normal_composition g p U hU hG.differentiableAt,
    hG0, normalGaugeMetric_apply, normalDifferential_zero, hG.fderiv]
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply,
    real_inner_smul_left, real_inner_smul_right]
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem normal_composition_pullback_zero
    (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    {G : ComplexVector n → ComplexVector n} (hG0 : G 0 = 0)
    (hG : HasFDerivAt G (Real.sqrt (2 : ℝ) • ContinuousLinearMap.id ℝ (ComplexVector n)) 0)
    (hΦ : MDifferentiableAt 𝓘(ℂ, ComplexVector n) (ComplexModel n)
      (normalRealMap g p U ∘ G) 0) :
    pullbackMat g.form (normalRealMap g p U ∘ G) 0 = 1 := by
  ext a b
  rw [pullbackMat_eq_real_metric_coefficients g.form hΦ,
    normal_composition_real_metric_zero g p U hU hG0 hG,
    normal_composition_real_metric_zero g p U hU hG0 hG]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  change (((1 / 2 : ℝ) * (2 * ⟪stdVec a, stdVec b⟫_ℝ) : ℝ) : ℂ) +
    Complex.I * (((1 / 2 : ℝ) * (2 * ⟪Complex.I • stdVec a, stdVec b⟫_ℝ) : ℝ) : ℂ) =
      if a = b then 1 else 0
  rw [complexVector_real_inner, complexVector_real_inner, inner_smul_left]
  have hStd : ⟪stdVec a, stdVec b⟫_ℂ = if a = b then 1 else 0 := by
    simp [stdVec, EuclideanSpace.inner_single_left]
  rw [hStd]
  split_ifs <;> norm_num

end Yau.Blueprint.C02Proof
