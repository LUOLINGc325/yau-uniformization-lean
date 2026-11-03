import Yau.Proofs.C02HermitianRealPullback
import Yau.Proofs.C02NormalPullbackMetric

/-! The physical pullback metric of a composed chart is computed using
the actual normal metric and the actual source differential. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem realCoordinateDifferential_comp
    {N : ComplexVector n → M.Carrier} {G : ComplexVector n → ComplexVector n}
    {z : ComplexVector n}
    (hN : MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) N (G z))
    (hG : DifferentiableAt ℝ G z) :
    realCoordinateDifferential (N ∘ G) z =
      (realCoordinateDifferential N (G z)).comp (fderiv ℝ G z) := by
  let := manifold_realSmooth M
  apply ContinuousLinearMap.ext
  intro u
  change (mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) (N ∘ G) z)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm u) = _
  rw [mfderiv_comp z hN hG.mdifferentiableAt]
  change (mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) N (G z))
      ((mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) G z)
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm u)) = _
  rw [mfderiv_eq_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem realPullbackMetric_normal_composition (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    {G : ComplexVector n → ComplexVector n} {z : ComplexVector n}
    (hG : DifferentiableAt ℝ G z) (u v : ComplexVector n) :
    realPullbackMetric g.form (normalRealMap g p U ∘ G) z u v =
      normalGaugeMetric g p U hU (G z) (fderiv ℝ G z u) (fderiv ℝ G z v) := by
  let := manifold_realSmooth M
  have hN := (normalRealMap_smooth g p U hU).mdifferentiableAt (by simp) (x := G z)
  unfold realPullbackMetric
  rw [realCoordinateDifferential_comp hN hG]
  exact (normalGaugeMetric_eq_pullback g p U hU (G z) (fderiv ℝ G z u) (fderiv ℝ G z v)).symm

end Yau.Blueprint.C02Proof
