import Yau.Proofs.C02RealPullbackComposition

/-! Nonsingularity of the corrected chart is the nonsingularity of the
two actual differentials, transferred through the canonical real tangent map. -/

noncomputable section
open scoped Manifold InnerProductSpace
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normal_composition_complex_differential_bijective
    (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    {G : ComplexVector n → ComplexVector n} {z : ComplexVector n}
    (hG : DifferentiableAt ℝ G z) (hDG : (fderiv ℝ G z).IsInvertible)
    (hΦ : MDifferentiableAt 𝓘(ℂ, ComplexVector n) (ComplexModel n)
      (normalRealMap g p U ∘ G) z)
    (hB : ‖normalDifferential g p U hU (G z) -
      ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ 1 / 4) :
    Function.Bijective (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n)
      (normalRealMap g p U ∘ G) z) := by
  let := manifold_realSmooth M
  have hN := (normalRealMap_smooth g p U hU).mdifferentiableAt (by simp) (x := G z)
  have hReal : Function.Bijective (realCoordinateDifferential (normalRealMap g p U ∘ G) z) := by
    rw [realCoordinateDifferential_comp hN hG]
    exact (rawNormalDifferential_bijective_of_close_identity g p U hU (G z) hB).comp hDG.bijective
  have hEq : (fun v => realTangentEquiv ((normalRealMap g p U ∘ G) z)
      (realCoordinateDifferential (normalRealMap g p U ∘ G) z v)) =
      mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) (normalRealMap g p U ∘ G) z :=
    funext (realCoordinateDifferential_eq_complex hΦ)
  rw [← hEq]
  exact (realTangentEquiv _).bijective.comp hReal

theorem smul_isInvertible_of_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E) (hL : L.IsInvertible) {a : ℝ} (ha : a ≠ 0) :
    (a • L).IsInvertible := by
  obtain ⟨e, he⟩ := hL
  refine ⟨(Units.mk0 a ha) • e, ?_⟩
  ext v
  change a • e v = a • L v
  exact congrArg (fun K : E →L[ℝ] E => a • K v) he

theorem normalized_inverse_operator_isInvertible
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D D0 : E →L[ℝ] E) (hD : D.IsInvertible) (hD0 : D0.IsInvertible) :
    (Real.sqrt (2 : ℝ) • D.inverse.comp D0).IsInvertible := by
  exact smul_isInvertible_of_ne_zero _ (hD.inverse.comp hD0)
    (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

end Yau.Blueprint.C02Proof
