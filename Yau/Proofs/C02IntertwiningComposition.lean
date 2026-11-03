import Yau.Proofs.C02ComplexDifferential

/-! Actual real differentials intertwining through the same intermediate
complex structure yield the complex differential of the composite. -/

noncomputable section
namespace Yau.Blueprint.C02Proof
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem complex_differentiableAt_of_intertwining_composition
    {N : E → F} {G : E → E} {z : E}
    (hN : DifferentiableAt ℝ N (G z)) (hG : DifferentiableAt ℝ G z)
    (J : E →L[ℝ] E)
    (hOuter : ∀ v, fderiv ℝ N (G z) (J v) = Complex.I • fderiv ℝ N (G z) v)
    (hInner : ∀ v, fderiv ℝ G z (Complex.I • v) = J (fderiv ℝ G z v)) :
    DifferentiableAt ℂ (N ∘ G) z := by
  apply (hasComplexFDerivAt_of_real_commutes_I (hN.comp z hG) ?_).differentiableAt
  intro v
  rw [fderiv_comp z hN hG, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    hInner, hOuter]

theorem inverse_differential_intertwines
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L J : E →L[ℝ] E) (hL : L.IsInvertible)
    (hForward : ∀ v, L (J v) = Complex.I • L v) (v : E) :
    L.inverse (Complex.I • v) = J (L.inverse v) := by
  apply hL.injective
  rw [hL.self_apply_inverse, hForward, hL.self_apply_inverse]

end Yau.Blueprint.C02Proof
