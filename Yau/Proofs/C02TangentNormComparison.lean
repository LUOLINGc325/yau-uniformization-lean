import Yau.LeafProofs.L12

/-! Intrinsic quadratic-form comparison gives comparison of the actual
real tangent norms, with both metric instances explicit. -/

noncomputable section
open scoped Manifold
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem realTangentNorm_le_of_quadratic_comparison
    (h₀ h₁ : HermitianField M) (x : M.Carrier) (C : ℝ) (hC : 0 ≤ C)
    (hCompare : ∀ v : TangentVector M x,
      hermitianNormSq (h₀ x) v ≤ C ^ 2 * hermitianNormSq (h₁ x) v)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    @norm _ (underlyingRealTangentNormedAddCommGroup h₀ x).toNorm v ≤
      C * @norm _ (underlyingRealTangentNormedAddCommGroup h₁ x).toNorm v := by
  rw [underlyingRealTangent_norm, underlyingRealTangent_norm]
  calc
    _ ≤ Real.sqrt (C ^ 2 * (2 * hermitianNormSq (h₁ x) (realTangentEquiv x v))) :=
      Real.sqrt_le_sqrt (by nlinarith [hCompare (realTangentEquiv x v)])
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]

end Yau.Blueprint.C02Proof
