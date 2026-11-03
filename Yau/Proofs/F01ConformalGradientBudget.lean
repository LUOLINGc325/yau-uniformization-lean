import Yau.Proofs.F01ConformalGradientBound

/-! A prescribed profile budget works on every manifold and restricted
sublevel; its constant can therefore be selected before all those domains. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem conformalScalar_gradient_bound_of_weighted_first
    (g : HermitianField M) (u : M.Carrier → ℝ) (hu : SmoothFn u)
    {B C L : ℝ} (hL : 0 < L) (x : M.Carrier) (hx : u x < L)
    (hgrad : gradNormSq g u x ≤ C ^ 2)
    (hprofile : Real.exp (-conformalProfile (u x / L) / 2) *
      |deriv conformalProfile (u x / L)| ≤ B) :
    gradNormSq (conformalField g (conformalScalar u L)) (conformalScalar u L) x ≤
      (B * C) ^ 2 / L ^ 2 := by
  have hcoef := conformal_profile_gradient_coefficient_bound (L := L) hprofile
  rw [conformalScalar_gradNormSq g u hu hL x hx]
  calc
    Real.exp (-conformalProfile (u x / L)) * (deriv conformalProfile (u x / L) / L) ^ 2 *
        gradNormSq g u x ≤
      (Real.exp (-conformalProfile (u x / L)) * (deriv conformalProfile (u x / L) / L) ^ 2) * C ^ 2 :=
      mul_le_mul_of_nonneg_left hgrad (by positivity)
    _ ≤ B ^ 2 / L ^ 2 * C ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg C)
    _ = (B * C) ^ 2 / L ^ 2 := by ring

end Yau.NodeProofs.F01Aux
