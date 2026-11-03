import spec.CHAIN.CONTRACTS

/-!
Finite matrix identities for the actual first and mixed second derivatives
of an inverse metric.  Differentiating `H⁻¹ H = 1` supplies the displayed
product identities; no positivity or Harnack conclusion is an input.
-/

noncomputable section

open scoped Matrix

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ}

theorem inverse_firstJet_of_product
    (H H₁ K₁ : Herm n) (hH : IsUnit H.det)
    (hproduct : K₁ * H + H⁻¹ * H₁ = 0) :
    K₁ = -(H⁻¹ * H₁ * H⁻¹) := by
  have hm : K₁ * H = -(H⁻¹ * H₁) := eq_neg_of_add_eq_zero_left hproduct
  calc
    K₁ = K₁ * (H * H⁻¹) := by rw [Matrix.mul_nonsing_inv H hH, Matrix.mul_one]
    _ = (K₁ * H) * H⁻¹ := by rw [Matrix.mul_assoc]
    _ = -(H⁻¹ * H₁) * H⁻¹ := by rw [hm]
    _ = -(H⁻¹ * H₁ * H⁻¹) := by rw [neg_mul]

/-- The two cross terms keep their order; no commutation of metric
derivatives is used. -/
theorem inverse_mixedJet_of_products
    (H H₁ H₂ H₁₂ K₁ K₂ K₁₂ : Herm n) (hH : IsUnit H.det)
    (hfirst₁ : K₁ * H + H⁻¹ * H₁ = 0)
    (hfirst₂ : K₂ * H + H⁻¹ * H₂ = 0)
    (hmixed : K₁₂ * H + K₁ * H₂ + K₂ * H₁ + H⁻¹ * H₁₂ = 0) :
    K₁₂ = H⁻¹ * H₁ * H⁻¹ * H₂ * H⁻¹ +
      H⁻¹ * H₂ * H⁻¹ * H₁ * H⁻¹ - H⁻¹ * H₁₂ * H⁻¹ := by
  have hK₁ := inverse_firstJet_of_product H H₁ K₁ hH hfirst₁
  have hK₂ := inverse_firstJet_of_product H H₂ K₂ hH hfirst₂
  have hm : K₁₂ * H = -(K₁ * H₂ + K₂ * H₁ + H⁻¹ * H₁₂) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_assoc] using hmixed
  calc
    K₁₂ = (K₁₂ * H) * H⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv H hH, Matrix.mul_one]
    _ = -(K₁ * H₂ + K₂ * H₁ + H⁻¹ * H₁₂) * H⁻¹ := by rw [hm]
    _ = H⁻¹ * H₁ * H⁻¹ * H₂ * H⁻¹ +
        H⁻¹ * H₂ * H⁻¹ * H₁ * H⁻¹ - H⁻¹ * H₁₂ * H⁻¹ := by
      rw [hK₁, hK₂]
      noncomm_ring

/-- Eliminating the free cotangent first jet removes one of the two
inverse-metric cross terms and leaves the tangent curvature congruence. -/
theorem inverse_mixedJet_schur_remainder
    (H H₁ H₂ H₁₂ K₁ K₂ K₁₂ : Herm n) (hH : IsUnit H.det)
    (hfirst₁ : K₁ * H + H⁻¹ * H₁ = 0)
    (hfirst₂ : K₂ * H + H⁻¹ * H₂ = 0)
    (hmixed : K₁₂ * H + K₁ * H₂ + K₂ * H₁ + H⁻¹ * H₁₂ = 0) :
    K₁₂ - K₁ * H * K₂ =
      H⁻¹ * (-H₁₂ + H₂ * H⁻¹ * H₁) * H⁻¹ := by
  have hK₁ := inverse_firstJet_of_product H H₁ K₁ hH hfirst₁
  have hK₂ := inverse_firstJet_of_product H H₂ K₂ hH hfirst₂
  have hK₁₂ := inverse_mixedJet_of_products H H₁ H₂ H₁₂ K₁ K₂ K₁₂
    hH hfirst₁ hfirst₂ hmixed
  have hcross : K₁ * H * K₂ = H⁻¹ * H₁ * H⁻¹ * H₂ * H⁻¹ := by
    rw [hK₁, hK₂]
    calc
      (-(H⁻¹ * H₁ * H⁻¹)) * H * (-(H⁻¹ * H₂ * H⁻¹)) =
          H⁻¹ * H₁ * (H⁻¹ * H) * H⁻¹ * H₂ * H⁻¹ := by noncomm_ring
      _ = H⁻¹ * H₁ * H⁻¹ * H₂ * H⁻¹ := by
        rw [Matrix.nonsing_inv_mul H hH, Matrix.mul_one]
  rw [hK₁₂, hcross]
  noncomm_ring

end Yau.NodeProofs.C01Aux
