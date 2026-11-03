import Yau.Proofs.F04BanachBilinear

noncomputable section

namespace Yau.F04Proof

/-- A quadratic-sum bound on an actual bilinear map gives the required
 product bound, by normalizing each nonzero argument. -/
theorem bilinear_product_bound_of_quadratic_bound
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (b : E →ₗ[ℝ] F →ₗ[ℝ] G) (C : ℝ)
    (hb : ∀ u v, ‖b u v‖ ≤ C * (‖u‖ ^ 2 + ‖v‖ ^ 2)) (u : E) (v : F) :
    ‖b u v‖ ≤ (2 * C) * ‖u‖ * ‖v‖ := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let a := ‖u‖⁻¹ • u
  let d := ‖v‖⁻¹ • v
  have ha : ‖a‖ = 1 := by
    dsimp only [a]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hnu]
  have hd : ‖d‖ = 1 := by
    dsimp only [d]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hnv]
  have hua : ‖u‖ • a = u := by
    dsimp only [a]
    rw [smul_smul, mul_inv_cancel₀ hnu, one_smul]
  have hvd : ‖v‖ • d = v := by
    dsimp only [d]
    rw [smul_smul, mul_inv_cancel₀ hnv, one_smul]
  have hbd : ‖b a d‖ ≤ 2 * C := by
    calc
      _ ≤ C * (‖a‖ ^ 2 + ‖d‖ ^ 2) := hb a d
      _ = _ := by rw [ha, hd]; ring
  calc
    ‖b u v‖ = ‖b (‖u‖ • a) (‖v‖ • d)‖ := by rw [hua, hvd]
    _ = ‖u‖ * ‖v‖ * ‖b a d‖ := by
      simp only [map_smul, LinearMap.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)]
      ring
    _ ≤ ‖u‖ * ‖v‖ * (2 * C) := mul_le_mul_of_nonneg_left hbd
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

end Yau.F04Proof
