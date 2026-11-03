import Yau.Proofs.C03ComplexBilinear

/-! The full real Hessian, including its mixed entry, becomes scalar after
the actual two-parameter holomorphic terminal correction. -/

noncomputable section
namespace Yau.Proofs.C03Aux

theorem complex_hessian_correction_scalar
    (H K : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (L : ℂ →L[ℝ] ℝ)
    (hsH : ∀ a b, H a b = H b a) (hsK : ∀ a b, K a b = K b a)
    (hdiag : ∀ v : ℂ, K v v - H v v = 2 * L (v ^ 2))
    (hL1 : L 1 = (H Complex.I Complex.I - H 1 1) / 4)
    (hLI : L Complex.I = -H 1 Complex.I / 2) :
    K = ((H 1 1 + H Complex.I Complex.I) / 2) • innerSL ℝ := by
  have h11 := hdiag 1
  simp only [one_pow] at h11
  have hII := hdiag Complex.I
  simp only [Complex.I_sq, map_neg] at hII
  have hsum := hdiag (1 + Complex.I)
  have hsq : (1 + Complex.I) ^ 2 = (2 : ℂ) * Complex.I := by
    calc
      _ = 1 + 2 * Complex.I + Complex.I * Complex.I := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  have h2 : L ((2 : ℂ) * Complex.I) = 2 * L Complex.I := by
    change L ((2 : ℝ) • Complex.I) = _
    rw [map_smul, smul_eq_mul]
  rw [hsq, h2] at hsum
  simp only [map_add, add_apply] at hsum
  rw [hsH Complex.I 1, hsK Complex.I 1] at hsum
  rw [hL1] at h11 hII
  rw [hLI] at hsum
  have hk11 : K 1 1 = (H 1 1 + H Complex.I Complex.I) / 2 := by linarith
  have hkII : K Complex.I Complex.I = (H 1 1 + H Complex.I Complex.I) / 2 := by linarith
  have hk1I : K 1 Complex.I = 0 := by linarith
  exact real_complex_bilinear_scalar K _ hk11 hk1I
    ((hsK Complex.I 1).trans hk1I) hkII

end Yau.Proofs.C03Aux
