import Yau.Proofs.F01ConformalGradient

/-! One fixed gradient budget before every conformal scale and point. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem conformalScalar_gradNormSq (g : HermitianField M)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) {L : ℝ} (hL : 0 < L)
    (x : M.Carrier) (hx : u x < L) :
    gradNormSq (conformalField g (conformalScalar u L)) (conformalScalar u L) x =
      Real.exp (-conformalProfile (u x / L)) *
        (deriv conformalProfile (u x / L) / L) ^ 2 * gradNormSq g u x := by
  rw [conformalField_gradNormSq]
  have hv : (WithLp.toLp 2 (fun i => wirt
      (fun z => Complex.ofReal (inChart x (conformalScalar u L) z))
      (chartPt x x) (stdVec i)) : ComplexVector n) =
      ((deriv conformalProfile (u x / L) / L : ℝ) : ℂ) •
        WithLp.toLp 2 (fun i => wirt (fun z => Complex.ofReal (inChart x u z))
          (chartPt x x) (stdVec i)) := by
    ext i
    exact conformalScalar_wirt u hu hL x hx (stdVec i)
  change Real.exp (-conformalScalar u L x) * dualNormMat (gMat g x) _ = _
  rw [hv, dualNormMat_real_smul_vector]
  simp only [conformalScalar, gradNormSq, mul_assoc]

theorem conformalProfile_exp_negative_half_sq (v : ℝ) :
    Real.exp (-conformalProfile v) = Real.exp (-conformalProfile v / 2) ^ 2 := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem conformal_profile_gradient_coefficient_bound {A L v : ℝ}
    (hbound : Real.exp (-conformalProfile v / 2) * |deriv conformalProfile v| ≤ A) :
    Real.exp (-conformalProfile v) * (deriv conformalProfile v / L) ^ 2 ≤
      A ^ 2 / L ^ 2 := by
  have hs : (Real.exp (-conformalProfile v / 2) * |deriv conformalProfile v|) ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) hbound 2
  rw [conformalProfile_exp_negative_half_sq]
  have he : Real.exp (-conformalProfile v / 2) ^ 2 * (deriv conformalProfile v / L) ^ 2 =
      (Real.exp (-conformalProfile v / 2) * |deriv conformalProfile v|) ^ 2 / L ^ 2 := by
    rw [mul_pow, sq_abs, div_pow]
    ring
  rw [he]
  exact div_le_div_of_nonneg_right hs (sq_nonneg L)

theorem conformalScalar_uniform_gradient_bound (g : HermitianField M)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) {C : ℝ} (hC : 0 ≤ C)
    (hgradient : ∀ x, gradNormSq g u x ≤ C ^ 2) :
    ∃ A : ℝ, 0 < A ∧ ∀ L, 0 < L → ∀ x, 0 ≤ u x → u x < L →
      gradNormSq (conformalField g (conformalScalar u L)) (conformalScalar u L) x ≤
        A ^ 2 / L ^ 2 := by
  obtain ⟨B, hB, hb⟩ := conformalProfile_weighted_derivative_bounds
  refine ⟨B * (C + 1), mul_pos hB (by positivity), ?_⟩
  intro L hL x hx0 hxL
  have hcoef := conformal_profile_gradient_coefficient_bound (L := L)
    (hb (u x / L) ⟨div_nonneg hx0 hL.le, (div_lt_one hL).mpr hxL⟩).1
  rw [conformalScalar_gradNormSq g u hu hL x hxL]
  calc
    Real.exp (-conformalProfile (u x / L)) * (deriv conformalProfile (u x / L) / L) ^ 2 *
        gradNormSq g u x ≤
      (Real.exp (-conformalProfile (u x / L)) * (deriv conformalProfile (u x / L) / L) ^ 2) * C ^ 2 :=
      mul_le_mul_of_nonneg_left (hgradient x) (by positivity)
    _ ≤ (B ^ 2 / L ^ 2) * C ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg C)
    _ ≤ (B * (C + 1)) ^ 2 / L ^ 2 := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ (sq_nonneg L)
      calc
        B ^ 2 * C ^ 2 ≤ B ^ 2 * (C + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg B)
        _ = (B * (C + 1)) ^ 2 := by ring

end Yau.NodeProofs.F01Aux
