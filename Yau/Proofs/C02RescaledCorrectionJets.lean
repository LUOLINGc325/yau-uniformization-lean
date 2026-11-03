import Yau.Proofs.C02RescaledCorrection

/-! Actual positive-order Fréchet jets scale by the same real dilation.
This transfers local finite-order estimates back to the one chosen chart. -/

noncomputable section
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem rescaledCorrection_jet_norm (s : ℝ) (hs : 0 < s) (a : E) (w : E → F)
    (hw : ContDiff ℝ ∞ w) (m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ (m + 1) (rescaledCorrection s a w) x‖ =
      s ^ m * ‖iteratedFDeriv ℝ (m + 1) w (a + s • x)‖ := by
  let H := fun y : E => w (a + y)
  have hH : ContDiff ℝ ∞ H := hw.comp (contDiff_const.add contDiff_id)
  have hCompose : ContDiff ℝ ∞ (fun y : E => w (a + s • y)) :=
    hw.comp (contDiff_const.add (contDiff_id.const_smul s))
  have hScale : iteratedFDeriv ℝ (m + 1) (fun y : E => w (a + s • y)) x =
      s ^ (m + 1) • iteratedFDeriv ℝ (m + 1) w (a + s • x) := by
    have h := congrFun (iteratedFDeriv_comp_const_smul s
      (hH.of_le (show (m + 1 : ℕ∞ω) ≤ ∞ by simp))) x
    rw [iteratedFDeriv_comp_add_left] at h
    exact h
  change ‖iteratedFDeriv ℝ (m + 1) (fun y => s⁻¹ • (w (a + s • y) - w a)) x‖ = _
  rw [iteratedFDeriv_const_smul_apply'
    ((hCompose.sub contDiff_const).contDiffAt.of_le (by simp)),
    fun_iteratedFDeriv_sub_apply (hCompose.contDiffAt.of_le (by simp)) contDiffAt_const,
    iteratedFDeriv_succ_const]
  simp only [Pi.zero_apply, sub_zero, hScale, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_pow, abs_of_pos hs]
  rw [pow_succ]
  have hCancel : s⁻¹ * (s ^ m * s) = s ^ m := by field_simp
  rw [← mul_assoc, hCancel]

theorem jet_norm_le_of_rescaledCorrection_bound
    (s : ℝ) (hs : 0 < s) (a : E) (w : E → F) (hw : ContDiff ℝ ∞ w)
    (m : ℕ) (B : ℝ)
    (hBound : ‖iteratedFDeriv ℝ (m + 1) (rescaledCorrection s a w) 0‖ ≤ B) :
    ‖iteratedFDeriv ℝ (m + 1) w a‖ ≤ (s⁻¹) ^ m * B := by
  have h := mul_le_mul_of_nonneg_left hBound (pow_nonneg (inv_nonneg.mpr hs.le) m)
  rw [rescaledCorrection_jet_norm s hs a w hw m 0, smul_zero, add_zero] at h
  simpa only [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hs.ne', one_pow, one_mul] using h

end Yau.Blueprint.C02Proof
