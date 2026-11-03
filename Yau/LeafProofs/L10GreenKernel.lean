import Yau.LeafProofs.L08

/-! The explicit unit-disc Green kernel, with the original Laplacian sign. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace Yau.LeafProofs

def discGreenKernel (z w : ℂ) : ℝ :=
  (2 * Real.pi)⁻¹ * (Real.log ‖z - w‖ - Real.log ‖1 - z * conj w‖)

theorem discGreen_identity (z w : ℂ) :
    ‖1 - z * conj w‖ ^ 2 - ‖z - w‖ ^ 2 =
      (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im]
  ring

theorem discGreen_denominator_ne_zero {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ < 1) : 1 - z * conj w ≠ 0 := by
  have hprod : ‖z * conj w‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    have := mul_le_mul_of_nonneg_right hz (norm_nonneg w)
    nlinarith
  intro h
  have hh : z * conj w = 1 := by linear_combination -h
  rw [hh, norm_one] at hprod
  exact (lt_irrefl _ hprod)

theorem discGreen_denominator_ge {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖z - w‖ ≤ ‖1 - z * conj w‖ := by
  have hid := discGreen_identity z w
  have ha : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hb : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  nlinarith [mul_nonneg ha hb, norm_nonneg (z - w), norm_nonneg (1 - z * conj w)]

theorem discGreen_boundary {z w : ℂ} (hz : ‖z‖ = 1) :
    discGreenKernel z w = 0 := by
  have hid := discGreen_identity z w
  have heq : ‖1 - z * conj w‖ = ‖z - w‖ := by
    rw [hz] at hid
    nlinarith [norm_nonneg (z - w), norm_nonneg (1 - z * conj w)]
  simp [discGreenKernel, heq]

theorem discGreen_rotation (a z w : ℂ) (ha : ‖a‖ = 1) :
    discGreenKernel (a * z) (a * w) = discGreenKernel z w := by
  have haa : a * conj a = 1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, ha]
    norm_num
  have hsub : ‖a * z - a * w‖ = ‖z - w‖ := by
    rw [← mul_sub, norm_mul, ha, one_mul]
  have hcorr : 1 - a * z * conj (a * w) = 1 - z * conj w := by
    rw [map_mul]
    calc
      _ = 1 - (a * conj a) * (z * conj w) := by ring
      _ = _ := by rw [haa, one_mul]
  simp only [discGreenKernel, hsub, hcorr]

end Yau.LeafProofs
