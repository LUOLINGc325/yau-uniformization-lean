import Yau.LeafProofs.L21WeightedAdjointFormula

/-! Compact-support integration identities for the ordinary Wirtinger
operators. These are the starting point of the lossless weak gain. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem contDiff_directional {f : X n → ℂ} (hf : ContDiff ℝ ∞ f) (v : X n) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ f x v) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem fderiv_directional {f : X n → ℂ} {x : X n}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (v w : X n) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
  rw [fderiv_clm_apply hf (differentiableAt_const v)]
  simp

theorem cross_directional_integral_symm {f : X n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (u v : X n) :
    (∫ x, star (fderiv ℝ f x u) * fderiv ℝ f x v ∂Yau.lebesgueC n) =
      ∫ x, star (fderiv ℝ f x v) * fderiv ℝ f x u ∂Yau.lebesgueC n := by
  have ha (a : X n) : ContDiff ℝ ∞ (fun x => star (fderiv ℝ f x a)) :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp (contDiff_directional hf a)
  have hi (a b : X n) := integral_local_mul_compact_fderiv
    (O := Set.univ) isOpen_univ ((ha a).of_le (by simp)).contDiffOn
    (hf.of_le (by simp)) hcf (by simp) b
  rw [hi u v, hi v u]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  have hdf := (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  rw [fderiv_star_apply, fderiv_star_apply, fderiv_directional hdf, fderiv_directional hdf,
    (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq u v]

theorem cross_directional_integral_im_eq_zero {f : X n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (u v : X n) :
    (∫ x, star (fderiv ℝ f x u) * fderiv ℝ f x v ∂Yau.lebesgueC n).im = 0 := by
  have hconj : (starRingEnd ℂ)
      (∫ x, star (fderiv ℝ f x u) * fderiv ℝ f x v ∂Yau.lebesgueC n) =
        ∫ x, star (fderiv ℝ f x v) * fderiv ℝ f x u ∂Yau.lebesgueC n := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with x
    change star (star (fderiv ℝ f x u) * fderiv ℝ f x v) = _
    simp only [star_mul, star_star]
  have hh := congrArg Complex.im hconj
  simp only [Complex.conj_im] at hh
  have hs := congrArg Complex.im (cross_directional_integral_symm hf hcf u v)
  linarith

theorem four_norm_wirtBar_sq (f : X n → ℂ) (x v : X n) :
    4 * ‖Yau.wirtBar f x v‖ ^ 2 =
      ‖fderiv ℝ f x v‖ ^ 2 + ‖fderiv ℝ f x (Complex.I • v)‖ ^ 2 -
        2 * (star (fderiv ℝ f x v) * fderiv ℝ f x (Complex.I • v)).im := by
  rw [Yau.wirtBar, norm_mul, mul_pow]
  norm_num
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

theorem four_norm_wirt_sq (f : X n → ℂ) (x v : X n) :
    4 * ‖Yau.wirt f x v‖ ^ 2 =
      ‖fderiv ℝ f x v‖ ^ 2 + ‖fderiv ℝ f x (Complex.I • v)‖ ^ 2 +
        2 * (star (fderiv ℝ f x v) * fderiv ℝ f x (Complex.I • v)).im := by
  rw [Yau.wirt, norm_mul, mul_pow]
  norm_num
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

theorem integrable_directional_norm_sq {f : X n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (v : X n) :
    Integrable (fun x => ‖fderiv ℝ f x v‖ ^ 2) (Yau.lebesgueC n) := by
  letI : IsLocallyFiniteMeasure (Yau.lebesgueC n) := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  have hm : MemLp (fun x => fderiv ℝ f x v) 2 (Yau.lebesgueC n) :=
    (contDiff_directional hf v).continuous.memLp_of_hasCompactSupport (hcf.fderiv_apply ℝ v)
  exact hm.integrable_norm_pow (p := 2) (by decide)

theorem integrable_cross_directional {f : X n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (u v : X n) :
    Integrable (fun x => star (fderiv ℝ f x u) * fderiv ℝ f x v) (Yau.lebesgueC n) := by
  letI : IsLocallyFiniteMeasure (Yau.lebesgueC n) := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  have hc : Continuous (fun x => star (fderiv ℝ f x u) * fderiv ℝ f x v) :=
    ((starL' ℝ : ℂ ≃L[ℝ] ℂ).continuous.comp (contDiff_directional hf u).continuous).mul
      (contDiff_directional hf v).continuous
  exact hc.integrable_of_hasCompactSupport (hcf.fderiv_apply ℝ v).mul_left

theorem integral_cross_directional_im_eq_zero {f : X n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (u v : X n) :
    (∫ x, (star (fderiv ℝ f x u) * fderiv ℝ f x v).im ∂Yau.lebesgueC n) = 0 := by
  calc
    _ = (∫ x, star (fderiv ℝ f x u) * fderiv ℝ f x v ∂Yau.lebesgueC n).im :=
      Complex.imCLM.integral_comp_comm (integrable_cross_directional hf hcf u v)
    _ = 0 := cross_directional_integral_im_eq_zero hf hcf u v

theorem four_integral_wirtBar_sq {f : X n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (v : X n) :
    4 * (∫ x, ‖Yau.wirtBar f x v‖ ^ 2 ∂Yau.lebesgueC n) =
      (∫ x, ‖fderiv ℝ f x v‖ ^ 2 ∂Yau.lebesgueC n) +
        ∫ x, ‖fderiv ℝ f x (Complex.I • v)‖ ^ 2 ∂Yau.lebesgueC n := by
  have ha := integrable_directional_norm_sq hf hcf v
  have hb := integrable_directional_norm_sq hf hcf (Complex.I • v)
  have hab : Integrable (fun x => ‖fderiv ℝ f x v‖ ^ 2 + ‖fderiv ℝ f x (Complex.I • v)‖ ^ 2)
      (Yau.lebesgueC n) := ha.add hb
  have hc : Integrable (fun x => (star (fderiv ℝ f x v) * fderiv ℝ f x (Complex.I • v)).im)
      (Yau.lebesgueC n) := Complex.imCLM.integrable_comp (integrable_cross_directional hf hcf v _)
  calc
    _ = ∫ x, 4 * ‖Yau.wirtBar f x v‖ ^ 2 ∂Yau.lebesgueC n := (integral_const_mul _ _).symm
    _ = ∫ x, ‖fderiv ℝ f x v‖ ^ 2 + ‖fderiv ℝ f x (Complex.I • v)‖ ^ 2 -
        2 * (star (fderiv ℝ f x v) * fderiv ℝ f x (Complex.I • v)).im ∂Yau.lebesgueC n := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact four_norm_wirtBar_sq f x v
    _ = _ := by
      rw [integral_sub hab (hc.const_mul 2), integral_add ha hb,
        integral_const_mul, integral_cross_directional_im_eq_zero hf hcf, mul_zero, sub_zero]

theorem four_integral_wirt_sq {f : X n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (v : X n) :
    4 * (∫ x, ‖Yau.wirt f x v‖ ^ 2 ∂Yau.lebesgueC n) =
      (∫ x, ‖fderiv ℝ f x v‖ ^ 2 ∂Yau.lebesgueC n) +
        ∫ x, ‖fderiv ℝ f x (Complex.I • v)‖ ^ 2 ∂Yau.lebesgueC n := by
  have ha := integrable_directional_norm_sq hf hcf v
  have hb := integrable_directional_norm_sq hf hcf (Complex.I • v)
  have hab : Integrable (fun x => ‖fderiv ℝ f x v‖ ^ 2 + ‖fderiv ℝ f x (Complex.I • v)‖ ^ 2)
      (Yau.lebesgueC n) := ha.add hb
  have hc : Integrable (fun x => (star (fderiv ℝ f x v) * fderiv ℝ f x (Complex.I • v)).im)
      (Yau.lebesgueC n) := Complex.imCLM.integrable_comp (integrable_cross_directional hf hcf v _)
  calc
    _ = ∫ x, 4 * ‖Yau.wirt f x v‖ ^ 2 ∂Yau.lebesgueC n := (integral_const_mul _ _).symm
    _ = ∫ x, ‖fderiv ℝ f x v‖ ^ 2 + ‖fderiv ℝ f x (Complex.I • v)‖ ^ 2 +
        2 * (star (fderiv ℝ f x v) * fderiv ℝ f x (Complex.I • v)).im ∂Yau.lebesgueC n := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact four_norm_wirt_sq f x v
    _ = _ := by
      rw [integral_add hab (hc.const_mul 2), integral_add ha hb,
        integral_const_mul, integral_cross_directional_im_eq_zero hf hcf, mul_zero, add_zero]

theorem real_gradient_energy_eq_four_bar {f : X n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) :
    (∑ a : Yau.RIdx n, ∫ x, ‖fderiv ℝ f x (Yau.realVec a)‖ ^ 2 ∂Yau.lebesgueC n) =
      4 * ∑ i : Fin n, ∫ x, ‖Yau.wirtBar f x (Yau.stdVec i)‖ ^ 2 ∂Yau.lebesgueC n := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa [Fin.sum_univ_two, Yau.realVec, Yau.stdVec] using (four_integral_wirtBar_sq hf hcf (Yau.stdVec i)).symm

theorem real_gradient_energy_eq_four_hol {f : X n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) :
    (∑ a : Yau.RIdx n, ∫ x, ‖fderiv ℝ f x (Yau.realVec a)‖ ^ 2 ∂Yau.lebesgueC n) =
      4 * ∑ i : Fin n, ∫ x, ‖Yau.wirt f x (Yau.stdVec i)‖ ^ 2 ∂Yau.lebesgueC n := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa [Fin.sum_univ_two, Yau.realVec, Yau.stdVec] using (four_integral_wirt_sq hf hcf (Yau.stdVec i)).symm

end Yau.LeafProofs.L21Aux
