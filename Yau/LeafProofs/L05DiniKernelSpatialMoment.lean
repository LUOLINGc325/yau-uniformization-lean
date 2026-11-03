import Yau.LeafProofs.L05DiniKernelShiftMoment

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic L16Aux

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
local instance l05DiniKernelSpatialMomentDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelSpatialMomentDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelSpatialMomentHessianGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelSpatialMomentHessianSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

set_option maxHeartbeats 2200000 in
theorem diniGaussian_shift_square_moment {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ h : Space n, ‖h‖ ≤ Real.sqrt t →
      Integrable (fun y : Space n =>
        ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+h)-fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖*‖y‖^(2:ℝ)) ∧
      (∫ y : Space n,
        ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+h)-fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖*‖y‖^(2:ℝ)) ≤
          C*‖h‖*t^((2:ℝ)/2-3/2) := by
  have hα : 0 ≤ (2:ℝ) := by norm_num
  obtain ⟨C,hC,hShiftSquare⟩ := diniHeatD3_shift_square_moment (n := n)
  have hshift (t : ℝ) (ht : 0 < t) (z : Space n) (hz : ‖z‖ ≤ Real.sqrt t) :
      Integrable (fun y : Space n =>
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+z)‖*‖y‖^(2:ℝ)) ∧
      (∫ y : Space n,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+z)‖*‖y‖^(2:ℝ)) ≤ C*t^((2:ℝ)/2-3/2) := by
    have hh := hShiftSquare t ht z hz
    constructor
    · convert! hh.1 using 1 <;> simp only [Real.rpow_two] <;> rfl
    · convert! hh.2 using 1 <;> norm_num [Real.rpow_two] <;> rfl
  refine ⟨C,hC,?_⟩
  intro t ht h hh
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  letI : IsFiniteMeasure ν := ⟨by simp [ν,Real.volume_Ioc]⟩
  let F : ℝ → Space n → ℝ := fun r y =>
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+r • h)‖ * ‖y‖^(2:ℝ)
  have hFpos (r : ℝ) (y : Space n) : 0 ≤ F r y := mul_nonneg
    (fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+r • h)).opNorm_nonneg
    (Real.rpow_nonneg (norm_nonneg y) (2:ℝ))
  have hscaled (r : ℝ) (hr : r ∈ Set.Ioc 0 1) : ‖r • h‖ ≤ Real.sqrt t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr.1]
    have hm : r*‖h‖ ≤ ‖h‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hr.2 (norm_nonneg h)
    exact hm.trans hh
  have hFI (r : ℝ) (hr : r ∈ Set.Ioc 0 1) : Integrable (F r) :=
    (hshift t ht (r • h) (hscaled r hr)).1
  have hFB (r : ℝ) (hr : r ∈ Set.Ioc 0 1) :
      (∫ y : Space n, F r y) ≤ C*t^((2:ℝ)/2-3/2) :=
    (hshift t ht (r • h) (hscaled r hr)).2
  have hH := ((gaussianKernel_spatial_smooth (n := n) t).fderiv_right (m := ∞)
    (by simp)).fderiv_right (m := ∞) (by simp)
  have hD3 := hH.fderiv_right (m := ∞) (by simp)
  have hn3 : Continuous (fun A : Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] ℝ => ‖A‖) :=
    continuous_norm (E := Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] ℝ)
  have hFc : Continuous (Function.uncurry F) :=
    (((hn3.comp hD3.continuous).comp
      (continuous_snd.add (continuous_fst.smul continuous_const))).mul
      (((Real.continuous_rpow_const hα).comp continuous_norm).comp continuous_snd))
  have hFm : AEStronglyMeasurable (Function.uncurry F) (ν.prod volume) :=
    hFc.aestronglyMeasurable
  have hFnI : Integrable (fun r : ℝ => ∫ y : Space n, ‖F r y‖) ν := by
    apply (integrable_const (C*t^((2:ℝ)/2-3/2))).mono' hFm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have heq : (fun y : Space n => ‖F r y‖) = F r := by
      funext y
      exact Real.norm_of_nonneg (hFpos r y)
    change ‖∫ y : Space n, ‖F r y‖‖ ≤ C*t^((2:ℝ)/2-3/2)
    rw [heq,Real.norm_of_nonneg (integral_nonneg (hFpos r))]
    exact hFB r hr
  have hprod : Integrable (Function.uncurry F) (ν.prod volume) := by
    apply (integrable_prod_iff hFm).mpr
    refine ⟨?_,hFnI⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hFI r hr
  have hQi := hprod.integral_prod_right.const_mul ‖h‖
  have hpoint (y : Space n) :
      ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+h) -
        fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖ * ‖y‖^(2:ℝ) ≤
          ‖h‖ * ∫ r, F r y ∂ν := by
    have hb := mul_le_mul_of_nonneg_right
      (gaussianKernel_secondFDeriv_spatial_increment_le t y h)
      (Real.rpow_nonneg (norm_nonneg y) (2:ℝ))
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hb
    convert hb using 1
    dsimp [ν,F]
    rw [integral_mul_const]
    ring
  have hn2 : Continuous (fun A : Space n →L[ℝ] Space n →L[ℝ] ℝ => ‖A‖) :=
    continuous_norm (E := Space n →L[ℝ] Space n →L[ℝ] ℝ)
  have hc : Continuous (fun y : Space n =>
      ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+h) -
        fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖ * ‖y‖^(2:ℝ)) :=
    (hn2.comp ((hH.continuous.comp (continuous_id.add continuous_const)).sub hH.continuous)).mul
      ((Real.continuous_rpow_const hα).comp continuous_norm)
  have hi : Integrable (fun y : Space n =>
      ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+h) -
        fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖ * ‖y‖^(2:ℝ)) := by
    apply hQi.mono' hc.aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (mul_nonneg
      (fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+h) -
        fderiv ℝ (fderiv ℝ (gaussianKernel t)) y).opNorm_nonneg
      (Real.rpow_nonneg (norm_nonneg y) (2:ℝ)))]
    exact hpoint y
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ y : Space n, ‖h‖ * ∫ r, F r y ∂ν :=
      integral_mono_ae hi hQi (ae_of_all _ hpoint)
    _ = ‖h‖ * ∫ y : Space n, ∫ r, F r y ∂ν := integral_const_mul _ _
    _ = ‖h‖ * ∫ r, (∫ y : Space n, F r y) ∂ν := by
      congr 1
      exact (integral_integral_swap hprod).symm
    _ ≤ ‖h‖ * ∫ _r, C*t^((2:ℝ)/2-3/2) ∂ν := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg h)
      apply integral_mono_ae hprod.integral_prod_left (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hFB r hr
    _ = C*‖h‖*t^((2:ℝ)/2-3/2) := by
      simp only [integral_const]
      simp [ν,Measure.real,Real.volume_Ioc] <;> ring


theorem diniHeatD2_shift_two_moments {n : ℕ} :
    ∃ M : ℝ, 0 < M ∧ ∀ a : ℝ, 0 < a → ∀ h : Space n, ‖h‖ ≤ Real.sqrt a →
      Integrable (fun y : Space n => ‖diniHeatD2 a (y+h)-diniHeatD2 a y‖) ∧
      Integrable (fun y : Space n => ‖diniHeatD2 a (y+h)-diniHeatD2 a y‖*‖y‖^2) ∧
      (∫ y : Space n, ‖diniHeatD2 a (y+h)-diniHeatD2 a y‖) ≤ M*‖h‖*a^(-(3/2:ℝ)) ∧
      (∫ y : Space n, ‖diniHeatD2 a (y+h)-diniHeatD2 a y‖*‖y‖^2) ≤ M*‖h‖*a^(-(1/2:ℝ)) := by
  obtain ⟨C0,hC0,h0⟩ := gaussianKernel_secondFDeriv_shift_weight_bound (n := n) (α := 0) le_rfl (by norm_num)
  obtain ⟨C2,hC2,h2⟩ := diniGaussian_shift_square_moment (n := n)
  refine ⟨1+C0+C2,by positivity,?_⟩
  intro a ha h hh
  have hz := h0 a ha h hh
  have hs := h2 a ha h hh
  have hi0 : Integrable (fun y : Space n => ‖diniHeatD2 a (y+h)-diniHeatD2 a y‖) := by
    simpa only [diniHeatD2,Real.rpow_zero,mul_one] using hz.1
  have hi2 : Integrable (fun y : Space n => ‖diniHeatD2 a (y+h)-diniHeatD2 a y‖*‖y‖^2) := by
    simpa only [diniHeatD2,Real.rpow_two] using hs.1
  have hb0 : (∫ y : Space n, ‖diniHeatD2 a (y+h)-diniHeatD2 a y‖) ≤ C0*‖h‖*a^(-(3/2:ℝ)) := by
    convert! hz.2 using 1 <;> norm_num [diniHeatD2]
  have hb2 : (∫ y : Space n, ‖diniHeatD2 a (y+h)-diniHeatD2 a y‖*‖y‖^2) ≤ C2*‖h‖*a^(-(1/2:ℝ)) := by
    convert! hs.2 using 1 <;> norm_num [diniHeatD2,Real.rpow_two]
  refine ⟨hi0,hi2,hb0.trans ?_,hb2.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [hC2] : C0 ≤ 1+C0+C2) (norm_nonneg h)) (Real.rpow_nonneg ha.le _)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [hC0] : C2 ≤ 1+C0+C2) (norm_nonneg h)) (Real.rpow_nonneg ha.le _)

end Yau.LeafProofs.L05Aux
