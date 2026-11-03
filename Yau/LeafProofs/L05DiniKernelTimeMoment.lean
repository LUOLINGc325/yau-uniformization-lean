import Yau.LeafProofs.L05DiniKernelMoments

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic L16Aux

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

local instance l05DiniKernelTimeMomentDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelTimeMomentDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelTimeMomentHessianGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelTimeMomentHessianSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance


set_option maxHeartbeats 1800000 in
theorem diniGaussian_time_square_moment {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ delta : ℝ, 0 ≤ delta →
      Integrable (fun y : Space n =>
        ‖fderiv ℝ (fderiv ℝ (gaussianKernel (t+delta))) y-
          fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖*‖y‖^(2:ℝ)) ∧
      (∫ y : Space n,
        ‖fderiv ℝ (fderiv ℝ (gaussianKernel (t+delta))) y-
          fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖*‖y‖^(2:ℝ)) ≤ C*delta*t^((2:ℝ)/2-2) := by
  have hα : 0 ≤ (2:ℝ) := by norm_num
  obtain ⟨C,hC,hbound⟩ := gaussianKernel_secondFDeriv_time_weight_bound (n := n) hα
  refine ⟨C,hC,?_⟩
  intro t ht δ hδ
  have htδ : 0 < t+δ := add_pos_of_pos_of_nonneg ht hδ
  have hle : t ≤ t+δ := le_add_of_nonneg_right hδ
  let μ : Measure ℝ := volume.restrict (Set.Ioc t (t+δ))
  letI : IsFiniteMeasure μ := ⟨by simp [μ,Real.volume_Ioc]⟩
  let F : ℝ → Space n → ℝ := fun r y =>
    ‖deriv (fun s : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel s)) y) r‖*‖y‖^(2:ℝ)
  have hFpos (r : ℝ) (y : Space n) : 0 ≤ F r y :=
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hFI (r : ℝ) (hr : r ∈ Set.Ioc t (t+δ)) : Integrable (F r) :=
    (hbound r (ht.trans hr.1)).1
  have hFB (r : ℝ) (hr : r ∈ Set.Ioc t (t+δ)) :
      (∫ y : Space n, F r y) ≤ C*t^((2:ℝ)/2-2) := by
    exact ((hbound r (ht.trans hr.1)).2).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos ht hr.1.le (by linarith)) hC.le)
  have hFc : ContinuousOn (Function.uncurry F) (Set.Ioc t (t+δ) ×ˢ Set.univ) := by
    intro p hp
    exact (((gaussianKernel_secondFDeriv_time_joint_smooth (ht.trans hp.1.1) p.2).continuousAt.norm).mul
      (((Real.continuous_rpow_const hα).comp continuous_norm).continuousAt.comp continuousAt_snd)).continuousWithinAt
  have hProd : μ.prod (volume : Measure (Space n)) =
      ((volume : Measure ℝ).prod (volume : Measure (Space n))).restrict
        (Set.Ioc t (t+δ) ×ˢ (Set.univ : Set (Space n))) := by
    simpa only [μ,Measure.restrict_univ] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ))
        (ν := (volume : Measure (Space n))) (Set.Ioc t (t+δ)) Set.univ)
  have hFm : AEStronglyMeasurable (Function.uncurry F) (μ.prod volume) := by
    rw [hProd]
    exact hFc.aestronglyMeasurable (measurableSet_Ioc.prod MeasurableSet.univ)
  have hFnI : Integrable (fun r : ℝ => ∫ y : Space n, ‖F r y‖) μ := by
    apply (integrable_const (C*t^((2:ℝ)/2-2))).mono' hFm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have heq : (fun y : Space n => ‖F r y‖) = F r := by
      funext y
      exact Real.norm_of_nonneg (hFpos r y)
    change ‖∫ y : Space n, ‖F r y‖‖ ≤ C*t^((2:ℝ)/2-2)
    rw [heq,Real.norm_of_nonneg (integral_nonneg (hFpos r))]
    exact hFB r hr
  have hprod : Integrable (Function.uncurry F) (μ.prod volume) := by
    apply (integrable_prod_iff hFm).mpr
    refine ⟨?_,hFnI⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hFI r hr
  have hQi := hprod.integral_prod_right
  have hpoint (y : Space n) :
      ‖fderiv ℝ (fderiv ℝ (gaussianKernel (t+δ))) y -
        fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖*‖y‖^(2:ℝ) ≤ ∫ r, F r y ∂μ := by
    have hb := mul_le_mul_of_nonneg_right
      (gaussianKernel_secondFDeriv_temporal_increment_le ht hδ y)
      (Real.rpow_nonneg (norm_nonneg y) (2:ℝ))
    rw [intervalIntegral.integral_of_le hle] at hb
    simpa only [μ,F,integral_mul_const] using hb
  have hHc (r : ℝ) : Continuous (fun y : Space n => fderiv ℝ (fderiv ℝ (gaussianKernel r)) y) :=
    ((gaussianKernel_spatial_smooth r).fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)
  have hc : Continuous (fun y : Space n =>
      ‖fderiv ℝ (fderiv ℝ (gaussianKernel (t+δ))) y -
        fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖*‖y‖^(2:ℝ)) :=
    ((hHc (t+δ)).sub (hHc t)).norm.mul ((Real.continuous_rpow_const hα).comp continuous_norm)
  have hi : Integrable (fun y : Space n =>
      ‖fderiv ℝ (fderiv ℝ (gaussianKernel (t+δ))) y -
        fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖*‖y‖^(2:ℝ)) := by
    apply hQi.mono' hc.aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
    exact hpoint y
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ y : Space n, ∫ r, F r y ∂μ := integral_mono_ae hi hQi (ae_of_all _ hpoint)
    _ = ∫ r, (∫ y : Space n, F r y) ∂μ := (integral_integral_swap hprod).symm
    _ ≤ ∫ _r, C*t^((2:ℝ)/2-2) ∂μ := by
      apply integral_mono_ae hprod.integral_prod_left (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hFB r hr
    _ = C*δ*t^((2:ℝ)/2-2) := by
      simp only [integral_const]
      simp [μ,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal hδ] <;> ring


theorem diniHeatD2_time_two_moments {n : ℕ} :
    ∃ M : ℝ, 0 < M ∧ ∀ a : ℝ, 0 < a → ∀ delta : ℝ, 0 ≤ delta →
      Integrable (fun y : Space n => ‖diniHeatD2 (a+delta) y-diniHeatD2 a y‖) ∧
      Integrable (fun y : Space n => ‖diniHeatD2 (a+delta) y-diniHeatD2 a y‖*‖y‖^2) ∧
      (∫ y : Space n, ‖diniHeatD2 (a+delta) y-diniHeatD2 a y‖) ≤ M*delta*a^(-(2:ℝ)) ∧
      (∫ y : Space n, ‖diniHeatD2 (a+delta) y-diniHeatD2 a y‖*‖y‖^2) ≤ M*delta/a := by
  obtain ⟨C0,hC0,h0⟩ := gaussianKernel_secondFDeriv_time_increment_weight_bound (n := n) (α := 0) le_rfl (by norm_num)
  obtain ⟨C2,hC2,h2⟩ := diniGaussian_time_square_moment (n := n)
  refine ⟨1+C0+C2,by positivity,?_⟩
  intro a ha delta hd
  have hz := h0 a ha delta hd
  have hs := h2 a ha delta hd
  have hi0 : Integrable (fun y : Space n => ‖diniHeatD2 (a+delta) y-diniHeatD2 a y‖) := by
    simpa only [diniHeatD2,Real.rpow_zero,mul_one] using hz.1
  have hi2 : Integrable (fun y : Space n => ‖diniHeatD2 (a+delta) y-diniHeatD2 a y‖*‖y‖^2) := by
    simpa only [diniHeatD2,Real.rpow_two] using hs.1
  have hb0 : (∫ y : Space n, ‖diniHeatD2 (a+delta) y-diniHeatD2 a y‖) ≤ C0*delta*a^(-(2:ℝ)) := by
    convert! hz.2 using 1 <;> norm_num [diniHeatD2]
  have hb2 : (∫ y : Space n, ‖diniHeatD2 (a+delta) y-diniHeatD2 a y‖*‖y‖^2) ≤ C2*delta/a := by
    convert! hs.2 using 1 <;> norm_num [diniHeatD2,Real.rpow_two,Real.rpow_neg_one,div_eq_mul_inv]
  refine ⟨hi0,hi2,hb0.trans ?_,hb2.trans ?_⟩
  · have hc : C0 ≤ 1+C0+C2 := by linarith only [hC2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hd) (Real.rpow_nonneg ha.le _)
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [hC0] : C2 ≤ 1+C0+C2) hd) ha.le

end Yau.LeafProofs.L05Aux
