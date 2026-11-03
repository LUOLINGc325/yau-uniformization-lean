import Yau.LeafProofs.L05DiniKernelMoments

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

local instance l05DiniKernelShiftMomentDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelShiftMomentDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelShiftMomentHessianGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelShiftMomentHessianSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance


set_option maxHeartbeats 1800000 in
theorem diniHeatD3_shift_square_moment {n : ℕ} :
    ∃ M : ℝ, 0 < M ∧ ∀ a : ℝ, 0 < a → ∀ z : Space n, ‖z‖ ≤ Real.sqrt a →
      Integrable (fun y : Space n => ‖diniHeatD3 a (y+z)‖*‖y‖^2) ∧
      (∫ y : Space n, ‖diniHeatD3 a (y+z)‖*‖y‖^2) ≤ M*a^(-(1/2:ℝ)) := by
  obtain ⟨C2,hC2,h2⟩ := L16Aux.gaussianKernel_thirdFDeriv_weight_bound (n := n) (s := 2) (by norm_num)
  obtain ⟨C0,hC0,h0⟩ := L16Aux.gaussianKernel_thirdFDeriv_weight_bound (n := n) (s := 0) le_rfl
  refine ⟨2*(C2+C0),by positivity,?_⟩
  intro a ha z hz
  have hi2 : Integrable (fun y : Space n => ‖diniHeatD3 a (y+z)‖*‖y+z‖^2) := by
    convert! (h2 a ha).1.comp_add_right z using 1 <;> simp only [diniHeatD3,diniHeatD2,Real.rpow_two] <;> rfl
  have hi0 : Integrable (fun y : Space n => ‖diniHeatD3 a (y+z)‖) := by
    convert! (h0 a ha).1.comp_add_right z using 1 <;> simp only [diniHeatD3,diniHeatD2,Real.rpow_zero,mul_one] <;> rfl
  have hpow (y : Space n) : ‖y‖^2 ≤ 2*‖y+z‖^2+2*‖z‖^2 := by
    have htri : ‖y‖ ≤ ‖y+z‖+‖z‖ := by
      calc
        _=‖(y+z)-z‖ := by rw [add_sub_cancel_right]
        _≤_ := norm_sub_le _ _
    have hs := mul_self_le_mul_self (norm_nonneg y) htri
    nlinarith only [hs,sq_nonneg (‖y+z‖-‖z‖)]
  have hpoint (y : Space n) : ‖diniHeatD3 a (y+z)‖*‖y‖^2 ≤
      2*(‖diniHeatD3 a (y+z)‖*‖y+z‖^2)+(2*‖z‖^2)*‖diniHeatD3 a (y+z)‖ := by
    have hh := mul_le_mul_of_nonneg_left (hpow y) (norm_nonneg (diniHeatD3 a (y+z)))
    nlinarith only [hh]
  have h3s := (((L16Aux.gaussianKernel_spatial_smooth (n := n) a).fderiv_right (m := ∞)
    (by simp)).fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hn : Continuous (fun A : Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] ℝ => ‖A‖) := continuous_norm
  have hc : Continuous (fun y : Space n => ‖diniHeatD3 a (y+z)‖*‖y‖^2) :=
    ((hn.comp h3s.continuous).comp (continuous_id.add continuous_const)).mul (continuous_norm.pow 2)
  have hdom := (hi2.const_mul 2).add (hi0.const_mul (2*‖z‖^2))
  have hi : Integrable (fun y : Space n => ‖diniHeatD3 a (y+z)‖*‖y‖^2) := by
    apply hdom.mono' hc.aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))]
    exact hpoint y
  have hz2 : ‖z‖^2 ≤ a := by
    have hs := mul_self_le_mul_self (norm_nonneg z) hz
    nlinarith only [hs,Real.sq_sqrt ha.le]
  have hb2 : (∫ y : Space n, ‖diniHeatD3 a y‖*‖y‖^2) ≤ C2*a^(-(1/2:ℝ)) := by
    convert! (h2 a ha).2 using 1 <;> norm_num [diniHeatD3,diniHeatD2,Real.rpow_two] <;> rfl
  have hb0 : (∫ y : Space n, ‖diniHeatD3 a y‖) ≤ C0*a^(-(3/2:ℝ)) := by
    convert! (h0 a ha).2 using 1 <;> norm_num [diniHeatD3,diniHeatD2] <;> rfl
  have hshift2 : (∫ y : Space n, ‖diniHeatD3 a (y+z)‖*‖y+z‖^2)=
      (∫ y : Space n, ‖diniHeatD3 a y‖*‖y‖^2) :=
    integral_add_right_eq_self (fun y : Space n => ‖diniHeatD3 a y‖*‖y‖^2) z
  have hshift0 : (∫ y : Space n, ‖diniHeatD3 a (y+z)‖)=
      (∫ y : Space n, ‖diniHeatD3 a y‖) :=
    integral_add_right_eq_self (fun y : Space n => ‖diniHeatD3 a y‖) z
  have hcomp : (∫ y : Space n, ‖diniHeatD3 a (y+z)‖*‖y‖^2) ≤
      2*(∫ y : Space n, ‖diniHeatD3 a y‖*‖y‖^2)+(2*‖z‖^2)*(∫ y : Space n, ‖diniHeatD3 a y‖) := by
    have hh := integral_mono_ae hi hdom (ae_of_all _ hpoint)
    simp only [Pi.add_apply] at hh
    rw [integral_add (hi2.const_mul 2) (hi0.const_mul (2*‖z‖^2)),integral_const_mul,integral_const_mul,
      hshift2,hshift0] at hh
    exact hh
  have hB2 := mul_le_mul_of_nonneg_left hb2 (by norm_num : (0:ℝ) ≤ 2)
  have hB0 := mul_le_mul_of_nonneg_left hb0 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (sq_nonneg ‖z‖))
  have hZa := mul_le_mul_of_nonneg_right hz2 (show 0 ≤ 2*(C0*a^(-(3/2:ℝ))) by positivity)
  have hpower : a*a^(-(3/2:ℝ))=a^(-(1/2:ℝ)) := by
    calc
      _=a^(1:ℝ)*a^(-(3/2:ℝ)) := by rw [Real.rpow_one]
      _=a^((1:ℝ)+(-(3/2:ℝ))) := (Real.rpow_add ha _ _).symm
      _=_ := by norm_num
  refine ⟨hi,?_⟩
  have hZa' : 2*‖z‖^2*(C0*a^(-(3/2:ℝ))) ≤ 2*C0*a^(-(1/2:ℝ)) := by
    calc
      _≤2*C0*(a*a^(-(3/2:ℝ))) := by nlinarith only [hZa]
      _=_ := by rw [hpower]
  nlinarith only [hcomp,hB2,hB0,hZa']

end Yau.LeafProofs.L05Aux
