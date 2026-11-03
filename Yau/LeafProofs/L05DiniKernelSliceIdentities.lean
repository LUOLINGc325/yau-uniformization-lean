import Yau.LeafProofs.L05DiniKernelPotential

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

local instance l05DiniKernelSliceIdentitiesDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelSliceIdentitiesDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelSliceIdentitiesHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05DiniKernelSliceIdentitiesHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance


open L16Aux

theorem dini_heatAverage_spatial_increment_eq {n : ℕ} {t M : ℝ} {g : Space n → ℝ}
    (ht : 0 < t) (hg : Continuous g) (hM : ∀ y, |g y| ≤ M) (x h : Space n) :
    fderiv ℝ (fderiv ℝ (heatAverage t g)) (x+h)-fderiv ℝ (fderiv ℝ (heatAverage t g)) x =
      ∫ y : Space n, (g (x-y)-g x) • (diniHeatD2 t (y+h)-diniHeatD2 t y) := by
  let D : Space n → Space n →L[ℝ] Space n →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ (gaussianKernel t))
  let K : Space n → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun y => D (y+h)-D y
  have hDc : Continuous D :=
    (((gaussianKernel_spatial_smooth (n := n) t).fderiv_right (m := ∞)
      (by simp)).continuous_fderiv (by simp))
  have hDi : Integrable D := by
    apply (integrable_norm_iff hDc.aestronglyMeasurable).mp
    simpa only [D,Real.rpow_zero,mul_one] using
      (gaussianKernel_secondFDeriv_weight_integrable_bound (n := n) (s := 0)
        (by norm_num) ht).1
  have hKc : Continuous K := (hDc.comp (continuous_id.add continuous_const)).sub hDc
  have hKi : Integrable K := (hDi.comp_add_right h).sub hDi
  have hK0 : (∫ y : Space n, K y) = 0 := by
    dsimp [K]
    rw [integral_sub (hDi.comp_add_right h) hDi,integral_add_right_eq_self,sub_self]
  have hi (z : Space n) : Integrable (fun y : Space n => g y • D (z-y)) := by
    convert (hDi.comp_sub_left z).bdd_smul M hg.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hM y) using 1
  have heq : fderiv ℝ (fderiv ℝ (heatAverage t g)) (x+h) -
        fderiv ℝ (fderiv ℝ (heatAverage t g)) x =
      ∫ y : Space n, (g (x-y)-g x) • K y := by
    rw [heatAverage_secondFDeriv_kernel_of_bounded ht hg hM (x+h),
      heatAverage_secondFDeriv_kernel_of_bounded ht hg hM x]
    calc
      _ = ∫ y : Space n, g y • D (x+h-y)-g y • D (x-y) :=
        (integral_sub (hi (x+h)) (hi x)).symm
      _ = ∫ y : Space n, g (x-y) • D (x+h-(x-y))-g (x-y) • D (x-(x-y)) :=
        (integral_sub_left_eq_self
          (fun y : Space n => g y • D (x+h-y)-g y • D (x-y)) volume x).symm
      _ = ∫ y : Space n, g (x-y) • K y := by
        congr 1
        funext y
        have h1 : x+h-(x-y) = y+h := by abel
        rw [h1,sub_sub_cancel,← smul_sub]
      _ = _ := integral_smul_sub_const_of_zero_integral hKc hKi.norm hK0
        (hg.comp (continuous_const.sub continuous_id)) (fun y => hM (x-y)) (g x)
  exact heq

theorem dini_heatAverage_time_increment_eq {n : ℕ} {t delta M : ℝ} {g : Space n → ℝ}
    (ht : 0 < t) (hd : 0 ≤ delta) (hg : Continuous g) (hM : ∀ y, |g y| ≤ M) (x : Space n) :
    fderiv ℝ (fderiv ℝ (heatAverage (t+delta) g)) x-fderiv ℝ (fderiv ℝ (heatAverage t g)) x =
      ∫ y : Space n, (g (x-y)-g x) • (diniHeatD2 (t+delta) y-diniHeatD2 t y) := by
  have htdelta : 0 < t+delta := add_pos_of_pos_of_nonneg ht hd
  let D : ℝ → Space n → Space n →L[ℝ] Space n →L[ℝ] ℝ :=
    fun r => fderiv ℝ (fderiv ℝ (gaussianKernel r))
  let K : Space n → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun y => D (t+delta) y-D t y
  have hDc (r : ℝ) : Continuous (D r) :=
    (((gaussianKernel_spatial_smooth (n := n) r).fderiv_right (m := ∞)
      (by simp)).continuous_fderiv (by simp))
  have hDi (r : ℝ) (hr : 0 < r) : Integrable (D r) := by
    apply (integrable_norm_iff (hDc r).aestronglyMeasurable).mp
    simpa only [D,Real.rpow_zero,mul_one] using
      (gaussianKernel_secondFDeriv_weight_integrable_bound (n := n) (s := 0)
        (by norm_num) hr).1
  have hKc : Continuous K := (hDc (t+delta)).sub (hDc t)
  have hKi : Integrable K := (hDi (t+delta) htdelta).sub (hDi t ht)
  have hK0 : (∫ y : Space n, K y) = 0 := by
    dsimp [K,D]
    rw [integral_sub (hDi (t+delta) htdelta) (hDi t ht),
      gaussianKernel_secondFDeriv_integral_zero htdelta,gaussianKernel_secondFDeriv_integral_zero ht,sub_self]
  have hi (r : ℝ) (hr : 0 < r) : Integrable (fun y : Space n => g y • D r (x-y)) := by
    convert ((hDi r hr).comp_sub_left x).bdd_smul M hg.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hM y) using 1
  have heq : fderiv ℝ (fderiv ℝ (heatAverage (t+delta) g)) x -
        fderiv ℝ (fderiv ℝ (heatAverage t g)) x =
      ∫ y : Space n, (g (x-y)-g x) • K y := by
    rw [heatAverage_secondFDeriv_kernel_of_bounded htdelta hg hM x,
      heatAverage_secondFDeriv_kernel_of_bounded ht hg hM x]
    calc
      _ = ∫ y : Space n, g y • D (t+delta) (x-y)-g y • D t (x-y) :=
        (integral_sub (hi (t+delta) htdelta) (hi t ht)).symm
      _ = ∫ y : Space n, g (x-y) • D (t+delta) (x-(x-y))-g (x-y) • D t (x-(x-y)) :=
        (integral_sub_left_eq_self
          (fun y : Space n => g y • D (t+delta) (x-y)-g y • D t (x-y)) volume x).symm
      _ = ∫ y : Space n, g (x-y) • K y := by
        congr 1
        funext y
        rw [sub_sub_cancel,← smul_sub]
      _ = _ := integral_smul_sub_const_of_zero_integral hKc hKi.norm hK0
        (hg.comp (continuous_const.sub continuous_id)) (fun y => hM (x-y)) (g x)
  exact heq

end Yau.LeafProofs.L05Aux
