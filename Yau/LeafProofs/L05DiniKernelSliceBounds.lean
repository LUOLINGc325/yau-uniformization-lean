import Yau.LeafProofs.L05DiniKernelSliceIdentities

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic
open L16Aux

local instance l05DiniKernelSliceBoundsDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelSliceBoundsDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelSliceBoundsHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05DiniKernelSliceBoundsHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

theorem dini_cancelled_integral_norm_le {n : ℕ} {g : Space n → ℝ} {psi : ℝ → ℝ}
    {K : Space n → DiniHessian n} {x : Space n}
    (hI : Integrable (fun y : Space n => ‖K y‖*psi ‖y‖))
    (hg : ∀ u v : Space n, |g u-g v| ≤ psi ‖u-v‖) :
    ‖∫ y : Space n, (g (x-y)-g x) • K y‖ ≤ ∫ y : Space n, ‖K y‖*psi ‖y‖ := by
  apply norm_integral_le_of_norm_le hI
  filter_upwards [] with y
  have hh := hg (x-y) x
  have he : (x-y)-x = -y := by abel
  rw [he,norm_neg] at hh
  calc
    _ ≤ ‖g (x-y)-g x‖*‖K y‖ := ContinuousLinearMap.opNorm_smul_le _ _
    _ = |g (x-y)-g x| *‖K y‖ := by rw [Real.norm_eq_abs]
    _ ≤ psi ‖y‖*‖K y‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
    _ = _ := by ring

theorem dini_heatAverage_hessian_norm_le {n : ℕ} {a M : ℝ} {g : Space n → ℝ} {psi : ℝ → ℝ}
    (ha : 0 < a) (hg : Continuous g) (hM : ∀ y, |g y| ≤ M)
    (hI : Integrable (fun y : Space n => ‖diniHeatD2 a y‖*psi ‖y‖))
    (hmod : ∀ u v : Space n, |g u-g v| ≤ psi ‖u-v‖) (x : Space n) :
    ‖fderiv ℝ (fderiv ℝ (heatAverage a g)) x‖ ≤ ∫ y : Space n, ‖diniHeatD2 a y‖*psi ‖y‖ := by
  rw [heatAverage_secondFDeriv_cancelled ha hg hM x]
  exact dini_cancelled_integral_norm_le hI hmod

theorem dini_heatAverage_spatial_increment_norm_le {n : ℕ} {a M : ℝ}
    {g : Space n → ℝ} {psi : ℝ → ℝ} (ha : 0 < a) (hg : Continuous g)
    (hM : ∀ y, |g y| ≤ M) (x h : Space n)
    (hI : Integrable (fun y : Space n => ‖diniHeatD2 a (y+h)-diniHeatD2 a y‖*psi ‖y‖))
    (hmod : ∀ u v : Space n, |g u-g v| ≤ psi ‖u-v‖) :
    ‖fderiv ℝ (fderiv ℝ (heatAverage a g)) (x+h)-fderiv ℝ (fderiv ℝ (heatAverage a g)) x‖ ≤
      ∫ y : Space n, ‖diniHeatD2 a (y+h)-diniHeatD2 a y‖*psi ‖y‖ := by
  rw [dini_heatAverage_spatial_increment_eq ha hg hM x h]
  exact dini_cancelled_integral_norm_le hI hmod

theorem dini_heatAverage_time_increment_norm_le {n : ℕ} {a delta M : ℝ}
    {g : Space n → ℝ} {psi : ℝ → ℝ} (ha : 0 < a) (hd : 0 ≤ delta) (hg : Continuous g)
    (hM : ∀ y, |g y| ≤ M) (x : Space n)
    (hI : Integrable (fun y : Space n => ‖diniHeatD2 (a+delta) y-diniHeatD2 a y‖*psi ‖y‖))
    (hmod : ∀ u v : Space n, |g u-g v| ≤ psi ‖u-v‖) :
    ‖fderiv ℝ (fderiv ℝ (heatAverage (a+delta) g)) x-fderiv ℝ (fderiv ℝ (heatAverage a g)) x‖ ≤
      ∫ y : Space n, ‖diniHeatD2 (a+delta) y-diniHeatD2 a y‖*psi ‖y‖ := by
  rw [dini_heatAverage_time_increment_eq ha hd hg hM x]
  exact dini_cancelled_integral_norm_le hI hmod

end Yau.LeafProofs.L05Aux
