import Yau.LeafProofs.L05DiniKernelSeries

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem dini_power_le_one_add_square {eta s : ℝ} (he : 0 ≤ eta) (he2 : eta ≤ 2) (hs : 0 ≤ s) :
    s^eta ≤ 1+s^2 := by
  by_cases hs1 : s ≤ 1
  · exact (Real.rpow_le_one hs hs1 he).trans (le_add_of_nonneg_right (sq_nonneg s))
  · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hs1) he2
    rw [Real.rpow_two] at hh
    exact hh.trans (le_add_of_nonneg_left zero_le_one)

theorem dini_weighted_kernel_integrable {n : ℕ} {kappa : Space n → ℝ} {psi : ℝ → ℝ} {eta B : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hm : Measurable psi) (hzero : psi 0=0)
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta)
    (hk0 : ∀ y : Space n, 0 ≤ kappa y) (hk : Integrable kappa)
    (hk2 : Integrable (fun y : Space n => kappa y*‖y‖^2)) :
    Integrable (fun y : Space n => kappa y*psi ‖y‖) := by
  have hbound (y : Space n) : 0 ≤ psi ‖y‖ ∧ psi ‖y‖ ≤ B*(1+‖y‖^2) := by
    by_cases hy : ‖y‖=0
    · rw [hy,hzero]
      exact ⟨le_rfl,by positivity⟩
    · have hy0 : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy)
      have hp := hpsi ‖y‖ hy0
      exact ⟨hp.1,hp.2.trans (mul_le_mul_of_nonneg_left
        (dini_power_le_one_add_square he.le (by linarith only [he1]) (norm_nonneg y)) hB)⟩
  have hdom := (hk.add hk2).const_mul B
  have hmeas : AEStronglyMeasurable (fun y : Space n => kappa y*psi ‖y‖) :=
    hk.aestronglyMeasurable.mul (hm.comp measurable_norm).aestronglyMeasurable
  apply hdom.mono' hmeas
  filter_upwards [] with y
  rw [Real.norm_of_nonneg (mul_nonneg (hk0 y) (hbound y).1)]
  have hh := mul_le_mul_of_nonneg_left (hbound y).2 (hk0 y)
  change kappa y*psi ‖y‖ ≤ B*(kappa y+kappa y*‖y‖^2)
  nlinarith only [hh]

theorem dini_kernel_tail_mass_bound {n : ℕ} {kappa : Space n → ℝ} {a : ℝ} (ha : 0 < a)
    (hk0 : ∀ y : Space n, 0 ≤ kappa y) (hk : Integrable kappa)
    (hk2 : Integrable (fun y : Space n => kappa y*‖y‖^2)) :
    (∫ y in {y : Space n | a < ‖y‖}, kappa y) ≤ (∫ y : Space n, kappa y*‖y‖^2)/a^2 := by
  let S : Set (Space n) := {y | a < ‖y‖}
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_norm
  have hpoint (y : Space n) (hy : y ∈ S) : a^2*kappa y ≤ kappa y*‖y‖^2 := by
    have hn := mul_self_le_mul_self ha.le hy.le
    have hh := mul_le_mul_of_nonneg_left hn (hk0 y)
    nlinarith only [hh]
  have hh := setIntegral_mono_on (hk.const_mul (a^2)).integrableOn hk2.integrableOn hS hpoint
  rw [integral_const_mul] at hh
  have ht := setIntegral_le_integral hk2 (ae_of_all _ fun y => mul_nonneg (hk0 y) (sq_nonneg _)) (s := S)
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  nlinarith only [hh,ht]

end Yau.LeafProofs.L05Aux
