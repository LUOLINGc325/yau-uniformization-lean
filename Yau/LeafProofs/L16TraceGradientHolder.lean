import Yau.LeafProofs.L16TraceLayerNormal

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- The actual weighted first Gaussian derivative moment. -/
theorem gaussianKernel_fderiv_weight_bound {n : ℕ} {α : ℝ} (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      Integrable (fun z : Space n => ‖fderiv ℝ (gaussianKernel r) z‖*‖z‖^α) ∧
      (∫ z : Space n, ‖fderiv ℝ (gaussianKernel r) z‖*‖z‖^α) ≤ C*r^(α/2-1/2) := by
  obtain ⟨C,hC,hMoment⟩ := gaussianKernel_weight_integral_bound (n := n)
    (s := α+1) (by linarith)
  refine ⟨C/2,by positivity,?_⟩
  intro r hr
  have hEq : (fun z : Space n => ‖fderiv ℝ (gaussianKernel r) z‖*‖z‖^α) =
      fun z => (‖z‖^(α+1)*gaussianKernel r z)/(2*r) := by
    funext z
    rw [gaussianKernel_fderiv_norm hr,Real.rpow_add_of_nonneg (norm_nonneg z) hα (by norm_num),Real.rpow_one]
    ring
  rw [hEq]
  refine ⟨(hMoment r hr).1.div_const (2*r),?_⟩
  rw [integral_div]
  have h := div_le_div_of_nonneg_right (hMoment r hr).2 (by positivity : 0 ≤ 2*r)
  have hPow : r^((α+1)/2) = r^(α/2-1/2)*r := by
    rw [← Real.rpow_add_one hr.ne']
    congr 1
    ring
  rw [hPow] at h
  convert h using 1 <;> field_simp

/-- Cancellation of the actual first heat derivative for a bounded source. -/
theorem heatAverage_fderiv_cancelled {n : ℕ} {r F : ℝ} {g : Space n → ℝ}
    (hr : 0 < r) (hg : Continuous g) (hF : ∀ y, |g y| ≤ F) (ξ : Space n) :
    fderiv ℝ (heatAverage r g) ξ =
      ∫ z : Space n, (g (ξ-z)-g ξ) • fderiv ℝ (gaussianKernel r) z := by
  rw [(heatAverage_hasFDerivAt_kernel_of_bounded hr hg hF ξ).fderiv]
  have hsub := integral_sub_left_eq_self
    (fun z : Space n => g z • fderiv ℝ (gaussianKernel r) (ξ-z)) ξ (μ := volume)
  simp only [sub_sub_cancel] at hsub
  rw [← hsub]
  exact integral_smul_sub_const_of_zero_integral
    ((gaussianKernel_spatial_smooth (n := n) r).continuous_fderiv (by simp))
    (gaussianKernel_fderiv_integrable hr).norm (gaussianKernel_fderiv_integral_zero hr)
    (hg.comp (continuous_const.sub continuous_id)) (fun z => hF (ξ-z)) (g ξ)

/-- Spatial Holder cancellation gives the true integrable mixed-layer exponent,
    stronger than the bounded-source r^(-1/2) gradient estimate. -/
theorem heatAverage_fderiv_holder_bound {n : ℕ} {α : ℝ} (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ (g : Space n → ℝ) (F H : ℝ),
      Continuous g → (∀ y, |g y| ≤ F) → 0 ≤ H →
      (∀ x y, |g x-g y| ≤ H*‖x-y‖^α) → ∀ ξ : Space n,
      ‖fderiv ℝ (heatAverage r g) ξ‖ ≤ C*H*r^(α/2-1/2) := by
  obtain ⟨C,hC,hMoment⟩ := gaussianKernel_fderiv_weight_bound (n := n) hα
  refine ⟨C,hC,?_⟩
  intro r hr g F H hg hF hH0 hH ξ
  rw [heatAverage_fderiv_cancelled hr hg hF ξ]
  calc
    _ ≤ ∫ z : Space n, H*(‖fderiv ℝ (gaussianKernel r) z‖*‖z‖^α) := by
      apply norm_integral_le_of_norm_le ((hMoment r hr).1.const_mul H)
      exact ae_of_all _ fun z => by
        have hh := hH (ξ-z) ξ
        have hDiff : (ξ-z)-ξ = -z := by abel
        rw [hDiff,norm_neg] at hh
        rw [norm_smul,Real.norm_eq_abs]
        calc
          _ ≤ (H*‖z‖^α)*‖fderiv ℝ (gaussianKernel r) z‖ :=
            mul_le_mul_of_nonneg_right hh (norm_nonneg _)
          _ = _ := by ring
    _ = H*(∫ z : Space n, ‖fderiv ℝ (gaussianKernel r) z‖*‖z‖^α) := integral_const_mul _ _
    _ ≤ H*(C*r^(α/2-1/2)) := mul_le_mul_of_nonneg_left (hMoment r hr).2 hH0
    _ = C*H*r^(α/2-1/2) := by ring

end Yau.LeafProofs.L16Aux
