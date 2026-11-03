import Yau.Proofs.F04ZeroPastLp
import Yau.Proofs.F04ZeroPastTests

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem integrable_mul_zeroPastCutoff {n : ℕ} {O : Set (Space n)} {s : ℝ}
    {f : Point n → ℝ} (hf : Integrable f (productVolume O (Ioo 0 s))) (δ : ℝ) :
    Integrable (fun p => f p * zeroPastCutoff δ p.2) (productVolume O (Ioo 0 s)) := by
  have hb : ∀ᵐ p ∂productVolume O (Ioo 0 s), ‖zeroPastCutoff δ p.2‖ ≤ (1 : ℝ) :=
    ae_of_all _ (fun p => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (zeroPastCutoff_range δ p.2).1] using
        (zeroPastCutoff_range δ p.2).2)
  exact hf.mul_bdd (((zeroPastCutoff_contDiff δ).continuous.comp continuous_snd).aestronglyMeasurable) hb

theorem integrable_zeroPastCutoff_error {n : ℕ} {O : Set (Space n)} {s : ℝ}
    {u φ : Point n → ℝ} (hu : MemLp u 2 (productVolume O (Ioo 0 s)))
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (δ : ℝ) :
    Integrable (fun p => (deriv (zeroPastCutoff δ) p.2 * u p) * φ p)
      (productVolume O (Ioo 0 s)) := by
  have hs : ContDiff ℝ ∞ (fun p : Point n => φ p * deriv (zeroPastCutoff δ) p.2) :=
    hφ.mul ((contDiff_infty_iff_deriv.mp (zeroPastCutoff_contDiff δ)).2.comp contDiff_snd)
  have h2 : MemLp (fun p : Point n => φ p * deriv (zeroPastCutoff δ) p.2) 2
      (productVolume O (Ioo 0 s)) := by
    rw [productVolume_eq_restrict]
    exact (hs.continuous.memLp_of_hasCompactSupport hcφ.mul_right).restrict _
  convert hu.integrable_mul h2 using 1
  funext p
  simp only [Pi.mul_apply]
  ring

theorem tendsto_integral_zeroPastCutoff {n : ℕ} {O : Set (Space n)}
    (hO : MeasurableSet O) {s : ℝ} {f : Point n → ℝ}
    (hf : Integrable f (productVolume O (Ioo 0 s))) :
    Tendsto (fun j : ℕ => ∫ p, f p * zeroPastCutoff (1 / ((j : ℝ) + 1)) p.2
      ∂productVolume O (Ioo 0 s)) atTop (𝓝 (∫ p, f p ∂productVolume O (Ioo 0 s))) := by
  apply tendsto_integral_of_dominated_convergence (fun p => ‖f p‖)
  · intro j
    exact hf.aestronglyMeasurable.mul
      (((zeroPastCutoff_contDiff _).continuous.comp continuous_snd).aestronglyMeasurable)
  · exact hf.norm
  · intro j
    apply ae_of_all
    intro p
    rw [norm_mul]
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (zeroPastCutoff_range _ _).1]
    exact (mul_le_mul_of_nonneg_left (zeroPastCutoff_range _ _).2 (abs_nonneg _)).trans_eq (mul_one _)
  · rw [productVolume_eq_restrict]
    filter_upwards [ae_restrict_mem (hO.prod measurableSet_Ioo)] with p hp
    have he : (fun j : ℕ => f p * zeroPastCutoff (1 / ((j : ℝ) + 1)) p.2) =ᶠ[atTop]
        (fun _ => f p) := by
      filter_upwards [zeroPastCutoff_eventually_one hp.2.1] with j hj
      rw [hj.1, mul_one]
    exact tendsto_const_nhds.congr' he.symm

/-- The true cutoff-derivative error tends to zero on a fixed positive
 cylinder. The integrable bound uses linear growth and the compact test. -/
theorem tendsto_integral_zeroPastCutoff_error {n : ℕ} {O : Set (Space n)}
    (hO : MeasurableSet O) {s K : ℝ} (hK : 0 ≤ K) {u φ : Point n → ℝ}
    (hu : MemLp u 2 (productVolume O (Ioo 0 s)))
    (hGrowth : ∀ p ∈ O ×ˢ Ioo 0 s, |u p| ≤ K * p.2)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    Tendsto (fun j : ℕ => ∫ p,
      (deriv (zeroPastCutoff (1 / ((j : ℝ) + 1))) p.2 * u p) * φ p
      ∂productVolume O (Ioo 0 s)) atTop (𝓝 0) := by
  obtain ⟨D, hD, hDeriv, _⟩ := Yau.LeafProofs.L16Aux.smoothTransition_two_derivative_bounds
  let bound : Point n → ℝ := fun p => (2 * D * K) * |φ p|
  have hBound : Integrable bound (productVolume O (Ioo 0 s)) := by
    rw [productVolume_eq_restrict]
    exact ((hφ.continuous.integrable_of_hasCompactSupport hcφ).abs.const_mul _).integrableOn
  have hLim : Tendsto (fun j : ℕ => ∫ p,
      (deriv (zeroPastCutoff (1 / ((j : ℝ) + 1))) p.2 * u p) * φ p
      ∂productVolume O (Ioo 0 s)) atTop
      (𝓝 (∫ _p : Point n, (0 : ℝ) ∂productVolume O (Ioo 0 s))) := by
    apply tendsto_integral_of_dominated_convergence bound
    · intro j
      have hd : Continuous (fun p : Point n => deriv (zeroPastCutoff (1 / ((j : ℝ) + 1))) p.2) :=
        ((contDiff_infty_iff_deriv.mp (zeroPastCutoff_contDiff _)).2.continuous).comp continuous_snd
      exact (hd.aestronglyMeasurable.mul hu.aestronglyMeasurable).mul hφ.continuous.aestronglyMeasurable
    · exact hBound
    · intro j
      rw [productVolume_eq_restrict]
      filter_upwards [ae_restrict_mem (hO.prod measurableSet_Ioo)] with p hp
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (zeroPastCutoff_growth_error_bound (le_trans zero_le_one hD) hK
          (by positivity) hDeriv (hGrowth p hp)) (abs_nonneg _)
    · rw [productVolume_eq_restrict]
      filter_upwards [ae_restrict_mem (hO.prod measurableSet_Ioo)] with p hp
      have he : (fun j : ℕ =>
          (deriv (zeroPastCutoff (1 / ((j : ℝ) + 1))) p.2 * u p) * φ p) =ᶠ[atTop]
          (fun _ => 0) := by
        filter_upwards [zeroPastCutoff_eventually_one hp.2.1] with j hj
        rw [hj.2, zero_mul, zero_mul]
      exact tendsto_const_nhds.congr' he.symm
  simpa only [integral_zero] using hLim

end Yau.F04Proof
