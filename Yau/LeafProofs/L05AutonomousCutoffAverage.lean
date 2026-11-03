import Yau.LeafProofs.L05AutonomousEllipsoidAverage
import Yau.LeafProofs.L05AutonomousCutoffTaylor

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The first moment vanishes for the actual ellipsoid measure, leaving only a quadratic remainder. -/
theorem auto_ellipsoid_cutoff_pointwise {n : ℕ} {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hcφ : HasCompactSupport φ) : ∃ C : ℝ, 0< C ∧
      ∀ (B : Space n ≃L[ℝ] Space n) (x : Space n),
        |autoSpatialAverage (autoLinearBallProbability B) φ x-φ x|≤ C*‖B.toContinuousLinearMap‖^2 := by
  obtain ⟨C,hC,hTaylor⟩ := auto_compact_taylor_budget hφ hcφ
  obtain ⟨M,hM⟩ := hφ.continuous.bounded_above_of_compact_support hcφ
  refine ⟨C,hC,?_⟩
  intro B x
  let μ := autoLinearBallProbability B
  let : IsProbabilityMeasure μ := autoLinearBallProbability_isProbability B
  let D := fderiv ℝ φ x
  have hAE : ∀ᵐ z ∂μ, ‖z‖≤ ‖B.toContinuousLinearMap‖ := autoLinearBallProbability_norm_ae B
  have hiφ : Integrable (fun z => φ (x+z)) μ :=
    Integrable.of_bound (hφ.continuous.comp (continuous_const.add continuous_id)).stronglyMeasurable.aestronglyMeasurable
      M (ae_of_all _ fun z => hM (x+z))
  have hic : Integrable (fun _ : Space n => φ x) μ := integrable_const _
  have hiD : Integrable (fun z => D z) μ := by
    apply Integrable.of_bound D.continuous.stronglyMeasurable.aestronglyMeasurable
      (‖D‖*‖B.toContinuousLinearMap‖)
    filter_upwards [hAE] with z hz
    exact (D.le_opNorm z).trans (mul_le_mul_of_nonneg_left hz (norm_nonneg D))
  have hzero : (∫ z, D z ∂μ)=0 := autoLinearBallProbability_linear_zero B D
  have heq : (∫ z, (φ (x+z)-φ x-D z) ∂μ)=autoSpatialAverage μ φ x-φ x := by
    have hsub₁ : (∫ z, (φ (x+z)-φ x-D z) ∂μ)=
        (∫ z, (φ (x+z)-φ x) ∂μ)-(∫ z, D z ∂μ) := by
      simpa only [Pi.sub_apply] using integral_sub (hiφ.sub hic) hiD
    have hsub₂ : (∫ z, (φ (x+z)-φ x) ∂μ)=
        (∫ z, φ (x+z) ∂μ)-(∫ _ : Space n, φ x ∂μ) := integral_sub hiφ hic
    rw [hsub₁,hsub₂,hzero,integral_const]
    simp only [probReal_univ,one_smul,sub_zero,autoSpatialAverage]
  have hBound : ∀ᵐ z ∂μ, ‖φ (x+z)-φ x-D z‖≤ C*‖B.toContinuousLinearMap‖^2 := by
    filter_upwards [hAE] with z hz
    rw [Real.norm_eq_abs]
    exact (hTaylor x z).trans (mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg z) (norm_nonneg _)|>.mpr hz) hC.le)
  have hh := norm_integral_le_of_norm_le_const hBound
  rw [heq] at hh
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

/-- Division by the actual squared radius cancels the actual ellipsoid size. -/
theorem auto_ellipsoid_cutoff_scaled {n : ℕ} {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hcφ : HasCompactSupport φ) : ∃ C : ℝ, 0< C ∧
      ∀ (B : Space n ≃L[ℝ] Space n) {r L : ℝ}, 0< r → 0≤ L →
        ‖B.toContinuousLinearMap‖^2≤ r^2*L → ∀ x,
        |(autoSpatialAverage (autoLinearBallProbability B) φ x-φ x)/r^2|≤ C*L := by
  obtain ⟨C,hC,hbound⟩ := auto_ellipsoid_cutoff_pointwise hφ hcφ
  refine ⟨C,hC,?_⟩
  intro B r L hr hL hB x
  rw [abs_div,abs_of_pos (sq_pos_of_pos hr)]
  apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
  exact (hbound B x).trans (by nlinarith only [mul_le_mul_of_nonneg_left hB hC.le])

end Yau.LeafProofs.L05AutonomousAux
