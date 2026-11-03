import Yau.Proofs.C03PoleLimitFatou
import Yau.Proofs.C03PoleLimitLocal

/-! The actual coordinate-pole bounds give finite source critical mass with exponent n+1. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
namespace Yau.Proofs.C03Aux.PoleLimit
open Yau Yau.NodeProofs.P03Aux
variable {n : ℕ}

theorem finite_critical_norm_of_coordinate_poles (f : ComplexVector n → ℂ)
    (θ : ComplexVector n → ComplexVector n) (φ : ComplexVector n → ℝ)
    (R : ℝ) (hR : 0 < R) (hθ : ContDiffOn ℝ 1 θ (ball 0 R)) (hθ0 : θ 0 = 0)
    (hθNZ : ∀ z ∈ ball (0 : ComplexVector n) R, z ≠ 0 → θ z ≠ 0)
    (hφ : ContinuousOn φ (ball 0 R))
    (hf : AEStronglyMeasurable f ((volume : Measure (ComplexVector n)).restrict (ball 0 R)))
    (B : ℝ) (hb : ∀ j : ℕ, (∫⁻ z in ball (0 : ComplexVector n) R,
      ENNReal.ofReal (‖f z‖ ^ 2 * Real.exp (-φ z) *
        Real.exp (-((n + 1 : ℕ) : ℝ) * Real.log (‖θ z‖ ^ 2 + poleEpsilon j)))) ≤
          ENNReal.ofReal B) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      (∫⁻ z in ball (0 : ComplexVector n) r,
        ENNReal.ofReal (‖f z‖ ^ 2 * ‖z‖ ^ (-2 * ((n : ℝ) + 1)))) < (⊤ : ℝ≥0∞) := by
  have hFatou := coordinate_pole_fatou f θ φ R B hθ.continuousOn hφ hf hb
  obtain ⟨r, L, M, hr, hrR, hL, hlocal⟩ := exists_local_coordinate_bounds θ φ R hR hθ hθ0 hφ
  let C := Real.exp M * L ^ (2 * (n + 1))
  have hC : 0 ≤ C := mul_nonneg (Real.exp_pos _).le
    (pow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hL) _)
  refine ⟨r, hr, hrR, ?_⟩
  calc
    _ ≤ ∫⁻ z in ball (0 : ComplexVector n) r, ENNReal.ofReal (C *
        (‖f z‖ ^ 2 * Real.exp (-φ z) * (‖θ z‖ ^ (2 * (n + 1)))⁻¹)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      exact ENNReal.ofReal_le_ofReal (critical_density_comparison f θ φ L M hL z
        (hlocal z hz).1 (hlocal z hz).2 (hθNZ z (ball_subset_ball hrR.le hz)))
    _ = ENNReal.ofReal C * ∫⁻ z in ball (0 : ComplexVector n) r,
        ENNReal.ofReal (‖f z‖ ^ 2 * Real.exp (-φ z) * (‖θ z‖ ^ (2 * (n + 1)))⁻¹) := by
      simp_rw [ENNReal.ofReal_mul hC]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * ∫⁻ z in ball (0 : ComplexVector n) R,
        ENNReal.ofReal (‖f z‖ ^ 2 * Real.exp (-φ z) * (‖θ z‖ ^ (2 * (n + 1)))⁻¹) :=
      mul_le_mul' le_rfl (lintegral_mono_set (ball_subset_ball hrR.le))
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal B := mul_le_mul' le_rfl hFatou
    _ < (⊤ : ℝ≥0∞) := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

end Yau.Proofs.C03Aux.PoleLimit
