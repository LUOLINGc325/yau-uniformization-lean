import Yau.LeafProofs.L05AutonomousDeficitHarnackPower
import Yau.LeafProofs.L05AutonomousSecondLimit
import Yau.LeafProofs.L05AutonomousHarnackMean
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- A concrete positive dyadic sequence, chosen strictly inside the finite-difference buffer. -/
def autoDeficitDyadic (h0 : ℝ) (j : ℕ) : ℝ := (h0/2)*(1/2)^j

theorem autoDeficitDyadic_pos {h0 : ℝ} (hh0 : 0 < h0) (j : ℕ) :
    0 < autoDeficitDyadic h0 j :=
  mul_pos (div_pos hh0 (by norm_num)) (pow_pos (by norm_num) _)

theorem autoDeficitDyadic_abs_lt {h0 : ℝ} (hh0 : 0 < h0) (j : ℕ) :
    |autoDeficitDyadic h0 j| < h0 := by
  rw [abs_of_pos (autoDeficitDyadic_pos hh0 j)]
  have hp : (1/2 : ℝ)^j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hp (div_nonneg hh0.le (by norm_num : (0 : ℝ) ≤ 2))
  change (h0/2)*(1/2)^j < h0
  linarith

theorem autoDeficitDyadic_tendsto_right {h0 : ℝ} (hh0 : 0 < h0) :
    Tendsto (autoDeficitDyadic h0) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall (autoDeficitDyadic_pos hh0)⟩
  have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)).const_mul (h0/2)
  change Tendsto (fun j : ℕ => (h0/2)*(1/2)^j) atTop (𝓝 (0 : ℝ))
  simpa only [mul_zero] using hh

/-- The normalized early mean converges along the actual dyadics, without any original jet input. -/
theorem auto_second_deficit_dyadic_mean_tendsto {n : ℕ} (c : Space n)
    {R T p M B h0 : ℝ} (hR : 0 < R) (hp : 0 < p) (hB : 0 ≤ B) (hh0 : 0 < h0)
    (u w : Point n → ℝ) (e : Space n) (hu : Continuous u) (hw : Measurable w)
    (hb : ∀ h, h ≠ 0 → |h| < h0 → ∀ z ∈ autoClosed c R T,
      |autoSecond u e h z| ≤ B ∧ autoSecond u e h z ≤ M)
    (hlim : ∀ᵐ z ∂(volume : Measure (Point n)).restrict (autoEarly c R T),
      Tendsto (fun h : ℝ => autoSecond u e h z) (𝓝[>] 0) (𝓝 (w z))) :
    Tendsto (fun j => autoLpMean (autoEarly c R T) p
      (fun z => M-autoSecond u e (autoDeficitDyadic h0 j) z)) atTop
      (𝓝 (autoLpMean (autoEarly c R T) p (fun z => M-w z))) := by
  let μ := (volume : Measure (Point n)).restrict (autoEarly c R T)
  letI l05DeficitDyadicEarlyFinite : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr (autoEarly_measure_ne_top c R T)
  have hEarly : autoEarly c R T ⊆ autoClosed c R T := by
    intro z hz
    have ho := autoEarly_subset_open c hR T hz
    exact ⟨Metric.ball_subset_closedBall ho.1, Ioo_subset_Icc_self ho.2⟩
  have hj : ∀ j, ∀ᵐ z ∂μ,
      |autoSecond u e (autoDeficitDyadic h0 j) z| ≤ B ∧
        autoSecond u e (autoDeficitDyadic h0 j) z ≤ M := by
    intro j
    exact (ae_restrict_mem (autoEarly_isOpen c R T).measurableSet).mono
      (fun z hz => hb _ (autoDeficitDyadic_pos hh0 j).ne'
        (autoDeficitDyadic_abs_lt hh0 j) z (hEarly hz))
  have hseq : ∀ᵐ z ∂μ,
      Tendsto (fun j => autoSecond u e (autoDeficitDyadic h0 j) z) atTop (𝓝 (w z)) :=
    hlim.mono (fun z hz => hz.comp (autoDeficitDyadic_tendsto_right hh0))
  have hIntegral := (auto_deficit_power_integral_tendsto μ hp hB
    (fun j => autoSecond u e (autoDeficitDyadic h0 j)) w
    (fun j => (autoSecond_continuous hu e _).measurable) hw hseq hj).2.2.2
  have hNormalized := hIntegral.div_const
    (((volume : Measure (Point n)) (autoEarly c R T)).toReal)
  have hPower := (Real.continuous_rpow_const
    (le_of_lt (one_div_pos.mpr hp))).tendsto
      ((∫ z, (M-w z)^p ∂μ)/((volume : Measure (Point n)) (autoEarly c R T)).toReal)
  exact hPower.comp hNormalized

end Yau.LeafProofs.L05AutonomousAux
