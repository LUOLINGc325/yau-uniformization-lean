import Yau.Proofs.P03PoleSequence

/-! Qualitative local coordinate and base-weight comparisons, with no uniform-distortion claim. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace Yau.Proofs.C03Aux.PoleLimit
open Yau
variable {n : ℕ}

theorem exists_local_coordinate_bounds (θ : ComplexVector n → ComplexVector n)
    (φ : ComplexVector n → ℝ) (R : ℝ) (hR : 0 < R)
    (hθ : ContDiffOn ℝ 1 θ (ball 0 R)) (hθ0 : θ 0 = 0)
    (hφ : ContinuousOn φ (ball 0 R)) :
    ∃ r L M : ℝ, 0 < r ∧ r < R ∧ 1 ≤ L ∧
      ∀ z ∈ ball (0 : ComplexVector n) r, ‖θ z‖ ≤ L * ‖z‖ ∧ φ z ≤ M := by
  have hθat : ContDiffAt ℝ 1 θ 0 :=
    (hθ 0 (mem_ball_self hR)).contDiffAt (ball_mem_nhds 0 hR)
  obtain ⟨K, S, hS, hLip⟩ := hθat.exists_lipschitzOnWith
  have hφat : ContinuousAt φ 0 :=
    (hφ 0 (mem_ball_self hR)).continuousAt (ball_mem_nhds 0 hR)
  have hφb : ∀ᶠ z in 𝓝 (0 : ComplexVector n), φ z < φ 0 + 1 :=
    hφat.eventually (Iio_mem_nhds (by linarith : φ 0 < φ 0 + 1))
  have hN : S ∩ {z | φ z < φ 0 + 1} ∩ ball (0 : ComplexVector n) (R / 2) ∈ 𝓝 0 :=
    inter_mem (inter_mem hS hφb) (ball_mem_nhds _ (half_pos hR))
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.mp hN
  let r := min ε (R / 2)
  have hr : 0 < r := lt_min hε (half_pos hR)
  have hrε : r ≤ ε := min_le_left _ _
  have hrR : r < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  have h0S : (0 : ComplexVector n) ∈ S := (hεN (mem_ball_self hε)).1.1
  refine ⟨r, max 1 (K : ℝ), φ 0 + 1, hr, hrR, le_max_left _ _, ?_⟩
  intro z hz
  have hzN := hεN (ball_subset_ball hrε hz)
  have hb := hLip.dist_le_mul z hzN.1.1 0 h0S
  rw [hθ0, dist_zero_right, dist_zero_right] at hb
  exact ⟨hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)), hzN.1.2.le⟩

theorem critical_power_eq (z : ComplexVector n) :
    ‖z‖ ^ (-2 * ((n : ℝ) + 1)) = (‖z‖ ^ (2 * (n + 1)))⁻¹ := by
  have he : -2 * ((n : ℝ) + 1) = -((2 * (n + 1) : ℕ) : ℝ) := by push_cast; ring
  rw [he, Real.rpow_neg (norm_nonneg z), Real.rpow_natCast]

theorem critical_density_comparison (f : ComplexVector n → ℂ)
    (θ : ComplexVector n → ComplexVector n) (φ : ComplexVector n → ℝ)
    (L M : ℝ) (hL : 1 ≤ L) (z : ComplexVector n)
    (hθ : ‖θ z‖ ≤ L * ‖z‖) (hφ : φ z ≤ M) (hNZ : z ≠ 0 → θ z ≠ 0) :
    ‖f z‖ ^ 2 * ‖z‖ ^ (-2 * ((n : ℝ) + 1)) ≤
      (Real.exp M * L ^ (2 * (n + 1))) *
        (‖f z‖ ^ 2 * Real.exp (-φ z) * (‖θ z‖ ^ (2 * (n + 1)))⁻¹) := by
  rw [critical_power_eq]
  by_cases hz : z = 0
  · subst z
    simp only [norm_zero, zero_pow (by omega : 2 * (n + 1) ≠ 0), inv_zero, mul_zero]
    positivity
  · have hpθ : 0 < ‖θ z‖ ^ (2 * (n + 1)) := pow_pos (norm_pos_iff.mpr (hNZ hz)) _
    have hpz : 0 < ‖z‖ ^ (2 * (n + 1)) := pow_pos (norm_pos_iff.mpr hz) _
    have hpow : ‖θ z‖ ^ (2 * (n + 1)) ≤ L ^ (2 * (n + 1)) * ‖z‖ ^ (2 * (n + 1)) := by
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hθ (2 * (n + 1))
    have hi : (‖z‖ ^ (2 * (n + 1)))⁻¹ ≤
        L ^ (2 * (n + 1)) * (‖θ z‖ ^ (2 * (n + 1)))⁻¹ := by
      apply (le_mul_inv_iff₀ hpθ).mpr
      apply (inv_mul_le_iff₀' hpz).mpr
      exact hpow
    have he : 1 ≤ Real.exp M * Real.exp (-φ z) := by
      rw [← Real.exp_add]
      have hdiff : 0 ≤ M + -φ z := by linarith
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hdiff
    calc
      _ ≤ ‖f z‖ ^ 2 * (L ^ (2 * (n + 1)) * (‖θ z‖ ^ (2 * (n + 1)))⁻¹) :=
        mul_le_mul_of_nonneg_left hi (sq_nonneg _)
      _ = L ^ (2 * (n + 1)) * (‖f z‖ ^ 2 * (‖θ z‖ ^ (2 * (n + 1)))⁻¹) := by ring
      _ ≤ (Real.exp M * Real.exp (-φ z)) *
          (L ^ (2 * (n + 1)) * (‖f z‖ ^ 2 * (‖θ z‖ ^ (2 * (n + 1)))⁻¹)) :=
        le_mul_of_one_le_left (by positivity) he
      _ = _ := by ring

end Yau.Proofs.C03Aux.PoleLimit
