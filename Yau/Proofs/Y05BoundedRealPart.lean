import Yau.Geometry.Basic
import Mathlib.Analysis.Complex.Schwarz

noncomputable section
open Set

namespace Yau.Proofs.Y05Aux

open Yau

variable {n : ℕ}

theorem mobius_denominator_ne_zero {M : ℝ} (hM : 0 < M) {w : ℂ} (hw : w.re ≤ M) :
    (2 * M : ℂ) - w ≠ 0 := by
  intro h
  have H := congrArg Complex.re h
  norm_num [Complex.sub_re, Complex.mul_re] at H
  linarith

theorem mobius_norm_le_one {M : ℝ} (hM : 0 < M) {w : ℂ} (hw : w.re ≤ M) :
    ‖w / ((2 * M : ℂ) - w)‖ ≤ 1 := by
  rw [norm_div, div_le_one₀ (norm_pos_iff.mpr (mobius_denominator_ne_zero hM hw))]
  apply (sq_le_sq₀ (norm_nonneg w) (norm_nonneg _)).mp
  rw [Complex.sq_norm, Complex.sq_norm]
  norm_num [Complex.normSq_apply]
  nlinarith

/-- A fixed concentric-ball estimate follows from the actual Schwarz lemma.
The branch is normalized at zero, so no imaginary constant enters the bound. -/
theorem boundedRe_norm_on_half_ball {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    {P : ComplexVector n → ℂ} (hP : DifferentiableOn ℂ P (Metric.ball 0 r))
    (hP0 : P 0 = 0) (hRe : ∀ z ∈ Metric.ball (0 : ComplexVector n) r, (P z).re ≤ M) :
    ∀ z ∈ Metric.ball (0 : ComplexVector n) (r / 2), ‖P z‖ ≤ 2 * M := by
  let Q : ComplexVector n → ℂ := fun z => P z / ((2 * M : ℂ) - P z)
  have hden (z : ComplexVector n) (hz : z ∈ Metric.ball (0 : ComplexVector n) r) :
      (2 * M : ℂ) - P z ≠ 0 := mobius_denominator_ne_zero hM (hRe z hz)
  have hD : DifferentiableOn ℂ (fun z : ComplexVector n => (2 * M : ℂ) - P z)
      (Metric.ball 0 r) := (differentiableOn_const (2 * M : ℂ)).sub hP
  have hQ : DifferentiableOn ℂ Q (Metric.ball 0 r) := by
    convert! hP.mul (hD.inv hden) using 1
    all_goals rfl
  have hQ0 : Q 0 = 0 := by simp only [Q, hP0, zero_div]
  have hmaps : MapsTo Q (Metric.ball 0 r) (Metric.closedBall (Q 0) 1) := by
    intro z hz
    rw [hQ0, Metric.mem_closedBall, dist_zero_right]
    exact mobius_norm_le_one hM (hRe z hz)
  intro z hz
  have hz' : z ∈ Metric.ball (0 : ComplexVector n) r :=
    Metric.ball_subset_ball (by linarith) hz
  have H := Complex.dist_le_div_mul_dist_of_mapsTo_ball hQ hmaps hz'
  rw [hQ0, dist_zero_right, dist_zero_right] at H
  have hzNorm : ‖z‖ < r / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hQhalf : ‖Q z‖ ≤ 1 / 2 := by
    have hdiv : ‖z‖ / r < 1 / 2 := (div_lt_iff₀ hr).mpr (by
      simpa only [div_eq_mul_inv, mul_comm, one_mul] using hzNorm)
    rw [div_mul_eq_mul_div, one_mul] at H
    linarith
  have hdenNorm : ‖(2 * M : ℂ) - P z‖ ≤ 2 * M + ‖P z‖ := by
    have H := norm_sub_le (2 * M : ℂ) (P z)
    simpa [abs_of_pos hM] using H
  have hvalue : P z = Q z * ((2 * M : ℂ) - P z) :=
    (div_mul_cancel₀ (P z) (hden z hz')).symm
  have hnorm : ‖P z‖ ≤ ‖Q z‖ * (2 * M + ‖P z‖) := by
    calc
      ‖P z‖ = ‖Q z‖ * ‖(2 * M : ℂ) - P z‖ := by rw [← norm_mul, ← hvalue]
      _ ≤ _ := mul_le_mul_of_nonneg_left hdenNorm (norm_nonneg _)
  have Hbound := hnorm.trans (mul_le_mul_of_nonneg_right hQhalf (by positivity))
  nlinarith

end Yau.Proofs.Y05Aux
