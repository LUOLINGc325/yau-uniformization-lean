import Yau.Proofs.C03EnvelopeSmoothingSubtract
import Yau.Proofs.C03EnvelopeSmoothingCircle
import Yau.Proofs.C03EnvelopeSmoothingTrace

/-! The fixed normalized convolution inherits the exact half-metric Levi lower bound. -/
noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder Convolution
open Filter Set Metric MeasureTheory
namespace Yau.Proofs.C03Aux.EnvelopeSmoothing
open Yau Yau.Blueprint Yau.LeafProofs L22Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
variable {n : ℕ}

theorem affine_disc_displacement_lt (z b v : ComplexVector n) (d : ℝ) (hd : 0 < d)
    (hb : ‖b‖ ≤ d) (r : ℝ) (hr : |r| < d / (‖v‖ + 1))
    (a : ℂ) (ha : ‖a‖ ≤ 1) : dist ((z - b) + a • (r • v)) z < 3 * d := by
  have hden : 0 < ‖v‖ + 1 := by positivity
  have hsmall : |r| * (‖v‖ + 1) < d := (lt_div_iff₀ hden).mp hr
  have hmove : ‖a • (r • v)‖ < d := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs]
    calc
      ‖a‖ * (|r| * ‖v‖) ≤ |r| * ‖v‖ := mul_le_of_le_one_left (by positivity) ha
      _ ≤ |r| * (‖v‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg r)
      _ < d := hsmall
  rw [dist_eq_norm]
  calc
    ‖(z - b) + a • (r • v) - z‖ = ‖a • (r • v) - b‖ := by congr 1; abel
    _ ≤ ‖a • (r • v)‖ + ‖b‖ := norm_sub_le _ _
    _ < d + d := add_lt_add_of_lt_of_le hmove hb
    _ < 3 * d := by linarith

theorem normalizedConvolution_strict_at
    (O S : Set (ComplexVector n)) (f F : ComplexVector n → ℝ)
    (hfc : ContinuousOn f O) (hFc : Continuous F) (hEq : EqOn F f O)
    (H : ComplexVector n → Herm n) (kappa : ℝ) (hkappa : 0 < kappa)
    (hsupport : PlanarLowerSupports f S (fun q v => 4 * kappa * matrixQuadratic (H q) v))
    (φ : ContDiffBump (0 : ComplexVector n)) (z : ComplexVector n)
    (d : ℝ) (hd : 0 < d) (hφ : φ.rOut ≤ d)
    (hO : ball z (3 * d) ⊆ O) (hS : ball z (3 * d) ⊆ S)
    (hHz : (H z).IsHermitian)
    (hcompare : ∀ q ∈ ball z (3 * d), ∀ v,
      (1 / 2 : ℝ) * matrixQuadratic (H z) v ≤ matrixQuadratic (H q) v) :
    HermLE (((kappa / 2 : ℝ) : ℂ) • H z)
      (leviC (normalizedConvolution φ F) z) := by
  have hgs := normalizedConvolution_smooth φ F hFc
  apply hermLE_levi_of_quadratic_lower (normalizedConvolution φ F) hgs z (H z) hHz (kappa / 2)
  intro v
  let A : ℝ := (kappa / 2) * matrixQuadratic (H z) v
  change A ≤ complexLeviQuadratic (normalizedConvolution φ F) z v
  apply complexLeviQuadratic_lower_of_corrected_circles (normalizedConvolution φ F) hgs z v A
  let eta : ℝ := d / (‖v‖ + 1)
  have heta : 0 < eta := div_pos hd (by positivity)
  filter_upwards [ball_mem_nhds (0 : ℝ) heta] with r hr
  have hr' : |r| < d / (‖v‖ + 1) := by
    simpa only [eta, mem_ball, Real.dist_eq, sub_zero] using hr
  have hlocalSupport : PlanarLowerSupports f (ball z (3 * d))
      (fun q w => 4 * kappa * matrixQuadratic (H q) w) :=
    fun q hq w => hsupport q (hS hq) w
  have hcircle : ∀ b ∈ closedBall (0 : ComplexVector n) φ.rOut,
      F (z - b) + A * r ^ 2 ≤
        circleAverage (fun theta => F (z + Complex.exp (theta * Complex.I) • (r • v) - b)) := by
    intro b hb
    have hb' : ‖b‖ ≤ d := (by simpa only [mem_closedBall, dist_zero_right] using hb : ‖b‖ ≤ φ.rOut).trans hφ
    have hdisc : ∀ a : ℂ, ‖a‖ ≤ 1 → (z - b) + a • (r • v) ∈ ball z (3 * d) :=
      fun a ha => mem_ball.mpr (affine_disc_displacement_lt z b v d hd hb' r hr' a ha)
    have hbound : ∀ a ∈ ball (0 : ℂ) 1,
        4 * (A * r ^ 2) ≤ 4 * kappa * matrixQuadratic (H ((z - b) + a • (r • v))) (r • v) := by
      intro a ha
      have ha' : ‖a‖ ≤ 1 := (by simpa only [mem_ball, dist_zero_right] using ha : ‖a‖ < 1).le
      have hcmp := hcompare _ (hdisc a ha') v
      calc
        4 * (A * r ^ 2) = (4 * kappa * r ^ 2) * ((1 / 2 : ℝ) * matrixQuadratic (H z) v) := by
          dsimp only [A]
          ring
        _ ≤ (4 * kappa * r ^ 2) * matrixQuadratic (H ((z - b) + a • (r • v))) v :=
          mul_le_mul_of_nonneg_left hcmp (by positivity)
        _ = _ := by rw [matrixQuadratic_real_smul]; ring
    have hfmean := corrected_affine_circle (ball z (3 * d)) f (hfc.mono hO)
      _ hlocalSupport (z - b) (r • v) (A * r ^ 2) hdisc hbound
    have hcenter : F (z - b) = f (z - b) := hEq (hO (by
      simpa only [zero_smul, add_zero] using hdisc 0 (by simp)))
    have hcircleEq : (fun theta : ℝ => F (z + Complex.exp (theta * Complex.I) • (r • v) - b)) =
        (fun theta : ℝ => f ((z - b) + Complex.exp (theta * Complex.I) • (r • v))) := by
      funext theta
      have hpoint : z + Complex.exp (theta * Complex.I) • (r • v) - b =
          (z - b) + Complex.exp (theta * Complex.I) • (r • v) := by abel
      rw [hpoint]
      exact hEq (hO (hdisc _ (by simp)))
    rw [hcenter, hcircleEq]
    exact hfmean
  have hmean := normalizedConvolution_circle_correction φ F hFc z (r • v) (A * r ^ 2) hcircle
  simpa only [smul_comm r] using hmean

end Yau.Proofs.C03Aux.EnvelopeSmoothing
