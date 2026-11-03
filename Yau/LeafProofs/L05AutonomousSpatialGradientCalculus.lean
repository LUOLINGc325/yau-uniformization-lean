import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Interval
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L05AutonomousAux

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A bound on the actual Hessian gives the actual spatial gradient Lipschitz estimate. -/
theorem spatialGradient_smooth_lipschitz {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    {R B : ℝ} (hB : ∀ z ∈ closedBall (0 : V) R, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ B)
    {x y : V} (hx : x ∈ closedBall (0 : V) R) (hy : y ∈ closedBall (0 : V) R) :
    ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ B * ‖y - x‖ := by
  have hd : ∀ z : V, HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z := by
    intro z
    exact ((hf.contDiffAt.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num)).hasFDerivAt
  exact (convex_closedBall (0 : V) R).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hd z).hasFDerivWithinAt) hB hx hy

/-- First-order Taylor's estimate follows from the actual derivative on the full segment. -/
theorem spatialGradient_smooth_remainder {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    {R B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ z ∈ closedBall (0 : V) R, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ B)
    {x y : V} (hx : x ∈ closedBall (0 : V) R) (hy : y ∈ closedBall (0 : V) R) :
    |f y - f x - fderiv ℝ f x (y - x)| ≤ B * ‖y - x‖ ^ 2 := by
  let g : V → ℝ := fun z => f z - f x - fderiv ℝ f x (z - x)
  have hseg : segment ℝ x y ⊆ closedBall (0 : V) R := (convex_closedBall (0 : V) R).segment_subset hx hy
  have hD (z : V) : HasFDerivAt g (fderiv ℝ f z - fderiv ℝ f x) z := by
    have hs := (hasFDerivAt_id (𝕜 := ℝ) z).sub_const x
    exact ((hf.differentiable (by simp) z).hasFDerivAt.sub_const (f x)).sub
      ((fderiv ℝ f x).hasFDerivAt.comp z hs)
  have hDbound : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ B * ‖y - x‖ := by
    intro z hz
    exact (spatialGradient_smooth_lipschitz hf hB hx (hseg hz)).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hB0)
  have hmean := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hD z).hasFDerivWithinAt) hDbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [g, sub_self, map_zero, sub_zero, Real.norm_eq_abs, pow_two, mul_assoc] using hmean

/-- Buffered finite differences bound the genuine Frechet derivative, with no unit-vector existence. -/
theorem spatialGradient_interpolation {f g : V → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {R s step B delta : ℝ} (hstep : 0 < step) (hbuffer : s + step ≤ R)
    (hB0 : 0 ≤ B) (hdelta : 0 ≤ delta)
    (hfB : ∀ z ∈ closedBall (0 : V) R, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ B)
    (hgB : ∀ z ∈ closedBall (0 : V) R, ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ B)
    (hfg : ∀ z ∈ closedBall (0 : V) R, |f z - g z| ≤ delta)
    {x : V} (hx : x ∈ closedBall (0 : V) s) :
    ‖fderiv ℝ f x - fderiv ℝ g x‖ ≤ 2 * delta / step + 2 * B * step := by
  have hsR : s ≤ R := by linarith
  have hxR := closedBall_subset_closedBall hsR hx
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  let y := x + step • v
  have hy : y ∈ closedBall (0 : V) R := by
    rw [mem_closedBall, dist_zero_right]
    have hxN : ‖x‖ ≤ s := by simpa using hx
    calc
      _ ≤ ‖x‖ + ‖step • v‖ := norm_add_le _ _
      _ = ‖x‖ + step := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hstep, hv, mul_one]
      _ ≤ R := by linarith
  have hfn := spatialGradient_smooth_remainder hf hB0 hfB hxR hy
  have hgn := spatialGradient_smooth_remainder hg hB0 hgB hxR hy
  have hnorm : ‖y - x‖ = step := by
    simp only [y, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hstep, hv, mul_one]
  have hfun : fderiv ℝ f x (y - x) - fderiv ℝ g x (y - x) =
      step * ((fderiv ℝ f x - fderiv ℝ g x) v) := by
    simp [y, map_smul, smul_eq_mul, sub_apply]
    ring
  have hid : fderiv ℝ f x (y - x) - fderiv ℝ g x (y - x) =
      (f y - g y) - (f x - g x) -
        (f y - f x - fderiv ℝ f x (y - x)) +
        (g y - g x - fderiv ℝ g x (y - x)) := by ring
  have hb : |step * ((fderiv ℝ f x - fderiv ℝ g x) v)| ≤ 2 * delta + 2 * B * step ^ 2 := by
    rw [← hfun, hid]
    calc
      _ ≤ |f y - g y| + |f x - g x| + |f y - f x - fderiv ℝ f x (y - x)| +
          |g y - g x - fderiv ℝ g x (y - x)| := by
        exact (abs_add_le _ _).trans
          (add_le_add ((abs_sub _ _).trans (add_le_add (abs_sub _ _) (le_refl _))) (le_refl _))
      _ ≤ delta + delta + B * step ^ 2 + B * step ^ 2 := by
        gcongr
        · exact hfg y hy
        · exact hfg x hxR
        · simpa only [hnorm] using hfn
        · simpa only [hnorm] using hgn
      _ = _ := by ring
  rw [abs_mul, abs_of_pos hstep] at hb
  rw [Real.norm_eq_abs]
  calc
    _ ≤ (2 * delta + 2 * B * step ^ 2) / step :=
      (le_div_iff₀ hstep).mpr (by nlinarith [hb])
    _ = _ := by field_simp [hstep.ne']

end Yau.LeafProofs.L05AutonomousAux
