import Yau.LeafProofs.L05AutonomousEllipsoidAverage
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- Actual Haar scaling cancels with the actual ball volume in the normalized mean. -/
theorem auto_radius_ellipsoid_average {n : ℕ} (S : Space n ≃L[ℝ] Space n) {r : ℝ} (hr : 0< r)
    (f : Space n → ℝ) (x : Space n) :
    autoSpatialAverage (autoLinearBallProbability (autoRadiusLinearEquiv S r hr)) f x=
      (∫ y in Metric.ball (0 : Space n) r, f (x+S y))/(volume : Measure (Space n)).real (Metric.ball 0 r) := by
  rw [autoLinearBallProbability_average]
  have hs := (volume : Measure (Space n)).setIntegral_comp_smul_of_pos (fun y => f (x+S y))
    (Metric.ball (0 : Space n) 1) hr
  rw [smul_ball hr.ne',smul_zero,Real.norm_eq_abs,abs_of_pos hr,mul_one,complexVector_finrank_real,smul_eq_mul] at hs
  have heq : (fun y : Space n => f (x+autoRadiusLinearEquiv S r hr y))=(fun y => f (x+S (r • y))) := by
    funext y
    rw [autoRadiusLinearEquiv_apply,map_smul]
  rw [heq,hs,auto_ball_volume_scale n hr]
  have hv : (volume : Measure (Space n)).real (Metric.ball (0 : Space n) 1)≠0 := (auto_ball_volume_pos n zero_lt_one).ne'
  have hp : r^(2*n)≠0 := pow_ne_zero _ hr.ne'
  field_simp

end Yau.LeafProofs.L05AutonomousAux
