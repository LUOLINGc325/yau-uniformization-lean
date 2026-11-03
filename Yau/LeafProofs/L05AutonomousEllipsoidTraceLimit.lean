import Yau.LeafProofs.L05AutonomousMeanSecondLimit
import Yau.LeafProofs.L05AutonomousBallMeanAffine
import Yau.LeafProofs.L05AutonomousEllipsoidScaling
import Yau.LeafProofs.L05AutonomousCutoffEnergy

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The small-scale bound identifies and bounds the genuine Hessian contraction. -/
theorem auto_trace_bound_of_ellipsoid_second {n : ℕ} (hn : 0 < n)
    {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) (A : Mat n) (S : Space n ≃L[ℝ] Space n)
    (hST : ∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
      (∑ k : Yau.RIdx n, H (S (Yau.realVec k)) (S (Yau.realVec k)))=
        ∑ i, ∑ j, A i j*H (Yau.realVec i) (Yau.realVec j))
    {C r0 : ℝ} (hr0 : 0 < r0) (x : Space n)
    (hbound : ∀ (r : ℝ) (hr : 0 < r), r < r0 →
      |(autoSpatialAverage (autoLinearBallProbability (autoRadiusLinearEquiv S r hr)) f x-f x)/r^2| ≤ C) :
    |Matrix.trace (A*secondFDerivMatrix f x)| ≤ C*(2*((2*n : ℝ)+2)) := by
  let g : Space n → ℝ := fun y => f (x+S y)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add S.contDiff)
  have hLap : autoBallMeanLaplacian g 0=Matrix.trace (A*secondFDerivMatrix f x) := by
    rw [auto_energy_trace_eq hf A x]
    calc
      _ = ∑ k : Yau.RIdx n, (fderiv ℝ (fderiv ℝ f) x) (S (Yau.realVec k)) (S (Yau.realVec k)) := by
        unfold autoBallMeanLaplacian
        apply Finset.sum_congr rfl
        intro k _
        have h := auto_ballMean_affine_second S.toContinuousLinearMap x 0
          (hf.contDiffAt.of_le (by simp)) (Yau.realVec k)
        simpa only [map_zero,add_zero,g,ContinuousLinearEquiv.coe_coe] using h
      _ = _ := hST _
  have hlim := auto_ball_mean_second_limit hn hg
  rw [hLap] at hlim
  have hboundEventually : ∀ᶠ r : ℝ in 𝓝[>] 0,
      |((∫ y in Metric.ball (0 : Space n) r, g y)/(volume : Measure (Space n)).real (Metric.ball 0 r)-g 0)/r^2| ≤ C := by
    have hevent : Ioo (0 : ℝ) r0 ∈ 𝓝[>] 0 :=
      mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨r0,hr0,subset_rfl⟩
    filter_upwards [hevent] with r hr
    have h := hbound r hr.1 hr.2
    rw [auto_radius_ellipsoid_average S hr.1] at h
    simpa only [g,map_zero,add_zero] using h
  have hnorm : |Matrix.trace (A*secondFDerivMatrix f x)/(2*((2*n : ℝ)+2))| ≤ C :=
    le_of_tendsto (continuous_abs.tendsto _ |>.comp hlim) hboundEventually
  have hD : 0 < 2*((2*n : ℝ)+2) := by positivity
  rwa [abs_div,abs_of_pos hD,div_le_iff₀ hD] at hnorm

end Yau.LeafProofs.L05AutonomousAux
