import Yau.LeafProofs.L05AutonomousBallMeanMass

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_ball_mean_lower_zero {n : ℕ} (hn : 0 < n) {r B : ℝ} (hr : 0 < r) (_hB : 0 ≤ B)
    {f : Space n → ℝ} (hf : ∀ x∈closedBall 0 r, ContDiffAt ℝ 2 f x)
    (hlap : ∀ x∈ball 0 r, -B ≤ autoBallMeanLaplacian f x) :
    (∫ x in ball (0 : Space n) r, f x)/(volume : Measure (Space n)).real (ball 0 r)-f 0 ≥
      -B*r^2/(2*((2*n : ℝ)+2)) := by
  have hK := auto_ballMean_kernel_integrable hn (autoBallMeanOmega n) hr
  have hF := auto_ballMean_kernel_source_integrable hn (autoBallMeanOmega n) hr hf
  have hPoint (x : Space n) : (-B)*autoRadialGreen (2*n) (autoBallMeanOmega n) r ‖x‖ ≤
      autoRadialGreen (2*n) (autoBallMeanOmega n) r ‖x‖*autoBallMeanLaplacian f x := by
    by_cases hx : x∈ball (0 : Space n) r
    · have hNonneg := auto_radialGreen_nonneg (r := r) (by omega : 0 < 2*n) (auto_ballMean_omega_pos n) ‖x‖
      calc
        _ = autoRadialGreen (2*n) (autoBallMeanOmega n) r ‖x‖*(-B) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hlap x hx) hNonneg
    · have hZero : autoRadialGreen (2*n) (autoBallMeanOmega n) r ‖x‖=0 :=
        auto_radialGreen_zero_outside (2*n) (autoBallMeanOmega n) r (by
          intro hs
          exact hx (by simpa only [mem_ball,dist_zero_right] using hs.2))
      rw [hZero,mul_zero,zero_mul]
  have h := integral_mono_ae (hK.const_mul (-B)) hF (ae_of_all volume hPoint)
  rw [integral_const_mul,auto_ballMean_kernel_mass hn hr] at h
  rw [auto_ball_mean_green_zero hn hr hf]
  convert h using 1 <;> ring

end Yau.LeafProofs.L05AutonomousAux
