import Yau.LeafProofs.L05AutonomousBallMeanIntegrable
import Yau.LeafProofs.L05AutonomousBallMeanIBP

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Interval
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_ballMean_kernel_mul_continuous_integrable {n : ℕ} (hn : 0 < n)
    (omega : ℝ) {r : ℝ} (hr : 0 < r) {f : Space n → ℝ}
    (hf : ContinuousOn f (closedBall 0 r)) :
    Integrable (fun x : Space n => autoRadialGreen (2*n) omega r ‖x‖*f x) := by
  let K : Space n → ℝ := fun x => autoRadialGreen (2*n) omega r ‖x‖
  have hInt : IntegrableOn (fun x => K x*f x) (closedBall 0 r) volume :=
    (auto_ballMean_kernel_integrable hn omega hr).integrableOn.mul_continuousOn hf (isCompact_closedBall 0 r)
  have hEq : (closedBall (0 : Space n) r).indicator (fun x => K x*f x)=(fun x => K x*f x) := by
    funext x
    by_cases hx : x∈closedBall (0 : Space n) r
    · exact indicator_of_mem hx _
    · have hZero : K x=0 := by
        apply auto_radialGreen_zero_outside (2*n) omega r
        intro hs
        exact hx (by simpa only [mem_closedBall,dist_zero_right] using hs.2.le)
      rw [indicator_of_notMem hx,hZero,zero_mul]
  change Integrable (fun x => K x*f x)
  rw [← hEq]
  exact (integrable_indicator_iff measurableSet_closedBall).mpr hInt

theorem auto_ballMean_laplacian_continuousOn {n : ℕ} {f : Space n → ℝ} {S : Set (Space n)}
    (hf : ∀ x∈S, ContDiffAt ℝ 2 f x) : ContinuousOn (autoBallMeanLaplacian f) S := by
  unfold autoBallMeanLaplacian
  apply continuousOn_finsetSum
  intro i _ x hx
  exact ((((hf x hx).fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).clm_apply
    contDiffAt_const |>.clm_apply contDiffAt_const).continuousAt.continuousWithinAt

theorem auto_ballMean_kernel_source_integrable {n : ℕ} (hn : 0 < n)
    (omega : ℝ) {r : ℝ} (hr : 0 < r) {f : Space n → ℝ}
    (hf : ∀ x∈closedBall 0 r, ContDiffAt ℝ 2 f x) :
    Integrable (fun x : Space n => autoRadialGreen (2*n) omega r ‖x‖*autoBallMeanLaplacian f x) :=
  auto_ballMean_kernel_mul_continuous_integrable hn omega hr (auto_ballMean_laplacian_continuousOn hf)

end Yau.LeafProofs.L05AutonomousAux

namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_ballMean_local_linear_bound {n : ℕ} {f : Space n → ℝ} {r : ℝ} (hr : 0 < r)
    (hf : ∀ x∈closedBall 0 r, ContDiffAt ℝ 2 f x) :
    ∃ L : ℝ, 0 < L ∧ ∀ x∈closedBall 0 r, |f x-f 0| ≤ L*‖x‖ := by
  have hD : ContinuousOn (fderiv ℝ f) (closedBall 0 r) := by
    intro x hx
    exact ((hf x hx).fderiv_right (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨M,hM⟩ := ((isCompact_closedBall (0 : Space n) r).image_of_continuousOn hD.norm).bddAbove
  let L := max 1 M
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨L,hL,?_⟩
  intro x hx
  have h0 : (0 : Space n) ∈ closedBall 0 r := by simpa only [mem_closedBall,dist_self] using hr.le
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y hy => (hf y hy).differentiableAt (by norm_num))
    (fun y hy => (hM ⟨y,hy,rfl⟩).trans (le_max_right 1 M))
    (convex_closedBall (0 : Space n) r) h0 hx
  simpa only [Real.norm_eq_abs,sub_zero] using h

end Yau.LeafProofs.L05AutonomousAux
