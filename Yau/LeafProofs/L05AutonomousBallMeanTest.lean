import Yau.LeafProofs.L05AutonomousBallMeanRadial
import Yau.LeafProofs.L05AutonomousBallMeanSource

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_ballMean_radial_test_contDiff {n : ℕ} {phi : ℝ → ℝ} {a R : ℝ}
    (ha : 0 < a) (hphi : ContDiff ℝ 2 phi) (hs : tsupport phi ⊆ Icc a R) :
    ContDiff ℝ 2 (fun x : Space n => phi ‖x‖) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have hEq : (fun x : Space n => phi ‖x‖)=ᶠ[𝓝 0] (fun _ => (0 : ℝ)) := by
      filter_upwards [Metric.ball_mem_nhds (0 : Space n) ha] with y hy
      apply image_eq_zero_of_notMem_tsupport
      intro hyphi
      have h := (hs hyphi).1
      have hn : ‖y‖ < a := by simpa only [mem_ball,dist_zero_right] using hy
      exact hn.not_ge h
    exact contDiffAt_const.congr_of_eventuallyEq hEq
  · exact hphi.contDiffAt.comp x (contDiffAt_norm ℝ hx)

theorem auto_ballMean_radial_test_tsupport {n : ℕ} {phi : ℝ → ℝ} {a R : ℝ}
    (hs : tsupport phi ⊆ Icc a R) :
    tsupport (fun x : Space n => phi ‖x‖) ⊆ closedBall 0 R := by
  apply closure_minimal ?_ isClosed_closedBall
  intro x hx
  have hP : ‖x‖ ∈ tsupport phi := subset_closure hx
  simpa only [mem_closedBall,dist_zero_right] using (hs hP).2

theorem auto_ballMean_radial_test_compact {n : ℕ} {phi : ℝ → ℝ} {a R : ℝ}
    (hs : tsupport phi ⊆ Icc a R) :
    HasCompactSupport (fun x : Space n => phi ‖x‖) :=
  (isCompact_closedBall (0 : Space n) R).of_isClosed_subset (isClosed_tsupport _)
    (auto_ballMean_radial_test_tsupport hs)

theorem auto_ballMean_radial_test_ibp {n : ℕ} {phi : ℝ → ℝ} {a R r : ℝ}
    (ha : 0 < a) (hR : R ≤ r) (hphi : ContDiff ℝ 2 phi) (hs : tsupport phi ⊆ Icc a R)
    {f : Space n → ℝ} (hf : ∀ x∈closedBall 0 r, ContDiffAt ℝ 2 f x) :
    (∫ x : Space n, phi ‖x‖*autoBallMeanLaplacian f x)=
      ∫ x : Space n, f x*autoBallMeanLaplacian (fun y : Space n => phi ‖y‖) x := by
  apply auto_ballMean_local_laplacian_ibp ?_
    (auto_ballMean_radial_test_contDiff ha hphi hs) (auto_ballMean_radial_test_compact hs)
  intro x hx
  exact hf x (closedBall_subset_closedBall hR (auto_ballMean_radial_test_tsupport hs hx))

end Yau.LeafProofs.L05AutonomousAux
