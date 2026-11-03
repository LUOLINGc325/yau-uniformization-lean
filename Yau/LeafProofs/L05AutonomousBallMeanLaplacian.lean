import Yau.LeafProofs.L05AutonomousBallMeanErrorIntegrable

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_ballMean_laplacian_tsupport {n : ℕ} (g : Space n → ℝ) :
    tsupport (autoBallMeanLaplacian g) ⊆ tsupport g := by
  apply closure_minimal ?_ (isClosed_tsupport g)
  intro x hx
  by_contra h
  exact hx (auto_ballMean_laplacian_zero_outside h)

theorem auto_ballMean_laplacian_integrable {n : ℕ} {g : Space n → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) : Integrable (autoBallMeanLaplacian g) := by
  have hCont : Continuous (autoBallMeanLaplacian g) := continuousOn_univ.mp
    (auto_ballMean_laplacian_continuousOn (fun x _ => hg.contDiffAt))
  have hCompact : HasCompactSupport (autoBallMeanLaplacian g) :=
    hgc.mono' (fun x hx => auto_ballMean_laplacian_tsupport g (subset_closure hx))
  exact hCont.integrable_of_hasCompactSupport hCompact

theorem auto_ballMean_test_laplacian_source_integrable {n : ℕ} (hn : 0 < n) (omega : ℝ)
    {r eta : ℝ} (hr : 0 < r) (heta : 0 < eta)
    {v : Space n → ℝ} (hv : ContinuousOn v (closedBall 0 r)) :
    Integrable (fun x : Space n => v x*autoBallMeanLaplacian
      (fun y : Space n => autoGreenTest (2*n) omega r eta ‖y‖) x) := by
  let g : Space n → ℝ := fun y => autoGreenTest (2*n) omega r eta ‖y‖
  have hPhi : ContDiff ℝ 2 (autoGreenTest (2*n) omega r eta) :=
    (auto_green_test_contDiff (by omega : 2 ≤ 2*n) omega hr heta).of_le (by norm_num)
  have hS := auto_green_test_tsupport (d := 2*n) omega r heta
  have hg : ContDiff ℝ 2 g := auto_ballMean_radial_test_contDiff heta hPhi hS
  have hgc : HasCompactSupport g := auto_ballMean_radial_test_compact hS
  have hSub : tsupport (autoBallMeanLaplacian g) ⊆ closedBall 0 r :=
    (auto_ballMean_laplacian_tsupport g).trans
      ((auto_ballMean_radial_test_tsupport hS).trans (closedBall_subset_closedBall (by linarith)))
  have hCont : Continuous (autoBallMeanLaplacian g) := continuousOn_univ.mp
    (auto_ballMean_laplacian_continuousOn (fun x _ => hg.contDiffAt))
  exact auto_ballMean_integrable_mul_compact (hv.mono hSub) hCont
    (hgc.mono' (fun x hx => auto_ballMean_laplacian_tsupport g (subset_closure hx)))

theorem auto_ballMean_test_laplacian_integral_zero {n : ℕ} (hn : 0 < n) (omega : ℝ)
    {r eta : ℝ} (hr : 0 < r) (heta : 0 < eta) :
    (∫ x : Space n, autoBallMeanLaplacian (fun y : Space n => autoGreenTest (2*n) omega r eta ‖y‖) x)=0 := by
  have h := auto_ballMean_test_ibp hn omega hr heta (f := fun _ : Space n => (1 : ℝ))
    (fun _ _ => contDiffAt_const)
  simpa only [autoBallMeanLaplacian,fderiv_fun_const,fderiv_zero,Pi.zero_apply,ContinuousLinearMap.zero_apply,Finset.sum_const_zero,mul_zero,one_mul,integral_zero] using h.symm

theorem auto_ballMean_test_ibp_sub_constant {n : ℕ} (hn : 0 < n) (omega : ℝ)
    {r eta : ℝ} (hr : 0 < r) (heta : 0 < eta)
    {f : Space n → ℝ} (hf : ∀ x∈closedBall 0 r, ContDiffAt ℝ 2 f x) :
    (∫ x : Space n, autoGreenTest (2*n) omega r eta ‖x‖*autoBallMeanLaplacian f x)=
      ∫ x : Space n, (f x-f 0)*autoBallMeanLaplacian
        (fun y : Space n => autoGreenTest (2*n) omega r eta ‖y‖) x := by
  have hcf : ContinuousOn f (closedBall 0 r) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hF := auto_ballMean_test_laplacian_source_integrable hn omega hr heta hcf
  have hOne := auto_ballMean_test_laplacian_source_integrable hn omega hr heta
    (v := fun _ : Space n => (1 : ℝ)) continuousOn_const
  simp only [one_mul] at hOne
  rw [auto_ballMean_test_ibp hn omega hr heta hf]
  simp_rw [sub_mul]
  rw [integral_sub hF (hOne.const_mul (f 0)),integral_const_mul,
    auto_ballMean_test_laplacian_integral_zero hn omega hr heta,mul_zero,sub_zero]

end Yau.LeafProofs.L05AutonomousAux
