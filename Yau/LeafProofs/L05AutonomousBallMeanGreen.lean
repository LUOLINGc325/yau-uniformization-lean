import Yau.LeafProofs.L05AutonomousBallMeanBulk
import Yau.LeafProofs.L05AutonomousBallMeanLaplacian

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_ballMean_green_identity {n : ℕ} (hn : 0 < n) {omega r : ℝ}
    (hOmega : 0 < omega) (hr : 0 < r)
    {f : Space n → ℝ} (hf : ∀ x∈closedBall 0 r, ContDiffAt ℝ 2 f x) :
    (∫ x in ball (0 : Space n) r, f x-f 0)/(omega*r^(2*n))=
      ∫ x : Space n, autoRadialGreen (2*n) omega r ‖x‖*autoBallMeanLaplacian f x := by
  let v : Space n → ℝ := fun x => f x-f 0
  have hv : ContinuousOn v (closedBall 0 r) :=
    (show ContinuousOn f (closedBall 0 r) from fun x hx => (hf x hx).continuousAt.continuousWithinAt).sub continuousOn_const
  have hv0 : v 0=0 := sub_self _
  obtain ⟨B,hB,hBD⟩ := auto_green_cutoff_deriv_bounds
  let I : ℝ → ℝ := fun eta => ∫ x : Space n, autoBallMeanInnerError omega r eta v
    (deriv (autoGreenInner eta)) (deriv (deriv (autoGreenInner eta))) x
  let O : ℝ → ℝ := fun eta => ∫ x : Space n, autoBallMeanOuterError omega r eta v
    (deriv (autoGreenOuter r eta)) (deriv (deriv (autoGreenOuter r eta))) x
  have hI : Tendsto I (𝓝[>] 0) (𝓝 0) := auto_ballMean_inner_error_tendsto hn omega hr hB.le hB.le hf
    (fun eta => deriv (autoGreenInner eta)) (fun eta => deriv (deriv (autoGreenInner eta)))
    (fun eta heta s _ => (hBD eta heta r s).1) (fun eta heta s _ => (hBD eta heta r s).2.1)
  have hO : Tendsto O (𝓝[>] 0) (𝓝 0) := auto_ballMean_outer_error_tendsto hn omega hr hB.le hB.le hf
    (fun eta => deriv (autoGreenOuter r eta)) (fun eta => deriv (deriv (autoGreenOuter r eta)))
    (fun eta heta s _ => (hBD eta heta r s).2.2.1) (fun eta heta s _ => (hBD eta heta r s).2.2.2)
  have hBulk := (auto_ballMean_bulk_tendsto hv hv0).div_const (omega*r^(2*n))
  have hR : Tendsto (fun eta : ℝ =>
      (∫ x : Space n, v x*autoGreenCutoffProduct r eta ‖x‖)/(omega*r^(2*n))+I eta+O eta)
      (𝓝[>] 0) (𝓝 ((∫ x in ball (0 : Space n) r, v x)/(omega*r^(2*n)))) := by
    simpa only [add_zero] using (hBulk.add hI).add hO
  have hEvent : Ioo (0 : ℝ) (r/8)∈𝓝[>] 0 :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨r/8,(show 0 < r/8 by positivity),subset_rfl⟩
  have hEq : (fun eta : ℝ => ∫ x : Space n,
        autoGreenTest (2*n) omega r eta ‖x‖*autoBallMeanLaplacian f x)=ᶠ[𝓝[>] 0]
      (fun eta : ℝ => (∫ x : Space n, v x*autoGreenCutoffProduct r eta ‖x‖)/(omega*r^(2*n))+I eta+O eta) := by
    filter_upwards [hEvent] with eta heta
    have hBI := (auto_ballMean_cutoff_product_integrable heta.1 hv).div_const (omega*r^(2*n))
    have hII := auto_ballMean_inner_error_integrable hn omega hr heta.1 heta.2 hv
    have hOI := auto_ballMean_outer_error_integrable hn omega hr heta.1 heta.2 hv
    rw [auto_ballMean_test_ibp_sub_constant hn omega hr heta.1 hf]
    change (∫ x : Space n, v x*autoBallMeanLaplacian (fun y : Space n => autoGreenTest (2*n) omega r eta ‖y‖) x)=_
    calc
      _ = ∫ x : Space n, v x*autoGreenCutoffProduct r eta ‖x‖/(omega*r^(2*n))+
          autoBallMeanInnerError omega r eta v (deriv (autoGreenInner eta)) (deriv (deriv (autoGreenInner eta))) x+
          autoBallMeanOuterError omega r eta v (deriv (autoGreenOuter r eta)) (deriv (deriv (autoGreenOuter r eta))) x :=
        integral_congr_ae (ae_of_all volume fun x => auto_ballMean_test_laplacian_decomposition hn hOmega hr heta.1 heta.2 v x)
      _ = _ := by
        have hAdd := integral_add (hBI.add hII) hOI
        simp only [Pi.add_apply] at hAdd
        rw [integral_add hBI hII,integral_div] at hAdd
        convert! hAdd using 1
  have hL := auto_ballMean_test_source_tendsto hn hOmega hr hf
  exact (tendsto_nhds_unique hL (hR.congr' hEq.symm)).symm

end Yau.LeafProofs.L05AutonomousAux
