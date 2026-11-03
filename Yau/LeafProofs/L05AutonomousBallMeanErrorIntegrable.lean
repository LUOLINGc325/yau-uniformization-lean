import Yau.LeafProofs.L05AutonomousBallMeanPointwise

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_green_cutoff_error_continuousOn {d : ℕ} (hd : 2 ≤ d) (omega : ℝ)
    {r : ℝ} (hr : 0 < r) {q1 q2 : ℝ → ℝ} (hq1 : Continuous q1) (hq2 : Continuous q2) :
    ContinuousOn (fun s : ℝ => autoGreenCutoffError d omega r s (q1 s) (q2 s)) (Ioi 0) := by
  intro s hs
  have hK := (auto_green_primitive_contDiffAt hd omega hr hs).continuousAt
  have hG := ((auto_greenIntegrand_continuousOn d r).continuousAt (isOpen_Ioi.mem_nhds hs)).neg.div_const ((d : ℝ)*omega)
  have hCoeff : ContinuousAt (fun t : ℝ => ((d : ℝ)-1)/t) s :=
    continuousAt_const.div continuousAt_id hs.ne'
  exact (((hK.mul hq2.continuousAt).add ((hG.const_mul 2).mul hq1.continuousAt)).add
    ((hCoeff.mul hK).mul hq1.continuousAt)).continuousWithinAt

theorem auto_ballMean_annulus_source_integrable {n : ℕ} {a b r : ℝ}
    (ha : 0 < a) (hbr : b ≤ r) {v : Space n → ℝ} (hv : ContinuousOn v (closedBall 0 r))
    {E : ℝ → ℝ} (hE : ContinuousOn E (Ioi 0)) :
    Integrable (fun x : Space n => if ‖x‖∈Icc a b then v x*E ‖x‖ else 0) := by
  let S : Set (Space n) := {x | ‖x‖∈Icc a b}
  have hSC : IsClosed S := isClosed_Icc.preimage continuous_norm
  have hSub : S ⊆ closedBall 0 b := fun x hx => by
    simpa only [mem_closedBall,dist_zero_right] using hx.2
  have hCompact : IsCompact S := (isCompact_closedBall (0 : Space n) b).of_isClosed_subset hSC hSub
  have hV : ContinuousOn v S := hv.mono (hSub.trans (closedBall_subset_closedBall hbr))
  have hEC : ContinuousOn (fun x : Space n => E ‖x‖) S :=
    hE.comp continuous_norm.continuousOn (fun x hx => ha.trans_le hx.1)
  have hInt : IntegrableOn (fun x : Space n => v x*E ‖x‖) S volume :=
    (hV.mul hEC).integrableOn_compact hCompact
  have hFn : S.indicator (fun x : Space n => v x*E ‖x‖)=
      (fun x : Space n => if ‖x‖∈Icc a b then v x*E ‖x‖ else 0) := by
    funext x
    by_cases hx : ‖x‖∈Icc a b
    · rw [indicator_of_mem (show x∈S from hx),ite_eq_left hx]
    · rw [indicator_of_notMem (show x∉S from hx),ite_eq_right hx]
  rw [← hFn]
  exact (integrable_indicator_iff hSC.measurableSet).mpr hInt

theorem auto_ballMean_inner_error_integrable {n : ℕ} (hn : 0 < n) (omega : ℝ)
    {r eta : ℝ} (hr : 0 < r) (heta : 0 < eta) (hetar : eta < r/8)
    {v : Space n → ℝ} (hv : ContinuousOn v (closedBall 0 r)) :
    Integrable (autoBallMeanInnerError omega r eta v
      (deriv (autoGreenInner eta)) (deriv (deriv (autoGreenInner eta)))) := by
  unfold autoBallMeanInnerError
  have hE := auto_green_cutoff_error_continuousOn (by omega : 2 ≤ 2*n) omega hr
    (contDiff_infty_iff_deriv.mp (auto_green_inner_contDiff eta)).2.continuous
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp (auto_green_inner_contDiff eta)).2).2.continuous
  exact auto_ballMean_annulus_source_integrable heta (by linarith : 2*eta ≤ r) hv hE

theorem auto_ballMean_outer_error_integrable {n : ℕ} (hn : 0 < n) (omega : ℝ)
    {r eta : ℝ} (hr : 0 < r) (heta : 0 < eta) (hetar : eta < r/8)
    {v : Space n → ℝ} (hv : ContinuousOn v (closedBall 0 r)) :
    Integrable (autoBallMeanOuterError omega r eta v
      (deriv (autoGreenOuter r eta)) (deriv (deriv (autoGreenOuter r eta)))) := by
  unfold autoBallMeanOuterError
  have hE := auto_green_cutoff_error_continuousOn (by omega : 2 ≤ 2*n) omega hr
    (contDiff_infty_iff_deriv.mp (auto_green_outer_contDiff heta r)).2.continuous
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp (auto_green_outer_contDiff heta r)).2).2.continuous
  exact auto_ballMean_annulus_source_integrable
    (by linarith : 0 < r-2*eta) (by linarith : r-eta ≤ r) hv hE

end Yau.LeafProofs.L05AutonomousAux
