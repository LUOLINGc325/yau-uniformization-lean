import Yau.Proofs.F03CompactHeatChartPowers
import Yau.LeafProofs.L09

/-! Smooth chart powers have actual finite jet integrals on every compactly contained ball. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem smooth_chart_jet_square_integrable_ball {n : ℕ}
    (D : Set (ComplexVector n)) (hD : IsOpen D) (f : ComplexVector n → ℂ)
    (hf : ContDiffOn ℝ ∞ f D) (R : ℝ) (hBall : Metric.closedBall 0 R ⊆ D) (j : ℕ) :
    IntegrableOn (fun z => ‖iteratedFDeriv ℝ j f z‖^2) (Metric.ball 0 R) (lebesgueC n) := by
  rw [LeafProofs.lebesgueC_eq_volume]
  have hCont : ContinuousOn (fun z => ‖iteratedFDeriv ℝ j f z‖^2) (Metric.closedBall 0 R) := by
    intro z hz
    exact (((hf.contDiffAt (hD.mem_nhds (hBall hz))).differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j)).continuousAt.norm.pow 2).continuousWithinAt
  exact (hCont.integrableOn_compact (isCompact_closedBall 0 R)).mono_set Metric.ball_subset_closedBall

end Yau.Proofs.F03Aux
