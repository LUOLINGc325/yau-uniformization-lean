import Yau.LeafProofs.L05AutonomousBallMeanKernelFormula

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Interval
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux

/-- Both the logarithmic and negative-power formulas are genuinely smooth away from the origin. -/
theorem auto_green_primitive_contDiffAt {d : ℕ} (hd : 2 ≤ d) (omega : ℝ) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) : ContDiffAt ℝ ∞ (autoGreenPrimitive d omega r) s := by
  rcases eq_or_lt_of_le hd with h|h
  · subst d
    have hC : ContDiffAt ℝ ∞ (fun t : ℝ =>
        (Real.log (r/t)-(r^2-t^2)/(2*r^2))/(2*omega)) s := by fun_prop (disch := positivity)
    apply hC.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact auto_green_primitive_log omega hr ht
  · have hC : ContDiffAt ℝ ∞ (fun t : ℝ =>
        ((t^(2-(d : ℝ))-r^(2-(d : ℝ)))/((d : ℝ)-2)-(r^2-t^2)/(2*r^d))/((d : ℝ)*omega)) s := by
      fun_prop (disch := positivity)
    apply hC.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact auto_green_primitive_power h omega hr ht

end Yau.LeafProofs.L05AutonomousAux
