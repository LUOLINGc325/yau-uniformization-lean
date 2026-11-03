import Yau.Proofs.P03Measure

open scoped Topology ContDiff
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

theorem affineLine_mem_outer_ball {a x y : ComplexVector n} {r : ℝ}
    (hx : x ∈ Metric.ball a (2 * r)) (hy : ‖y‖ ≤ r) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    x - z • y ∈ Metric.ball a (3 * r) := by
  have hx' := Metric.mem_ball.mp hx
  apply Metric.mem_ball.mpr
  calc
    dist (x - z • y) a = ‖(x - a) - z • y‖ := by
      rw [dist_eq_norm]
      congr 1
      abel
    _ ≤ ‖x - a‖ + ‖z • y‖ := norm_sub_le _ _
    _ = dist x a + ‖z‖ * ‖y‖ := by rw [dist_eq_norm, norm_smul]
    _ ≤ dist x a + ‖y‖ :=
      add_le_add le_rfl (mul_le_of_le_one_left (norm_nonneg y) hz)
    _ < 3 * r := by linarith

/-- Use native scalar Cauchy mean value only after restricting the actual
several-variable holomorphic function to a complex affine line. -/
theorem circleAverage_affineLine {h : ComplexVector n → ℂ} {a x y : ComplexVector n}
    {r : ℝ} (hc : Continuous h) (hh : DifferentiableOn ℂ h (Metric.ball a (3 * r)))
    (hx : x ∈ Metric.ball a (2 * r)) (hy : ‖y‖ ≤ r) :
    Real.circleAverage (fun z : ℂ => h (x - z • y)) 0 1 = h x := by
  have hline : DiffContOnCl ℂ (fun z : ℂ => h (x - z • y))
      (Metric.ball 0 |(1 : ℝ)|) := by
    constructor
    · intro z hz
      have hz' : ‖z‖ ≤ 1 := by
        have ht : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
        exact ht.le
      have hm := affineLine_mem_outer_ball hx hy hz'
      have hd := (hh _ hm).differentiableAt (Metric.isOpen_ball.mem_nhds hm)
      have hl : DifferentiableAt ℂ (fun w : ℂ => x - w • y) z := by
        have hconst : DifferentiableAt ℂ (fun _ : ℂ => x) z := differentiableAt_const x
        have hid : DifferentiableAt ℂ (fun w : ℂ => w) z := differentiableAt_id
        exact hconst.sub (hid.smul_const y)
      exact (hd.comp z hl).differentiableWithinAt
    · exact (hc.comp (continuous_const.sub (continuous_id.smul continuous_const))).continuousOn
  simpa only [zero_smul, sub_zero] using hline.circleAverage

end Yau.NodeProofs.P03Aux
