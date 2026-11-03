import Yau.LeafProofs.L12Complete

noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual original Bishop--Gromov leaf gives the polynomial lower
unit-ball volume bound needed to turn a weighted norm into growth. -/
theorem origin_unitBall_volume_le (g : SmoothMetric M)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (o x : M.Carrier) :
    μ (distBall g.form o 1) ≤ ENNReal.ofReal ((distFrom g.form o x+2)^(2*n))*μ (distBall g.form x 1) := by
  letI := L12Aux.inducedMetricSpace g
  have hr : 0 ≤ distFrom g.form o x := by change 0 ≤ dist o x; exact dist_nonneg
  have hR : 0 < distFrom g.form o x+2 := by linarith
  have hsub : distBall g.form o 1 ⊆ distBall g.form x (distFrom g.form o x+2) := by
    intro y hy
    have hy' := (L12Aux.mem_distBall_iff g o y (by norm_num : (0 : ℝ) < 1)).mp hy
    apply (L12Aux.mem_distBall_iff g x y hR).mpr
    have htri := dist_triangle x o y
    change dist o y < 1 at hy'
    change dist x y < dist o x+2
    rw [dist_comm x o] at htri
    linarith
  have hcomp := Yau.LeafProofs.L12 n M g g.complete_distance g.kahler_equations hRic μ hμ
    x 1 (distFrom g.form o x+2) (by norm_num) (by linarith)
  simpa only [div_one] using (measure_mono hsub).trans hcomp

end Yau.Proofs.P04Aux
