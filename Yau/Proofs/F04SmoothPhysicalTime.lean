import Yau.Proofs.F04ChartContinuity
import Yau.Proofs.F05SmoothTimeJets

open Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof

/-- The ACTUAL one-sided physical time derivative of a genuinely smooth
 closed-slab scalar profile is smooth on that SAME closed slab. -/
theorem smoothSpaceTime_timeDerivative_smooth
    {n : ℕ} {M : ComplexManifold n} {S : ℝ} (hS : 0 < S)
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v (Icc 0 S)) :
    SmoothSpaceTime (fun x t => derivWithin (v x) (Icc 0 S) t) (Icc 0 S) := by
  intro c
  exact Yau.Proofs.F05Aux.F05_joint_time_derivative_smooth (uniqueDiffOn_Icc hS) (hv c)

/-- The physical closed-time scalar derivative exists as an ACTUAL
 HasDerivWithinAt, obtained from the genuine joint chart profile. -/
theorem smoothSpaceTime_hasDerivWithinAt
    {n : ℕ} {M : ComplexManifold n} {S : ℝ}
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v (Icc 0 S))
    (x : M.Carrier) (t : ℝ) (ht : t ∈ Icc 0 S) :
    HasDerivWithinAt (v x) (derivWithin (v x) (Icc 0 S) t) (Icc 0 S) t := by
  have hc : ContDiffOn ℝ ∞ (fun s => v (chartInv x (chartPt x x)) s) (Icc 0 S) :=
    (hv x).comp (contDiffOn_const.prodMk contDiffOn_id) (fun s hs => ⟨mem_extChartAt_target x,hs⟩)
  rw [Yau.LeafProofs.chartInv_chartPt_of_mem x x (mem_chart_source _ _)] at hc
  exact (hc.differentiableOn (by simp) t ht).hasDerivWithinAt

end Yau.F04Proof
