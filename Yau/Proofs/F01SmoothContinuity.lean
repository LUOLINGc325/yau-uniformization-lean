import spec.CHAIN.CONTRACTS

/-! Global continuity follows from the original fixed-chart smoothness. -/
open Set Filter
open scoped Manifold Topology ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem continuous_of_smoothFn {f : M.Carrier → ℝ} (hf : SmoothFn f) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hchart : ContinuousAt (inChart x f) (chartPt x x) :=
    (hf x).continuousOn.continuousAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds (mem_extChartAt_target x))
  have hcomp : ContinuousAt (fun y => f (chartInv x (chartPt x y))) x :=
    hchart.comp (continuousAt_extChartAt (I := ComplexModel n) x)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds
    (mem_extChartAt_source x)] with y hy
  exact (congrArg f ((extChartAt (ComplexModel n) x).left_inv hy)).symm

end Yau.NodeProofs.F01Aux
