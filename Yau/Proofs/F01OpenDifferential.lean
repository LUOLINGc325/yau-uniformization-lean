import Yau.Proofs.F01OpenCharts

/-! Native differentiation of the inclusion composed with an inverse chart.
Only actual target points are used, so inverse charts are compared on an open
neighborhood before taking their manifold derivatives. -/
open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

theorem openInclusion_comp_chartInv_eventuallyEq
    (a : (openConnectedManifold M S hS).Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) :
    (fun w => openInclusion M S hS (chartInv a w)) =ᶠ[𝓝 z] chartInv a.val := by
  have hopen : IsOpen (chartTarget a) := isOpen_extChartAt_target (I := ComplexModel n) a
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact openInclusion_chartInv M S hS a hw

theorem openInclusion_comp_chartInv_mfderiv
    (a : (openConnectedManifold M S hS).Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) :
    (mfderiv (ComplexModel n) (ComplexModel n) (openInclusion M S hS) (chartInv a z)).comp
      (mfderiv (ComplexModel n) (ComplexModel n) (chartInv a) z) =
      mfderiv (ComplexModel n) (ComplexModel n) (chartInv a.val) z := by
  have hd : MDifferentiableAt (ComplexModel n) (ComplexModel n) (chartInv a) z := by
    exact (mdifferentiableWithinAt_extChartAt_symm hz).mdifferentiableAt
      (by simp [ComplexModel])
  rw [← mfderiv_comp z (openInclusion_mdifferentiable M S hS _) hd]
  exact (openInclusion_comp_chartInv_eventuallyEq M S hS a hz).mfderiv_eq

end Yau.NodeProofs.F01Aux
