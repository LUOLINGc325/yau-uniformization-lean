import Yau.Proofs.P03LeviChartTransport
import Yau.LeafProofs.L22LeviTransport
import Yau.LeafProofs.L22Locality

open scoped Manifold Topology ContDiff ComplexOrder Matrix
open Yau.LeafProofs

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The original centred strict-psh predicate gives positive Levi matrices
at every point of every fixed holomorphic chart. -/
theorem strictPsh_chart_posDef {ψ : M.Carrier → ℝ} (hψ : IsSmoothStrictPsh ψ)
    (a : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a) :
    (leviC (inChart a ψ) z).PosDef := by
  let x := chartInv a z
  have hx : chartInv a z ∈ (extChartAt (ComplexModel n) x).source := mem_extChartAt_source x
  have hf : ContDiffAt ℝ 2 (inChart x ψ) (chartPt x x) :=
    ((hψ.1 x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))).of_le
      (by simp)
  have hpos : (leviC (inChart x ψ) (chartPt x x)).PosDef := hψ.2 x
  have he := inChart_transition_germ_of_source ψ a x hz hx
  rw [L22Aux.leviC_congr_of_eventuallyEq he]
  exact L22Aux.leviC_posDef_chart_comp a x hz hx hf hpos

end Yau.NodeProofs.P03Aux
