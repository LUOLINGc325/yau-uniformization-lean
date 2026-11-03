import Yau.Proofs.F01KahlerMixedExchange

/-! Locality of the actual nested complex derivatives on an open set. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Yau.NodeProofs.F01Aux
open Yau
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem mixed_wirtinger_eq_of_eqOn {f g : E → ℂ} {S : Set E}
    (hS : IsOpen S) (heq : EqOn f g S) {z : E} (hz : z ∈ S) (u v : E) :
    wirt (fun w => wirtBar f w u) z v = wirt (fun w => wirtBar g w u) z v := by
  apply wirt_eq_of_eventuallyEq
  filter_upwards [hS.mem_nhds hz] with w hw
  apply wirtBar_eq_of_eventuallyEq
  filter_upwards [hS.mem_nhds hw] with y hy
  exact heq hy

end Yau.NodeProofs.F01Aux
