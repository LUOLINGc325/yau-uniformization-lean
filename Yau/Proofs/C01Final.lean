import Yau.Proofs.C01Completeness
import Yau.Proofs.C01CompactMetricDecay
import Yau.Proofs.C01IntegratedHarnack

/-! The original full nine-clause Harnack-completeness contract from its registered E03 parent, with all dimensions and the same localized flow. -/

noncomputable section
open scoped Topology Manifold ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.BlueprintContracts

theorem C01_of_E03 : E03_contract → C01_contract := by
  intro hE03 n X o h U P ρ hflow
  have hjoint : JointPositivity X h := hE03 n X o h U P ρ hflow
  exact ⟨localizedFlow_nonnegBisectional hflow hjoint,
    localizedFlow_complete_distance hflow hjoint,
    localizedFlow_ricci_posDef hflow hjoint,
    fun x _t ht => localizedFlow_matrix_harnack hflow hjoint x ht,
    fun x _t ht V => localizedFlow_scalar_harnack hflow hjoint x ht V,
    localizedFlow_metric_monotonicity hflow hjoint,
    localizedFlow_basepoint_scalar_bound hflow hjoint,
    localizedFlow_integrated_harnack hflow hjoint,
    localizedFlow_compact_metric_decay hflow hjoint⟩

end Yau.NodeProofs.C01Aux
