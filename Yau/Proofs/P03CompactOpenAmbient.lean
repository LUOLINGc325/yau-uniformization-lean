import Yau.Geometry.Basic
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Metrizable.CompletelyMetrizable

open scoped Topology Uniformity
open TopologicalSpace

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

theorem manifold_locallyCompact (M : ComplexManifold n) : LocallyCompactSpace M.Carrier :=
  ChartedSpace.locallyCompactSpace (ComplexVector n) M.Carrier

theorem continuousFunctions_complete (M : ComplexManifold n) : CompleteSpace C(M.Carrier, ℂ) := by
  letI := manifold_locallyCompact M
  infer_instance

theorem continuousFunctions_countablyGenerated (M : ComplexManifold n) :
    Filter.IsCountablyGenerated (𝓤 C(M.Carrier, ℂ)) := by
  letI := manifold_locallyCompact M
  infer_instance

theorem continuousFunctions_completelyMetrizable (M : ComplexManifold n) :
    IsCompletelyMetrizableSpace C(M.Carrier, ℂ) := by
  letI := continuousFunctions_complete M
  letI := continuousFunctions_countablyGenerated M
  infer_instance

end Yau.NodeProofs.P03Aux
