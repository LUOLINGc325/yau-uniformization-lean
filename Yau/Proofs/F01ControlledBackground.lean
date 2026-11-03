import Yau.Proofs.F01BackgroundGeometry

/-! Consumer of the ORIGINAL controlled-exhaustion fields. Every level
above u(o) gives the actual complete bounded-geometry Hermitian background
needed by the original short-time theorem, without another geometric inlet. -/
open Set
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint Yau.LeafProofs
variable {n : ℕ}

theorem controlled_background_geometry (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) {L : ℝ} (ho : u o < L) :
    let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
    MetricSmooth α ∧ LeafCandidates.HermitianBoundedGeometry α ∧
      IsCompleteDistance (inducedDistance α) := by
  have hL : 0 < L := (lt_of_lt_of_le zero_lt_one (hu.2.2.1 o)).trans ho
  exact approximatingMetric_actual_geometry X.manifold
    (L12Aux.metricSmooth_of_smoothMetric X.metric) hu.1
    (fun x => zero_le_one.trans (hu.2.2.1 x)) o hL ho (hu.2.1 L)

end Yau.NodeProofs.F01Aux
