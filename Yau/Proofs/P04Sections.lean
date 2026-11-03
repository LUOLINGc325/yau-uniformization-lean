import Yau.Proofs.P04Assembly
import Yau.Proofs.P04InitialRicci
import Yau.Proofs.P02
import Yau.Proofs.G02

noncomputable section
open MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ}

/-- Original P02 supplies the actual weight and original G02 the actual
volume. The entire section construction then has no added analytic premise. -/
theorem canonical_initial_data_from_ancestors (X : KahlerManifold n) (o : Yau.Blueprint.Pt X) :
    Yau.Blueprint.CanonicalInitialData X o := by
  obtain ⟨ψ,hψ,Cψ,hψupper⟩ := Yau.NodeProofs.P02_proved n X o
  obtain ⟨μ,hμ,_hunique⟩ := Yau.NodeProofs.G02_proved n X.manifold X.metric.form
    (Yau.LeafProofs.L18Aux.metricSmooth_of_smoothMetric X.metric)
  exact canonical_initial_data_of_actual_inputs X o ψ hψ Cψ hψupper μ hμ (initial_ricci_posSemidef X)

end Yau.Proofs.P04Aux
