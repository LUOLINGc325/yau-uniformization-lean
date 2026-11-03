import Yau.Proofs.P02
import Yau.Proofs.G02GluedVolume

open scoped Manifold Topology ContDiff
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

/-- The geometric volume and a smooth strictly plurisubharmonic background
are chosen once, before any finite pole regularization parameter is introduced. -/
theorem exists_interpolation_background (X : KahlerManifold n) :
    ∃ (μ : Measure X.manifold.Carrier) (ψ : X.manifold.Carrier → ℝ),
      IsRiemannianVolume X.metric.form μ ∧ IsSmoothStrictPsh ψ := by
  obtain ⟨μ, hμ⟩ := Yau.Proofs.G02Aux.exists_riemannianVolume X.metric.form (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric)
  let o : X.manifold.Carrier := Classical.arbitrary _
  obtain ⟨ψ, hψ, _⟩ := Yau.NodeProofs.P02_proved n X o
  exact ⟨μ, ψ, hμ, hψ⟩

end Yau.NodeProofs.P03Aux
