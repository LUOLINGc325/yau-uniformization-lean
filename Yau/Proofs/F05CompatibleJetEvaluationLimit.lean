import Yau.Proofs.F05JetAmbient
import Yau.Proofs.F05JetCompatibility

/-! Convergence in the actual compatible jet norm gives pointwise
convergence of all four original jet evaluations. -/

open Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_compatible_jet_evaluation_tendsto (A : AtlasData M) {α T : ℝ}
    (hT : 0 ≤ T) (u : ℕ → F05CompatibleJetGraph A α hT)
    (uLim : F05CompatibleJetGraph A α hT) (hu : Tendsto u atTop (𝓝 uLim))
    (i : Fin A.count) (p : F05Q A i T) :
    Tendsto (fun k => ((u k).val i).val.1 p) atTop (𝓝 ((uLim.val i).val.1 p)) ∧
    Tendsto (fun k => ((u k).val i).val.2.1 p) atTop (𝓝 ((uLim.val i).val.2.1 p)) ∧
    Tendsto (fun k => ((u k).val i).val.2.2.1.val.1 p) atTop (𝓝 ((uLim.val i).val.2.2.1.val.1 p)) ∧
    Tendsto (fun k => ((u k).val i).val.2.2.2.val.1 p) atTop (𝓝 ((uLim.val i).val.2.2.2.val.1 p)) := by
  have hAmbient : Tendsto (fun k => (u k).val) atTop (𝓝 uLim.val) :=
    (continuous_subtype_val.tendsto uLim).comp hu
  refine ⟨?_,?_,?_,?_⟩
  · exact ((F05GlobalValueEval A α hT i p).continuous.tendsto uLim.val).comp hAmbient
  · exact ((F05GlobalGradientEval A α hT i p).continuous.tendsto uLim.val).comp hAmbient
  · exact ((F05GlobalHessianEval A α hT i p).continuous.tendsto uLim.val).comp hAmbient
  · exact ((F05GlobalTimeEval A α hT i p).continuous.tendsto uLim.val).comp hAmbient

end Yau.Proofs.F05Aux
