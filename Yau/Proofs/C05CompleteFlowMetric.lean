import Yau.Proofs.C05CompleteFieldMetric
import Yau.Proofs.C04RescaledTubeScaling

/-! The complete smooth metrics used below are the actual flow slices and their
positive constant rescalings. Their closed distance balls are compact. -/

noncomputable section

namespace Yau.Proofs.C05Aux

open Yau Blueprint Set
open C04Aux C04RescaledTubeAux

variable {n : ℕ}

def completeFlowMetric (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : FlowStage X o h U P ρ) (hH : HarnackCompleteness X o h)
    (t : ℝ) (ht : 0 < t) : SmoothMetric X.manifold :=
  smoothMetricOfCompleteField (h t) (localizedFlow_metricSmooth X o h U P ρ hf.1 ht.le)
    (hH.2.1 t ht) (hf.1.1.2.2.1 t ht.le)

theorem completeFlowMetric_form (X : KahlerManifold n) (o : Pt X) (h : Flow X)
    (U P ρ : STF X) (hf : FlowStage X o h U P ρ) (hH : HarnackCompleteness X o h)
    (t : ℝ) (ht : 0 < t) : (completeFlowMetric X o h U P ρ hf hH t ht).form = h t := rfl

def completeRescaledFlowMetric (X : KahlerManifold n) (o : Pt X) (h : Flow X)
    (U P ρ : STF X) (hf : FlowStage X o h U P ρ) (hH : HarnackCompleteness X o h)
    (R : ℝ) (hR : 0 < R) (t : ℝ) (ht : 0 < t) : SmoothMetric X.manifold :=
  smoothMetricOfCompleteField (scaleField R hR (h t))
    (metricSmooth_scale R hR (h t) (localizedFlow_metricSmooth X o h U P ρ hf.1 ht.le))
    (complete_scale R hR (h t) (localizedFlow_metricSmooth X o h U P ρ hf.1 ht.le)
      (hH.2.1 t ht))
    (kahlerClosed_scale R hR (h t) (localizedFlow_metricSmooth X o h U P ρ hf.1 ht.le)
      (hf.1.1.2.2.1 t ht.le))

theorem completeRescaledFlowMetric_form (X : KahlerManifold n) (o : Pt X) (h : Flow X)
    (U P ρ : STF X) (hf : FlowStage X o h U P ρ) (hH : HarnackCompleteness X o h)
    (R : ℝ) (hR : 0 < R) (t : ℝ) (ht : 0 < t) :
    (completeRescaledFlowMetric X o h U P ρ hf hH R hR t ht).form =
      scaleField R hR (h t) := rfl

theorem isCompact_rescaled_flow_sublevel (X : KahlerManifold n) (o : Pt X) (h : Flow X)
    (U P ρ : STF X) (hf : FlowStage X o h U P ρ) (hH : HarnackCompleteness X o h)
    (R : ℝ) (hR : 0 < R) (t : ℝ) (ht : 0 < t) (x : Pt X) (a : ℝ) :
    IsCompact {y | inducedDistance (scaleField R hR (h t)) x y ≤ a} :=
  Yau.LeafProofs.L12Aux.isCompact_inducedDistance_sublevel
    (completeRescaledFlowMetric X o h U P ρ hf hH R hR t ht) x a

end Yau.Proofs.C05Aux
