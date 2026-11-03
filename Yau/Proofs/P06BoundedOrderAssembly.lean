import Yau.Proofs.P06BoundedOrderAssemblyCutoffs

/-! The original type/order and existence/uniqueness assertions from the
internal cutoff construction, which the parent proof supplies. -/
noncomputable section
open MeasureTheory

namespace Yau.NodeProofs.P06Aux.BoundedOrder
open Yau Yau.Blueprint
variable {n : ℕ}

theorem hodgeTypeAndOrder_of_cutoffConstruction
    (X : KahlerManifold n) (μ : Measure X.manifold.Carrier)
    (hμ : IsRiemannianVolume X.metric.form μ)
    (hc : HodgeCutoffConstruction X.metric.form μ) : HodgeTypeAndOrder X.metric.form := by
  refine ⟨PDETypeTrace.boundedFormHeat_oneOne X, ?_, ?_⟩
  · intro A B U V hA hB hU hV hAB
    exact boundedFormHeat_comparison_of_cutoffConstruction X μ hμ hc A B U V hA hB hU hV hAB
  · intro A U C hA hU hC hbound
    exact boundedFormHeat_orderBound_of_cutoffConstruction X μ hμ hc A U hA hU hC hbound

theorem hodgeHeatExistenceUniqueness_of_cutoffConstruction
    (X : KahlerManifold n) (μ : Measure X.manifold.Carrier)
    (hμ : IsRiemannianVolume X.metric.form μ)
    (hc : HodgeCutoffConstruction X.metric.form μ) : HodgeHeatExistenceUniqueness X.metric.form := by
  intro A hA
  obtain ⟨U, hU, _⟩ := hc.2 A hA
  exact ⟨⟨U, hU⟩, fun U V hU hV => boundedFormHeat_unique X A U V hU hV⟩

end Yau.NodeProofs.P06Aux.BoundedOrder
