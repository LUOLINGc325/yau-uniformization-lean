import Yau.Proofs.P08CanonicalAverage
import Yau.Proofs.P08ScalarAverage
import Yau.Blueprint.Nodes

/-! Assembly of both canonical-average clauses. Its only predecessor
premises are exactly the original P04 and P07 node contracts. -/
noncomputable section
namespace Yau.NodeProofs.P08Aux
open Yau Yau.Blueprint
variable {n : ℕ}

/-- The original initial section data and controlled exhaustion imply both
frozen average conclusions. Every analytic estimate is internally proved. -/
theorem canonicalAverages_of_initial_exhaustion (X : KahlerManifold n) (o : Pt X)
    (h4 : CanonicalInitialData X o) {u : Pt X → ℝ} (hu : ControlledExhaustion X o u) :
    CanonicalAverages X o := by
  constructor
  · intro S hS ho hgrowth
    exact canonical_log_average X o S hS ho hgrowth
  · obtain ⟨S, hS, ho, hgrowth⟩ := h4.1 o
    obtain ⟨B, hB, hbound⟩ := canonical_regularized_averages X o S hS ho hgrowth
    exact ScalarAverage.scalar_average_of_regularized_bounds X o hu S hS B hB.le hbound

/-- This preserves every dimension and every original quantifier. The
registered original node is closed only after its original predecessors. -/
theorem P08_of_P04_P07 (h4 : Blueprint.P04) (h7 : Blueprint.P07) : Blueprint.P08 := by
  intro n X o
  obtain ⟨u, hu⟩ := h7 n X o
  exact canonicalAverages_of_initial_exhaustion X o (h4 n X o) hu

end Yau.NodeProofs.P08Aux
