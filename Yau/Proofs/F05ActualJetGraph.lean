import Yau.Proofs.F05ActualJetCompatibility

/-! Actual homogeneous Schauder functions have their genuine element of the
complete compatible jet graph, retaining the original product norm bound. -/

open Set
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

def F05ActualJetGraph {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (w : M.Carrier → ℝ → ℝ)
    (hw : ∀ i : Fin A.count, SchauderBound α (F05Q A i T) (pull A i w) C)
    (h0 : ∀ x ∈ closure O, w x 0 = 0)
    (hTime0 : ∀ i : Fin A.count, ∀ z ∈ F05D A i, timeD (F05Q A i T) (pull A i w) (z,0) = 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t = 0) : F05CompatibleJetGraph A α hT :=
  ⟨F05ActualJetAmbient hA hα hT w hw h0 hTime0 hBoundary,
    F05ActualJetAmbient_compatible hA hα hT w hw h0 hTime0 hBoundary⟩

theorem F05ActualJetGraph_norm_le {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (w : M.Carrier → ℝ → ℝ)
    (hw : ∀ i : Fin A.count, SchauderBound α (F05Q A i T) (pull A i w) C)
    (h0 : ∀ x ∈ closure O, w x 0 = 0)
    (hTime0 : ∀ i : Fin A.count, ∀ z ∈ F05D A i, timeD (F05Q A i T) (pull A i w) (z,0) = 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t = 0) (hC : 0 ≤ C) :
    ‖F05ActualJetGraph hA hα hT w hw h0 hTime0 hBoundary‖ ≤ C :=
  F05ActualJetAmbient_norm_le hA hα hT w hw h0 hTime0 hBoundary hC

theorem F05ActualJetGraph_value {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (w : M.Carrier → ℝ → ℝ)
    (hw : ∀ i : Fin A.count, SchauderBound α (F05Q A i T) (pull A i w) C)
    (h0 : ∀ x ∈ closure O, w x 0 = 0)
    (hTime0 : ∀ i : Fin A.count, ∀ z ∈ F05D A i, timeD (F05Q A i T) (pull A i w) (z,0) = 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t = 0)
    (i : Fin A.count) (p : F05Q A i T) :
    ((F05ActualJetGraph hA hα hT w hw h0 hTime0 hBoundary).val i).val.1 p = pull A i w p.val := rfl

end Yau.Proofs.F05Aux
