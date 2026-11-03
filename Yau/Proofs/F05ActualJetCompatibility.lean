import Yau.Proofs.F05ActualOverlapJets
import Yau.Proofs.F05ActualJetAmbient

/-! The actual value, time, gradient and full Hessian identities put the
encoded derivatives in the original closed overlap graph. -/

open Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_jet_ambient_compatible_of_derivatives {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {α T : ℝ} (hT : 0 ≤ T) (u : F05JetAmbient A α hT)
    (w : M.Carrier → ℝ → ℝ) (hw : ∀ i : Fin A.count, C2 (F05Q A i T) (pull A i w))
    (hV : ∀ i (p : F05Q A i T), (u i).val.1 p = pull A i w p.val)
    (hG : ∀ i (p : F05Q A i T), (u i).val.2.1 p = spatialD (pull A i w) p.val)
    (hH : ∀ i (p : F05Q A i T), (u i).val.2.2.1.val.1 p = spatialDD (pull A i w) p.val)
    (hK : ∀ i (p : F05Q A i T), (u i).val.2.2.2.val.1 p = timeD (F05Q A i T) (pull A i w) p.val) :
    u ∈ F05CompatibleJetGraph A α hT := by
  change ((u ∈ F05ValueOverlapGraph A α hT ∧ u ∈ F05TimeOverlapGraph A α hT) ∧
    u ∈ F05GradientOverlapGraph A α hT) ∧ u ∈ F05HessianOverlapGraph A α hT
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · apply (Submodule.mem_iInf _).mpr
    intro p
    change (u p.left).val.1 p.leftPoint-(u p.right).val.1 p.rightPoint = 0
    rw [hV,hV]
    exact sub_eq_zero.mpr (F05_actual_overlap_jets hA w hw p).1
  · apply (Submodule.mem_iInf _).mpr
    intro p
    change (u p.left).val.2.2.2.val.1 p.leftPoint-(u p.right).val.2.2.2.val.1 p.rightPoint = 0
    rw [hK,hK]
    exact sub_eq_zero.mpr (F05_actual_overlap_jets hA w hw p).2.1
  · simp only [F05GradientOverlapGraph,Submodule.mem_iInf,LinearMap.mem_ker]
    intro p v
    change (u p.left).val.2.1 p.leftPoint v-
      (u p.right).val.2.1 p.rightPoint (fderiv ℝ (F05Transition A p.left p.right) p.leftCoord.val v) = 0
    rw [hG,hG,(F05_actual_overlap_jets hA w hw p).2.2.1]
    simp only [ContinuousLinearMap.comp_apply,sub_self]
  · simp only [F05HessianOverlapGraph,Submodule.mem_iInf,LinearMap.mem_ker]
    intro p v a
    change (u p.left).val.2.2.1.val.1 p.leftPoint v a-
      (u p.right).val.2.2.1.val.1 p.rightPoint
        (fderiv ℝ (F05Transition A p.left p.right) p.leftCoord.val v)
        (fderiv ℝ (F05Transition A p.left p.right) p.leftCoord.val a)-
      (u p.right).val.2.1 p.rightPoint
        (fderiv ℝ (fderiv ℝ (F05Transition A p.left p.right)) p.leftCoord.val v a) = 0
    rw [hH,hH,hG,(F05_actual_overlap_jets hA w hw p).2.2.2]
    rw [chartSecondJet_apply]
    ring

theorem F05ActualJetAmbient_compatible {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (w : M.Carrier → ℝ → ℝ)
    (hw : ∀ i : Fin A.count, SchauderBound α (F05Q A i T) (pull A i w) C)
    (h0 : ∀ x ∈ closure O, w x 0 = 0)
    (hTime0 : ∀ i : Fin A.count, ∀ z ∈ F05D A i, timeD (F05Q A i T) (pull A i w) (z,0) = 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t = 0) :
    F05ActualJetAmbient hA hα hT w hw h0 hTime0 hBoundary ∈ F05CompatibleJetGraph A α hT := by
  apply F05_jet_ambient_compatible_of_derivatives hA hT _ w (fun i => (hw i).1)
  · exact fun i p => (F05ActualJetAmbient_eval hA hα hT w hw h0 hTime0 hBoundary i p).1
  · exact fun i p => (F05ActualJetAmbient_eval hA hα hT w hw h0 hTime0 hBoundary i p).2.1
  · exact fun i p => (F05ActualJetAmbient_eval hA hα hT w hw h0 hTime0 hBoundary i p).2.2.1
  · exact fun i p => (F05ActualJetAmbient_eval hA hα hT w hw h0 hTime0 hBoundary i p).2.2.2

end Yau.Proofs.F05Aux
