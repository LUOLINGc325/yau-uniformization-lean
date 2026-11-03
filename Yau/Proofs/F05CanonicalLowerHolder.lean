import Yau.Proofs.F05ReconstructionBudget

/-! The full closed radius-two chart jets have a true lower Holder bound,
derived from actual finite reconstruction and FTC uniqueness at the rim. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_canonical_lower_holder {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (hT : 0 < T), T ≤ 1 →
      ∀ u : F05CompatibleJetGraph A α hT.le, ∀ i : Fin A.count,
        HolderBound α (F05Q A i T)
          (fun p => (F05CanonicalPull A χ α hT.le u i p,
            spatialD (F05CanonicalPull A χ α hT.le u i) p)) (C*‖u‖) := by
  classical
  choose β hβ hRange hSupport hOne using (fun j : Fin A.count => F05_outer_manifold_cutoff hA j)
  obtain ⟨C,hC,hBudget⟩ := F05_reconstruction_lower_budget hA hχ β hβ hSupport hα hα1
  refine ⟨C,hC,?_⟩
  intro T hT hT1 u i
  let v : Point n → ℝ := pull A i (F05CutoffReconstruction A χ β α hT.le u)
  have hBounds := hBudget T hT hT1 u i
  let ui : F05LocalFTCGraph A i α hT.le := ⟨(u.val i).val,(u.val i).property.1.1.1⟩
  have hValue : EqOn v (F05BCFFun (u.val i).val.1) (F05Q A i T) := by
    intro p hp
    exact (F05CutoffReconstruction_eq hA hχ β hSupport hOne α hT.le u
      (F05D_lift_mem_closure hA hp.1) p.2).trans
        (F05CanonicalJetFunction_value hA hχ α hT.le u i hp.1 hp.2)
  have hReal := F05LocalFTCGraph_realization A i α hT ui v hValue
    (fun p hp => hBounds.1.2.2.2.2.1 p hp)
  have hCanonical := F05CanonicalJetFunction_realizes hA hχ α hT u i
  apply holderBound_congr_on hBounds.2
  intro p hp
  apply Prod.ext
  · exact F05CutoffReconstruction_eq hA hχ β hSupport hOne α hT.le u
      (F05D_lift_mem_closure hA hp.1) p.2
  · exact (hReal.2.1 hp).trans (hCanonical.2.1 hp).symm

end Yau.Proofs.F05Aux
