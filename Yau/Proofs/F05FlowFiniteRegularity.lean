import Yau.Proofs.F05FlowSourceSolvers
import Yau.Proofs.F05FiniteManifoldPatch

/-! The actual native flow patches give genuine C2 regularity for their
literal manifold sum in every physical chart. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_flow_finite_patch_C2 {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ}
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    (β : Fin A.count → M.Carrier → ℝ) (hβ : ∀ j, SmoothFn (β j))
    (hSupport : ∀ j, tsupport (β j) ⊆ lift A j '' Metric.closedBall 0 (3/4))
    {α T ρ K E : ℝ} (hα : 0 < α) (hα1 : α < 1) (hT1 : T ≤ 1)
    (U H : Fin A.count → F05SourceZeroGraph A α T → Point n → ℝ)
    (hData : F05FlowSourcePatchData A χ h c α T ρ K E U H)
    (f : F05SourceZeroGraph A α T) (i : Fin A.count) :
    C2 (F05Q A i T) (pull A i (F05FiniteManifoldPatch A β (fun j => U j f))) := by
  have hEach (j : Fin A.count) :
      C2 (F05Q A i T) (pull A i (F05ManifoldPatch A j (β j) (U j f))) := by
    obtain ⟨B,hB,hBudget⟩ := F05_manifold_patch_budget hA j (hβ j) (hSupport j) hα hα1
    have hInfo := (hData j).2.2.2 f
    exact (hBudget T _ _ (U j f) hT1 hInfo.1 hInfo.2.1 i).1.1
  change C2 (F05Q A i T) (fun p => ∑ j,pull A i (F05ManifoldPatch A j (β j) (U j f)) p)
  exact c2_sum Finset.univ (fun j _ => hEach j)

end Yau.Proofs.F05Aux
