import Yau.Proofs.F05CutoffReconstruction
import Yau.Proofs.F05JetExtensionSchauder
import Yau.Proofs.F05JetExtensionBounds
import Yau.LeafProofs.L16FinitePhysicalParametrix

/-! Genuine finite reconstruction gives a full-chart lower Holder budget.
Every constant is fixed before the endpoint and the compatible jet. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_reconstruction_lower_budget {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (β : Fin A.count → M.Carrier → ℝ) (hβ : ∀ j, SmoothFn (β j))
    (hSupport : ∀ j, tsupport (β j) ⊆ lift A j '' Metric.closedBall 0 (3/4))
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (hT : 0 < T), T ≤ 1 →
      ∀ u : F05CompatibleJetGraph A α hT.le, ∀ i : Fin A.count,
        C2 (F05Q A i T) (pull A i (F05CutoffReconstruction A χ β α hT.le u)) ∧
        HolderBound α (F05Q A i T)
          (fun p => (pull A i (F05CutoffReconstruction A χ β α hT.le u) p,
            spatialD (pull A i (F05CutoffReconstruction A χ β α hT.le u)) p)) (C*‖u‖) := by
  classical
  choose H hH hHigh using (fun j : Fin A.count => F05_local_extension_schauder_budget A j
    (F05ModelPartition A χ j) (F05ModelPartition_contDiff hA hχ j)
    (F05ModelPartition_tsupport hA hχ j) α hα hα1)
  choose R hR hRaw using (fun j : Fin A.count => F05_local_extension_raw_low_budget A j
    (F05ModelPartition A χ j) (F05ModelPartition_contDiff hA hχ j)
    ((F05ModelPartition_tsupport hA hχ j).trans (Metric.closedBall_subset_closedBall (by norm_num : (1/4 : ℝ) ≤ 1))))
  choose B hB hPatch using (fun j : Fin A.count => F05_manifold_patch_budget hA j (hβ j) (hSupport j) hα hα1)
  let C := 1+∑ j,B j*R j
  have hSum : 0 ≤ ∑ j,B j*R j := Finset.sum_nonneg (fun j _ => mul_nonneg (hB j).le (hR j).le)
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro T hT hT1 u i
  let U (j : Fin A.count) : Point n → ℝ := F05LocalJetExtension A j (F05ModelPartition A χ j) (u.val j).val
  let V (j : Fin A.count) : Point n → ℝ := pull A i (F05ManifoldPatch A j (β j) (U j))
  have hEach (j : Fin A.count) :
      SchauderBound α (F05Q A i T) (V j) (B j*(H j*‖(u.val j).val‖+R j*‖(u.val j).val‖)) ∧
      HolderBound α (F05Q A i T) (fun p => (V j p,spatialD (V j) p)) (B j*(R j*‖(u.val j).val‖)) := by
    let uj : F05LocalFTCGraph A j α hT.le := ⟨(u.val j).val,(u.val j).property.1.1.1⟩
    exact hPatch j T _ _ (U j) hT1 (hHigh j T hT uj) (hRaw j α hα hα1 T hT uj).2.2 i
  have hC2 : C2 (F05Q A i T) (fun p => ∑ j,V j p) := c2_sum Finset.univ (fun j _ => (hEach j).1.1)
  have hLow := lowPair_holderBound_finset_sum Finset.univ
    (fun j _ => (hEach j).1.1) (fun j _ => (hEach j).2)
  have hNorm (j : Fin A.count) : ‖(u.val j).val‖ ≤ ‖u‖ := by
    change ‖u.val j‖ ≤ ‖u.val‖
    exact norm_le_pi_norm u.val j
  have hBudget : (∑ j,B j*(R j*‖(u.val j).val‖)) ≤ C*‖u‖ := by
    calc
      _ = ∑ j,(B j*R j)*‖(u.val j).val‖ := Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ ∑ j,(B j*R j)*‖u‖ := Finset.sum_le_sum
        (fun j _ => mul_le_mul_of_nonneg_left (hNorm j) (mul_nonneg (hB j).le (hR j).le))
      _ = (∑ j,B j*R j)*‖u‖ := (Finset.sum_mul ..).symm
      _ ≤ C*‖u‖ := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (norm_nonneg _)
  exact ⟨hC2,holderBound_mono_const hLow hBudget⟩

end Yau.Proofs.F05Aux
