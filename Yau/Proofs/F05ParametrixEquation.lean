import Yau.Proofs.F05GlobalPatchEquation
import Yau.Proofs.F05IntrinsicFiniteSum

/-! The actual finite manifold parametrix has the literal original source
minus its complete native-plus-cutoff residual on the same closed domain. -/

open Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_global_parametrix_equation {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    (β γ : Fin A.count → M.Carrier → ℝ) (hβ : ∀ j, SmoothFn (β j))
    (hβSupport : ∀ j, tsupport (β j) ⊆ lift A j '' Metric.closedBall 0 (5/8))
    (hγSupport : ∀ j, tsupport (γ j) ⊆ lift A j '' Metric.closedBall 0 (3/4))
    (hβOne : ∀ j z, z ∈ Metric.closedBall (0 : Space n) (1/2) → β j (lift A j z) = 1)
    (hγOne : ∀ j z, z ∈ Metric.closedBall (0 : Space n) (5/8) → γ j (lift A j z) = 1)
    {α T ρ K E : ℝ} (hα : 0 < α) (hα1 : α < 1) (hT1 : T ≤ 1)
    (U H : Fin A.count → F05SourceZeroGraph A α T → Point n → ℝ)
    (hData : F05FlowSourcePatchData A χ h c α T ρ K E U H)
    (f : F05SourceZeroGraph A α T) {x : M.Carrier} (hx : x ∈ closure O)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    F05IntrinsicLinearOperator c h T (F05FiniteManifoldPatch A β (fun j => U j f)) x t =
      F05SourceZeroFun f x t-
        F05FiniteManifoldPatch A γ (fun j => F05FlowOuterResidual A h c β U H j f) x t := by
  classical
  have hβ75 (j : Fin A.count) : tsupport (β j) ⊆ lift A j '' Metric.closedBall 0 (3/4) :=
    (hβSupport j).trans (image_mono (Metric.closedBall_subset_closedBall (by norm_num : (5/8 : ℝ) ≤ 3/4)))
  have hC2 (j i : Fin A.count) :
      C2 (F05Q A i T) (pull A i (F05ManifoldPatch A j (β j) (U j f))) := by
    obtain ⟨B,hB,hBudget⟩ := F05_manifold_patch_budget hA j (hβ j) (hβ75 j) hα hα1
    have hInfo := (hData j).2.2.2 f
    exact (hBudget T _ _ (U j f) hT1 hInfo.1 hInfo.2.1 i).1.1
  have hSum := F05_intrinsic_operator_finite_sum hA h c T
    (fun j => F05ManifoldPatch A j (β j) (U j f)) hC2 hx ht
  have hEach (j : Fin A.count) := F05_global_single_patch_equation hA hχ h c β γ hβ
    hβSupport hγSupport hβOne hγOne U H hData j f hx ht
  obtain ⟨V,hV,hKV,hPartition⟩ := hχ.2.2.2
  calc
    _ = ∑ j,F05IntrinsicLinearOperator c h T (F05ManifoldPatch A j (β j) (U j f)) x t := hSum
    _ = ∑ j,(χ j x*F05SourceZeroFun f x t-
        F05ManifoldPatch A j (γ j) (F05FlowOuterResidual A h c β U H j f) x t) :=
      Finset.sum_congr rfl (fun j _ => hEach j)
    _ = (∑ j,χ j x)*F05SourceZeroFun f x t-
        ∑ j,F05ManifoldPatch A j (γ j) (F05FlowOuterResidual A h c β U H j f) x t := by
      rw [Finset.sum_sub_distrib,Finset.sum_mul]
    _ = _ := by rw [hPartition x (hKV hx),one_mul]; rfl

end Yau.Proofs.F05Aux
