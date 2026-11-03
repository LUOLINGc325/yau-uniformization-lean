import Yau.Proofs.F05PhysicalManifoldOperator
import Yau.Proofs.F05ResidualFamilyBound
import Yau.Proofs.F05OperatorLocality

/-! The physical patch equation holds on the entire original closed domain,
including points outside its chart. The glued residual has its exact factor. -/

open Set Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_global_single_patch_equation {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    (β γ : Fin A.count → M.Carrier → ℝ) (hβ : ∀ j, SmoothFn (β j))
    (hβSupport : ∀ j, tsupport (β j) ⊆ lift A j '' Metric.closedBall 0 (5/8))
    (hγSupport : ∀ j, tsupport (γ j) ⊆ lift A j '' Metric.closedBall 0 (3/4))
    (hβOne : ∀ j z, z ∈ Metric.closedBall (0 : Space n) (1/2) → β j (lift A j z) = 1)
    (hγOne : ∀ j z, z ∈ Metric.closedBall (0 : Space n) (5/8) → γ j (lift A j z) = 1)
    {α T ρ K E : ℝ} (U H : Fin A.count → F05SourceZeroGraph A α T → Point n → ℝ)
    (hData : F05FlowSourcePatchData A χ h c α T ρ K E U H)
    (i : Fin A.count) (f : F05SourceZeroGraph A α T)
    {x : M.Carrier} (hx : x ∈ closure O) {t : ℝ} (ht : t ∈ Icc 0 T) :
    F05IntrinsicLinearOperator c h T (F05ManifoldPatch A i (β i) (U i f)) x t =
      χ i x*F05SourceZeroFun f x t-
        F05ManifoldPatch A i (γ i) (F05FlowOuterResidual A h c β U H i f) x t := by
  have hβ75 : tsupport (β i) ⊆ lift A i '' Metric.closedBall 0 (3/4) :=
    (hβSupport i).trans (image_mono (Metric.closedBall_subset_closedBall (by norm_num : (5/8 : ℝ) ≤ 3/4)))
  by_cases hγx : γ i x = 0
  · have hOut : x ∉ tsupport (β i) := by
      intro hMem
      obtain ⟨z,hz,heq⟩ := hβSupport i hMem
      have hh := hγOne i z hz
      rw [heq,hγx] at hh
      norm_num at hh
    have hβx := image_eq_zero_of_notMem_tsupport hOut
    have hχx : χ i x = 0 := by
      have hh := F05_outer_partition_product hχ i (β i) (hβOne i) x
      simpa only [hβx,zero_mul] using hh.symm
    have hTime : F05ManifoldPatch A i (β i) (U i f) x = fun _ => 0 := by
      funext r
      simp only [F05ManifoldPatch,hβx,zero_mul]
    have hLocal : (fun y => F05ManifoldPatch A i (β i) (U i f) y t) =ᶠ[𝓝 x] 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hOut] with y hy
      simp only [F05ManifoldPatch,hy,Pi.zero_apply,zero_mul]
    unfold F05IntrinsicLinearOperator
    rw [hTime,F05_laplacian_locally_zero (h t) hLocal]
    simp only [derivWithin_fun_const,Pi.zero_apply,mul_zero,sub_zero,hχx,zero_mul,F05ManifoldPatch,hγx]
  · have hCoord := F05_supported_coord hA i (hγSupport i) hx hγx
    let q : Point n := (F05Coord A i x,t)
    have hq : q ∈ F05Q A i T := ⟨hCoord.1,ht⟩
    have hInfo := (hData i).2.2.2 f
    have hEq := F05_physical_manifold_patch_equation hA hχ h c i (hβ i) hβ75 (hβOne i)
      (U i f) (holderGraphFun (f.val i)) (H i f) hInfo.1.1 hInfo.2.2.2.2.2.1 hq
    have hNested := F05_nested_residual_product hA i (hβSupport i) (hγSupport i) (hγOne i)
      (F05PrincipalExtension (F05FlowPrincipal A i h c)) (F05DriftExtension (F05FlowDrift A i h c))
      (U i f) (H i f) q
    have hGamma : F05ModelOuterCutoff A i (γ i) q.1 = γ i x := by
      rw [F05ModelOuterCutoff_eq hA i (hγSupport i) (F05D_mem_ball hCoord.1),hCoord.2.2]
    have hPartition : F05ModelPartition A χ i q.1 = χ i x := by
      rw [F05ModelPartition_eq hA hχ i (F05D_mem_ball hCoord.1),hCoord.2.2]
    have hSource : holderGraphFun (f.val i) q = F05SourceZeroFun f x t := by
      have hh := F05SourceZeroFun_pull f i (F05Coord A i x) hCoord.1 t ht
      rw [hCoord.2.2] at hh
      exact hh.symm
    change F05IntrinsicLinearOperator c h T (F05ManifoldPatch A i (β i) (U i f))
      (lift A i (F05Coord A i x)) t = _ at hEq
    rw [hCoord.2.2,hPartition,hSource] at hEq
    rw [hGamma] at hNested
    change γ i x*F05FlowOuterResidual A h c β U H i f q = F05FlowOuterResidual A h c β U H i f q at hNested
    change F05IntrinsicLinearOperator c h T (F05ManifoldPatch A i (β i) (U i f)) x t =
      χ i x*F05SourceZeroFun f x t-γ i x*F05FlowOuterResidual A h c β U H i f q
    exact hEq.trans (congrArg (fun r => χ i x*F05SourceZeroFun f x t-r) hNested.symm)

end Yau.Proofs.F05Aux
