import Yau.Proofs.F05PhysicalResidual
import Yau.Proofs.F05LocalOperatorTransfer
import Yau.Proofs.F05TransitionInverse
import Yau.Proofs.F05FlowPatchSolver
import Yau.Proofs.F05CutoffReconstruction
import Yau.Proofs.F05JetOperator

/-! The actual manifold cutoff patch satisfies the original intrinsic
operator equation. Both native residual and outer commutator are retained. -/

open Set Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_intrinsic_operator_eq_chart {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    (T : ℝ) (w : M.Carrier → ℝ → ℝ) (i : Fin A.count) {p : Point n}
    (hp : p.1 ∈ F05D A i)
    (hSpatial : ContDiffAt ℝ 2 (fun z => w (lift A i z) p.2) p.1) :
    F05IntrinsicLinearOperator c h T w (lift A i p.1) p.2 =
      linearOp (F05Q A i T) (F05FlowPrincipal A i h c) (F05FlowDrift A i h c) (pull A i w) p := by
  have hLap := F05_flattened_laplacian_C2 hA (h p.2) i (fun x => w x p.2) (F05D_mem_ball hp) hSpatial
  change laplacian (h p.2) (fun x => w x p.2) (lift A i p.1) =
    (∑ a,∑ b,flatA (h p.2) A i (p.1,0) a b*spatialDD (pull A i w) p (realVec a) (realVec b))+
      ∑ a,flatB (h p.2) A i (p.1,0) a*spatialD (pull A i w) p (realVec a) at hLap
  have hA0 : flatA (h p.2) A i (p.1,0) = flatA (h p.2) A i p := rfl
  have hB0 : flatB (h p.2) A i (p.1,0) = flatB (h p.2) A i p := rfl
  rw [hA0,hB0] at hLap
  have hTime := F05_timeD_pull A i T w (p := p) hp
  unfold F05IntrinsicLinearOperator
  rw [hLap,← hTime]
  unfold linearOp F05FlowPrincipal F05FlowDrift pull
  simp only [Matrix.smul_apply,smul_eq_mul,mul_add,Finset.mul_sum,mul_assoc]
  ring

theorem F05_own_patch_pull_near {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) {β : M.Carrier → ℝ}
    (hSupport : tsupport β ⊆ lift A i '' Metric.closedBall 0 (3/4))
    (W : Point n → ℝ) {z : Space n} (hz : z ∈ F05D A i) :
    ∀ᶠ y in 𝓝 z, ∀ t : ℝ, pull A i (F05ManifoldPatch A i β W) (y,t) =
      F05ModelOuterCutoff A i β y*W (y,t) := by
  filter_upwards [Metric.isOpen_ball.mem_nhds (F05D_mem_ball hz)] with y hy t
  unfold pull F05ManifoldPatch
  rw [F05Coord_lift_ball hA i hy,F05ModelOuterCutoff_eq hA i hSupport hy]

theorem F05_physical_manifold_patch_equation {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ) (i : Fin A.count)
    {β : M.Carrier → ℝ} (hβ : SmoothFn β)
    (hSupport : tsupport β ⊆ lift A i '' Metric.closedBall 0 (3/4))
    (hOne : ∀ z ∈ Metric.closedBall (0 : Space n) (1/2), β (lift A i z) = 1)
    {T : ℝ} (W f H : Point n → ℝ) (hW : C2 (cylinder univ 0 T) W)
    (hEq : ∀ p ∈ cylinder (closure (F05ModelOpen A i)) 0 T,
      linearOp (cylinder (closure (F05ModelOpen A i)) 0 T)
        (F05PrincipalExtension (F05FlowPrincipal A i h c))
        (F05DriftExtension (F05FlowDrift A i h c)) W p = F05ModelPartition A χ i p.1*f p-H p)
    {p : Point n} (hp : p ∈ F05Q A i T) :
    F05IntrinsicLinearOperator c h T (F05ManifoldPatch A i β W) (lift A i p.1) p.2 =
      F05ModelPartition A χ i p.1*f p-
        F05OuterResidual (F05PrincipalExtension (F05FlowPrincipal A i h c))
          (F05DriftExtension (F05FlowDrift A i h c)) (F05ModelOuterCutoff A i β) W H p := by
  let φ := F05ModelOuterCutoff A i β
  let V : Point n → ℝ := fun q => φ q.1*W q
  have hφ := F05ModelOuterCutoff_contDiff hA i hβ
  have hV : C2 (cylinder univ 0 T) V := c2_spatial_mul (hφ.of_le (by simp)) hW
  have hNear : ∀ x ∈ F05D A i, ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc 0 T,
      V (y,t) = pull A i (F05ManifoldPatch A i β W) (y,t) := by
    intro x hx
    exact (F05_own_patch_pull_near hA i hSupport W hx).mono fun y hy t _ => (hy t).symm
  have hTransfer := F05_local_c2_transfer hV hNear
  have hOp := F05_local_linearOp_transfer hV hNear (F05FlowPrincipal A i h c) (F05FlowDrift A i h c) hp
  have hpModel := F05Q_subset_model_cylinder A i T hp
  have hPlateau : φ p.1*F05ModelPartition A χ i p.1 = F05ModelPartition A χ i p.1 := by
    dsimp only [φ]
    rw [F05ModelOuterCutoff_eq hA i hSupport (F05D_mem_ball hp.1),
      F05ModelPartition_eq hA hχ i (F05D_mem_ball hp.1)]
    exact F05_outer_partition_product hχ i β hOne _
  have hSupport₁ : tsupport φ ⊆ Metric.closedBall 0 1 :=
    (F05ModelOuterCutoff_tsupport hA i hSupport).trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hProduct := F05_outer_original_patch_equation (Q := cylinder (closure (F05ModelOpen A i)) 0 T)
    (F05FlowPrincipal A i h c) (F05FlowDrift A i h c) φ (F05ModelPartition A χ i) W f H
    hSupport₁ ((hφ.of_le (by simp)).contDiffAt)
    (hW.2.2.2.2.1 p ⟨mem_univ _,hp.2⟩) (hEq p hpModel) hPlateau
  calc
    _ = linearOp (F05Q A i T) (F05FlowPrincipal A i h c) (F05FlowDrift A i h c)
        (pull A i (F05ManifoldPatch A i β W)) p :=
      F05_intrinsic_operator_eq_chart hA h c T _ i hp.1 (hTransfer.1.2.2.2.2.1 p hp)
    _ = linearOp (cylinder univ 0 T) (F05FlowPrincipal A i h c) (F05FlowDrift A i h c) V p := hOp.symm
    _ = linearOp (cylinder (closure (F05ModelOpen A i)) 0 T)
        (F05FlowPrincipal A i h c) (F05FlowDrift A i h c) V p :=
      (linearOp_cylinder_restrict_space _ _ V hpModel).symm
    _ = _ := hProduct

end Yau.Proofs.F05Aux
