import Yau.Proofs.F05BootstrapBackgroundData
import Yau.Proofs.F05BootstrapLocalFields

/-! A smooth fixed background supplies the actual within jets on the
physical positive-time patch. Its ambient jets are identified only for
this already smooth background, never for the unknown solution. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ}

theorem F05_smooth_spatial_slice_differentiable {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {T : ℝ} {f : Point n → V}
    (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 3 ×ˢ Ioc 0 T))
    {z : Point n} (hz : z ∈ Metric.ball 0 3 ×ˢ Ioc 0 T) :
    DifferentiableAt ℝ (fun x => f (x,z.2)) z.1 := by
  have hSlice : ContDiffOn ℝ ∞ (fun x => f (x,z.2)) (Metric.ball 0 3) :=
    hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun x hx => ⟨hx,hz.2⟩)
  exact (hSlice.differentiableOn (by simp) z.1 hz.1).differentiableAt
    (Metric.isOpen_ball.mem_nhds hz.1)

theorem F05_pos_patch_subset_background (ν : Option (RIdx n)) (T : ℝ) :
    F05PosPatch ν T ⊆ Metric.ball 0 3 ×ˢ Ioc 0 T :=
  fun z hz => ⟨Metric.ball_subset_ball (by norm_num : (2 : ℝ) ≤ 3) hz.1.2,hz.2⟩

theorem F05_smooth_background_relative_jets {ν : Option (RIdx n)} {T : ℝ}
    {f : Point n → ℝ} (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 3 ×ˢ Ioc 0 T)) :
    EqOn (F05RelD (F05PosSpace ν) f) (spatialD f) (F05PosPatch ν T) ∧
      EqOn (F05RelDD (F05PosSpace ν) f) (spatialDD f) (F05PosPatch ν T) := by
  have hX := F05_posSpace_uniqueDiffOn ν
  have hSub := F05_pos_patch_subset_background ν T
  have hD : EqOn (F05RelD (F05PosSpace ν) f) (spatialD f) (F05PosPatch ν T) := by
    intro z hz
    exact ((F05_smooth_spatial_slice_differentiable hf (hSub hz)).hasFDerivAt.hasFDerivWithinAt).fderivWithin
      (hX z.1 hz.1)
  refine ⟨hD,?_⟩
  intro z hz
  have hEq : EqOn (fun x => F05RelD (F05PosSpace ν) f (x,z.2))
      (fun x => spatialD f (x,z.2)) (F05PosSpace ν) := by
    intro x hx
    exact @hD (x,z.2) ⟨hx,hz.2⟩
  rw [F05RelDD,fderivWithin_congr hEq (hEq hz.1)]
  have hSmooth := F05_joint_spatial_derivative_smooth Metric.isOpen_ball hf
  exact ((F05_smooth_spatial_slice_differentiable hSmooth (hSub hz)).hasFDerivAt.hasFDerivWithinAt).fderivWithin
    (hX z.1 hz.1)

theorem F05_smooth_background_relative_c2 {ν : Option (RIdx n)} {T : ℝ}
    {f : Point n → ℝ} (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 3 ×ˢ Ioc 0 T)) :
    F05RelC2 (F05PosSpace ν) (Ioc 0 T) f := by
  have hSub := F05_pos_patch_subset_background ν T
  have hJets := F05_smooth_background_relative_jets (ν := ν) hf
  have hSpatial := F05_joint_spatial_jets_smooth Metric.isOpen_ball hf
  have hTime := F05_joint_vector_time_derivative_smooth (uniqueDiffOn_Ioc 0 T) hf
  refine ⟨hf.continuousOn.mono hSub,(hSpatial.1.continuousOn.mono hSub).congr hJets.1,
    (hSpatial.2.continuousOn.mono hSub).congr hJets.2,hTime.continuousOn.mono hSub,?_,?_⟩
  · intro t ht
    have hSlice : ContDiffOn ℝ ∞ (fun x => f (x,t)) (Metric.ball 0 3) :=
      hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun x hx => ⟨hx,ht⟩)
    exact (hSlice.of_le (by simp)).mono (fun x hx =>
      Metric.ball_subset_ball (by norm_num : (2 : ℝ) ≤ 3) hx.2)
  · exact F05_smooth_background_good_diff hf none

end Yau.Proofs.F05Aux
