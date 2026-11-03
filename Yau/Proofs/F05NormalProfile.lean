import Yau.Proofs.F05NormalBuffers
import Yau.Proofs.F05PositivePhysicalPatch

/-! A fixed positive-time physical profile is genuinely smooth on an open
tangential buffer times a closed inward interval, ready for scalar Seeley
extension. This product is proved from the actual supplied atlas. -/

open Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_smooth_normal_profile_product {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) (j : RIdx n) (hν : A.normal i = some j)
    (w : M.Carrier → ℝ → ℝ) {τ T t : ℝ} (ht : t ∈ Icc τ T)
    (hInner : ∀ k, ContDiffOn ℝ ∞ (pull A k w)
      (region (A.normal k) (3/2) ×ˢ Icc τ T))
    {x : Space n} (hx : x ∈ Metric.ball 0 3) (hFace : realCoord x j = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ContDiffOn ℝ ∞
      (fun q : F05Tangential j × ℝ => pull A i w (F05NormalMergeMap j q,t))
      (Metric.ball (F05TangentPoint j x hFace) δ ×ˢ Icc 0 δ) := by
  have hxN : ‖x‖ < 3 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  obtain ⟨δ,hδ,hBuffer⟩ := F05_normal_product_buffer j hFace hxN
  have hSmooth := F05_inner_smooth_to_physical_patch hA w hInner i
  refine ⟨δ,hδ,?_⟩
  apply hSmooth.comp ((F05NormalMergeMap j).contDiff.prodMk contDiff_const).contDiffOn
  intro q hq
  have hInside := hBuffer q hq
  have hBall : F05NormalMergeMap j q ∈ Metric.ball (0 : Space n) 3 := by
    simpa only [Metric.mem_ball,dist_zero_right] using hInside.1
  refine ⟨⟨hBall,?_⟩,ht⟩
  apply (((hA.1 i).2.2.2.2.2.2.2 _ hBall).2.1).mpr
  simpa only [hν] using hInside.2

end Yau.Proofs.F05Aux
