import Yau.Proofs.F05BootstrapRectangle
import Yau.Proofs.F05BootstrapGoodLocal

/-! Actual good-time differentiation commutes with the closed spatial
first and second jets. Only local relative Schauder regularity of the
function and its computed first time derivative is used. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2400000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_good_time_spatial_jets {ν : Option (RIdx n)} {T α : ℝ}
    {u : Point n → ℝ} (hu : F05LocalSchauder α ν T u)
    (hw : F05LocalSchauder α ν T (F05GoodPartial T none u))
    {z : Point n} (hz : z ∈ F05PosPatch ν T) :
    HasDerivWithinAt (fun t => F05RelD (F05PosSpace ν) u (z.1,t))
      (F05RelD (F05PosSpace ν) (F05GoodPartial T none u) z) (Ioc 0 T) z.2 ∧
    HasDerivWithinAt (fun t => F05RelDD (F05PosSpace ν) u (z.1,t))
      (F05RelDD (F05PosSpace ν) (F05GoodPartial T none u) z) (Ioc 0 T) z.2 := by
  let Y := F05PosSpace ν
  let w := F05GoodPartial T none u
  have hU := F05_local_schauder_to_relative hu
  have hW := F05_local_schauder_to_relative hw
  have hY : UniqueDiffOn ℝ Y := F05_posSpace_uniqueDiffOn ν
  have hn : ‖z.1‖ < 2 := by simpa only [Metric.mem_ball,dist_zero_right] using hz.1.2
  let R := (‖z.1‖+2)/2
  let s := z.2/2
  have hR : 0 < R := by dsimp only [R]; linarith [norm_nonneg z.1]
  have hR2 : R < 2 := by dsimp only [R]; linarith
  have hs : 0 < s := by dsimp only [s]; linarith [hz.2.1]
  have hsT : s < T := by dsimp only [s]; linarith [hz.2.1,hz.2.2]
  have hSpace : region ν R ⊆ Y := F05_region_subset_posSpace ν hR2
  have hTime : Icc s T ⊆ Ioc 0 T := fun t ht => ⟨hs.trans_le ht.1,ht.2⟩
  have hSub : region ν R ×ˢ Icc s T ⊆ Y ×ˢ Ioc 0 T :=
    fun p hp => ⟨hSpace hp.1,hTime hp.2⟩
  have hFirst (x : Space n) (hx : x ∈ region ν R) (t : ℝ) (ht : t ∈ Icc s T) :
      HasDerivWithinAt (fun a => F05RelD Y u (x,a)) (F05RelD Y w (x,t)) (Icc s T) t := by
    apply F05_rectangle_spatial_parameter_commute (F05_region_isCompact ν R)
      (v := fun x t => u (x,t)) (w := fun x t => w (x,t))
      (A := fun x t => F05RelD Y u (x,t)) (B := fun x t => F05RelD Y w (x,t))
      (F05_region_convex ν R) (F05_region_closure_interior ν hR)
      (F05_region_uniqueDiffOn ν hR) (hW.1.mono hSub) (hW.2.1.mono hSub)
    · intro a ha y hy
      exact (((hU.2.2.2.2.1 a (hTime ha) y (hSpace hy)).differentiableWithinAt
        (by norm_num)).hasFDerivWithinAt).mono hSpace
    · intro a ha y hy
      exact (((hW.2.2.2.2.1 a (hTime ha) y (hSpace hy)).differentiableWithinAt
        (by norm_num)).hasFDerivWithinAt).mono hSpace
    · intro y hy a ha
      exact ((hU.2.2.2.2.2 (y,a) ⟨hSpace hy,hTime ha⟩).hasDerivWithinAt).mono hTime
    · exact hx
    · exact ht
  have hSecond (x : Space n) (hx : x ∈ region ν R) (t : ℝ) (ht : t ∈ Icc s T) :
      HasDerivWithinAt (fun a => F05RelDD Y u (x,a)) (F05RelDD Y w (x,t)) (Icc s T) t := by
    apply F05_rectangle_spatial_parameter_commute (F05_region_isCompact ν R)
      (v := fun x t => F05RelD Y u (x,t)) (w := fun x t => F05RelD Y w (x,t))
      (A := fun x t => F05RelDD Y u (x,t)) (B := fun x t => F05RelDD Y w (x,t))
      (F05_region_convex ν R) (F05_region_closure_interior ν hR)
      (F05_region_uniqueDiffOn ν hR) (hW.2.1.mono hSub) (hW.2.2.1.mono hSub)
    · intro a ha y hy
      exact ((((hU.2.2.2.2.1 a (hTime ha)).fderivWithin hY (m := 1) (by norm_num)).differentiableOn
        (by norm_num) y (hSpace hy)).hasFDerivWithinAt).mono hSpace
    · intro a ha y hy
      exact ((((hW.2.2.2.2.1 a (hTime ha)).fderivWithin hY (m := 1) (by norm_num)).differentiableOn
        (by norm_num) y (hSpace hy)).hasFDerivWithinAt).mono hSpace
    · exact hFirst
    · exact hx
    · exact ht
  have hx : z.1 ∈ region ν R := F05_posSpace_mem_region hz.1 (by dsimp only [R]; linarith)
  have ht : z.2 ∈ Icc s T := ⟨by dsimp only [s]; linarith [hz.2.1],hz.2.2⟩
  have hNear : Icc s T ∈ 𝓝[Ioc 0 T] z.2 := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds
      (Ioi_mem_nhds (show s < z.2 by dsimp only [s]; linarith [hz.2.1]))] with a ha hsa
    exact ⟨hsa.le,ha.2⟩
  have hFirstAt := hFirst z.1 hx z.2 ht
  have hSecondAt := hSecond z.1 hx z.2 ht
  constructor
  · exact hFirstAt.mono_of_mem_nhdsWithin hNear
  · exact HasDerivWithinAt.mono_of_mem_nhdsWithin
      (F := Space n →L[ℝ] Space n →L[ℝ] ℝ) hSecondAt hNear

end Yau.Proofs.F05Aux
