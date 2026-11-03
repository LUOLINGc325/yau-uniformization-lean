import Yau.Proofs.F05BootstrapRectangle
import Yau.Proofs.F05BootstrapTangentRectangleGeometry
import Yau.Proofs.F05BootstrapShiftedSpatial
import Yau.Proofs.F05BootstrapGoodLocal

/-! Tangent good derivatives commute with both actual spatial jets, up to
the true physical face. A two-sided buffered rectangle supplies the
classical line derivative; no joint Hessian derivative is assumed. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2400000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_good_tangent_spatial_jets {ν : Option (RIdx n)} {k : RIdx n} {T α : ℝ}
    (hd : F05GoodLetter ν (some k)) {u : Point n → ℝ}
    (hu : F05LocalSchauder α ν T u)
    (hw : F05LocalSchauder α ν T (F05GoodPartial T (some k) u))
    {z : Point n} (hz : z ∈ F05PosPatch ν T) :
    HasDerivAt (fun a : ℝ => F05RelD (F05PosSpace ν) u (z.1+a • realVec k,z.2))
      (F05RelD (F05PosSpace ν) (F05GoodPartial T (some k) u) z) 0 ∧
    HasDerivAt (fun a : ℝ => F05RelDD (F05PosSpace ν) u (z.1+a • realVec k,z.2))
      (F05RelDD (F05PosSpace ν) (F05GoodPartial T (some k) u) z) 0 := by
  let Y := F05PosSpace ν
  let w := F05GoodPartial T (some k) u
  have hU := F05_local_schauder_to_relative hu
  have hW := F05_local_schauder_to_relative hw
  have hY : UniqueDiffOn ℝ Y := F05_posSpace_uniqueDiffOn ν
  have hGood := F05_local_schauder_good_diff hd hu
  have hn : ‖z.1‖ < 2 := by simpa only [Metric.mem_ball,dist_zero_right] using hz.1.2
  let R := (‖z.1‖+2)/2
  let η := (2-R)/2
  have hR : 0 < R := by dsimp only [R]; linarith [norm_nonneg z.1]
  have hR2 : R < 2 := by dsimp only [R]; linarith
  have hη : 0 < η := by dsimp only [η]; linarith
  have hMargin : R+η < 2 := by dsimp only [η]; linarith
  have hMap (a : ℝ) (ha : a ∈ Icc (-η) η) :
      MapsTo (fun x => x+a • realVec k) (region ν R) Y :=
    fun x hx => F05_tangent_rectangle_maps hd hη.le hMargin hx ha
  let Shift : Space n × ℝ → Point n := fun p => (p.1+p.2 • realVec k,z.2)
  have hShiftCont : Continuous Shift :=
    (continuous_fst.add (continuous_snd.smul continuous_const)).prodMk continuous_const
  have hShiftMap : MapsTo Shift (region ν R ×ˢ Icc (-η) η) (Y ×ˢ Ioc 0 T) :=
    fun p hp => ⟨hMap p.2 hp.2 hp.1,hz.2⟩
  have hWC := hW.1.comp hShiftCont.continuousOn hShiftMap
  have hWDC := hW.2.1.comp hShiftCont.continuousOn hShiftMap
  have hWDDC := hW.2.2.1.comp hShiftCont.continuousOn hShiftMap
  have hFirst (x : Space n) (hx : x ∈ region ν R) (a : ℝ) (ha : a ∈ Icc (-η) η) :
      HasDerivWithinAt (fun b => F05RelD Y u (x+b • realVec k,z.2))
        (F05RelD Y w (x+a • realVec k,z.2)) (Icc (-η) η) a := by
    apply F05_rectangle_spatial_parameter_commute (F05_region_isCompact ν R)
      (v := fun x a => u (x+a • realVec k,z.2)) (w := fun x a => w (x+a • realVec k,z.2))
      (A := fun x a => F05RelD Y u (x+a • realVec k,z.2))
      (B := fun x a => F05RelD Y w (x+a • realVec k,z.2))
      (F05_region_convex ν R) (F05_region_closure_interior ν hR)
      (F05_region_uniqueDiffOn ν hR) hWC hWDC
    · intro b hb y hy
      exact F05_shifted_relative_hasFDeriv
        ((hU.2.2.2.2.1 z.2 hz.2).differentiableOn (by norm_num)) _ (hMap b hb) hy
    · intro b hb y hy
      exact F05_shifted_relative_hasFDeriv
        ((hW.2.2.2.2.1 z.2 hz.2).differentiableOn (by norm_num)) _ (hMap b hb) hy
    · intro y hy b hb
      exact (F05_tangent_parameter_derivative hGood ⟨hMap b hb hy,hz.2⟩).hasDerivWithinAt
    · exact hx
    · exact ha
  have hSecond (x : Space n) (hx : x ∈ region ν R) (a : ℝ) (ha : a ∈ Icc (-η) η) :
      HasDerivWithinAt (fun b => F05RelDD Y u (x+b • realVec k,z.2))
        (F05RelDD Y w (x+a • realVec k,z.2)) (Icc (-η) η) a := by
    apply F05_rectangle_spatial_parameter_commute (F05_region_isCompact ν R)
      (v := fun x a => F05RelD Y u (x+a • realVec k,z.2))
      (w := fun x a => F05RelD Y w (x+a • realVec k,z.2))
      (A := fun x a => F05RelDD Y u (x+a • realVec k,z.2))
      (B := fun x a => F05RelDD Y w (x+a • realVec k,z.2))
      (F05_region_convex ν R) (F05_region_closure_interior ν hR)
      (F05_region_uniqueDiffOn ν hR) hWDC hWDDC
    · intro b hb y hy
      exact F05_shifted_relative_hasFDeriv
        (((hU.2.2.2.2.1 z.2 hz.2).fderivWithin hY (m := 1) (by norm_num)).differentiableOn
          (by norm_num)) _ (hMap b hb) hy
    · intro b hb y hy
      exact F05_shifted_relative_hasFDeriv
        (((hW.2.2.2.2.1 z.2 hz.2).fderivWithin hY (m := 1) (by norm_num)).differentiableOn
          (by norm_num)) _ (hMap b hb) hy
    · exact hFirst
    · exact hx
    · exact ha
  have hx : z.1 ∈ region ν R := F05_posSpace_mem_region hz.1 (by dsimp only [R]; linarith)
  have hZero : (0 : ℝ) ∈ Icc (-η) η := ⟨by linarith,hη.le⟩
  have hNear : Icc (-η) η ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by linarith) hη
  constructor
  · simpa only [zero_smul,add_zero] using (hFirst z.1 hx 0 hZero).hasDerivAt hNear
  · simpa only [zero_smul,add_zero] using HasDerivWithinAt.hasDerivAt (F := Space n →L[ℝ] Space n →L[ℝ] ℝ) (hSecond z.1 hx 0 hZero) hNear

end Yau.Proofs.F05Aux
