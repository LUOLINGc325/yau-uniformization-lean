import Yau.Proofs.F05JetFTC
import Yau.Proofs.F05BCFExtension
import Yau.Proofs.F05SegmentWithinDerivative

/-! Spatial FTC constraints realize the actual first and second derivatives
on the physical interior, using continuity of the graph components. -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_hasFDerivWithinAt_of_chart_FTC {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] (A : AtlasData M) (i : Fin A.count) (T : ℝ)
    (f : BoundedContinuousFunction (F05Q A i T) V)
    (G : BoundedContinuousFunction (F05Q A i T) (Space n →L[ℝ] V))
    (hFTC : ∀ z w : F05D A i, ∀ t : Icc 0 T,
      f ⟨(w.val,t.val),w.property,t.property⟩ - f ⟨(z.val,t.val),z.property,t.property⟩ =
      (∫ r in (0 : ℝ)..1, G (F05SpatialPath A i T z.property w.property t.property r))
        (w.val-z.val)) (t : Icc 0 T) {z : Space n} (hz : z ∈ F05D A i) :
    HasFDerivWithinAt (fun w => F05BCFFun f (w,t.val))
      (G ⟨(z,t.val),hz,t.property⟩) (F05D A i) z := by
  let g : Space n → Space n →L[ℝ] V := fun w => F05BCFFun G (w,t.val)
  have hzD : z ∈ F05D A i := hz
  have hG : ContinuousOn g (F05D A i) :=
    (F05BCFFun_continuousOn G).comp (by fun_prop) (fun w hw => ⟨hw,t.property⟩)
  have hInt (y : Space n) (hy : y ∈ F05D A i) :
      IntervalIntegrable (fun r : ℝ => g (AffineMap.lineMap z y r)) volume 0 1 :=
    (hG.comp (by fun_prop) ((F05D_convex A i).mapsTo_lineMap hzD hy)).intervalIntegrable_of_Icc
      (by norm_num)
  have hEq (y : Space n) (hy : y ∈ F05D A i) :
      F05BCFFun f (y,t.val) - F05BCFFun f (z,t.val) =
        (∫ r in (0 : ℝ)..1, g (AffineMap.lineMap z y r)) (y-z) := by
    have hIntegral : (∫ r in (0 : ℝ)..1,
        G (F05SpatialPath A i T hzD hy t.property r)) =
        ∫ r in (0 : ℝ)..1, g (AffineMap.lineMap z y r) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr' : r ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hr
      have hPath := F05SpatialPath_eq A i T hzD hy t.property hr'
      change G (F05SpatialPath A i T hzD hy t.property r) =
        F05BCFFun G (AffineMap.lineMap z y r,t.val)
      rw [← hPath,F05BCFFun_apply]
    rw [F05BCFFun_apply f ⟨(y,t.val),hy,t.property⟩,
      F05BCFFun_apply f ⟨(z,t.val),hzD,t.property⟩,← hIntegral]
    exact hFTC ⟨z,hzD⟩ ⟨y,hy⟩ t
  have hResult := F05_hasFDerivWithinAt_of_segment_integral (F05D_convex A i) hzD
    (hG z hzD) hInt hEq
  simpa only [g,F05BCFFun_apply G ⟨(z,t.val),hzD,t.property⟩] using hResult

theorem F05_hasFDerivAt_of_chart_FTC {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] (A : AtlasData M) (i : Fin A.count) (T : ℝ)
    (f : BoundedContinuousFunction (F05Q A i T) V)
    (G : BoundedContinuousFunction (F05Q A i T) (Space n →L[ℝ] V))
    (hFTC : ∀ z w : F05D A i, ∀ t : Icc 0 T,
      f ⟨(w.val,t.val),w.property,t.property⟩ - f ⟨(z.val,t.val),z.property,t.property⟩ =
      (∫ r in (0 : ℝ)..1, G (F05SpatialPath A i T z.property w.property t.property r))
        (w.val-z.val)) (t : Icc 0 T) {z : Space n} (hz : z ∈ interior (F05D A i)) :
    HasFDerivAt (fun w => F05BCFFun f (w,t.val))
      (G ⟨(z,t.val),interior_subset hz,t.property⟩) z :=
  (F05_hasFDerivWithinAt_of_chart_FTC A i T f G hFTC t (interior_subset hz)).hasFDerivAt
    (mem_interior_iff_mem_nhds.mp hz)

theorem F05LocalFTCGraph_hasFDerivWithinAt_value (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05LocalFTCGraph A i α hT)
    (t : Icc 0 T) {z : Space n} (hz : z ∈ F05D A i) :
    HasFDerivWithinAt (fun w => F05BCFFun u.val.1 (w,t.val))
      (u.val.2.1 ⟨(z,t.val),hz,t.property⟩) (F05D A i) z :=
  F05_hasFDerivWithinAt_of_chart_FTC A i T u.val.1 u.val.2.1
    (F05LocalFTCGraph_spatial_value A i α hT u) t hz

theorem F05LocalFTCGraph_hasFDerivWithinAt_gradient (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05LocalFTCGraph A i α hT)
    (t : Icc 0 T) {z : Space n} (hz : z ∈ F05D A i) :
    HasFDerivWithinAt (fun w => F05BCFFun u.val.2.1 (w,t.val))
      (u.val.2.2.1.val.1 ⟨(z,t.val),hz,t.property⟩) (F05D A i) z :=
  F05_hasFDerivWithinAt_of_chart_FTC A i T u.val.2.1 u.val.2.2.1.val.1
    (F05LocalFTCGraph_spatial_gradient A i α hT u) t hz

theorem F05LocalFTCGraph_hasFDerivAt_value (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05LocalFTCGraph A i α hT)
    (t : Icc 0 T) {z : Space n} (hz : z ∈ interior (F05D A i)) :
    HasFDerivAt (fun w => F05BCFFun u.val.1 (w,t.val))
      (u.val.2.1 ⟨(z,t.val),interior_subset hz,t.property⟩) z :=
  F05_hasFDerivAt_of_chart_FTC A i T u.val.1 u.val.2.1
    (F05LocalFTCGraph_spatial_value A i α hT u) t hz

theorem F05LocalFTCGraph_hasFDerivAt_gradient (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05LocalFTCGraph A i α hT)
    (t : Icc 0 T) {z : Space n} (hz : z ∈ interior (F05D A i)) :
    HasFDerivAt (fun w => F05BCFFun u.val.2.1 (w,t.val))
      (u.val.2.2.1.val.1 ⟨(z,t.val),interior_subset hz,t.property⟩) z :=
  F05_hasFDerivAt_of_chart_FTC A i T u.val.2.1 u.val.2.2.1.val.1
    (F05LocalFTCGraph_spatial_gradient A i α hT u) t hz

end Yau.Proofs.F05Aux
