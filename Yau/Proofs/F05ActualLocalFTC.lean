import Yau.Proofs.F05ActualJetComponent
import Yau.Proofs.F05ActualFTC
import Yau.Proofs.F05JetFTC

/-! The encoded derivatives of an actual Schauder function satisfy all three
closed FTC kernels on the genuine convex physical chart set. -/

open Set MeasureTheory
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05ActualJetComponent_mem_FTC (A : AtlasData M) (i : Fin A.count)
    {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T) {v : Point n → ℝ}
    (hv : SchauderBound α (F05Q A i T) v C) :
    F05ActualJetComponent hα hv ∈ F05LocalFTCGraph A i α hT := by
  simp only [F05LocalFTCGraph,Submodule.mem_inf,Submodule.mem_iInf,LinearMap.mem_ker]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro z w t
    have hG : ContinuousOn (fun x : Space n => spatialD v (x,t.val)) (F05D A i) :=
      hv.1.2.1.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx => ⟨hx,t.property⟩)
    have hDerivative (x : Space n) (hx : x ∈ F05D A i) :
        HasFDerivAt (fun y => v (y,t.val)) (spatialD v (x,t.val)) x :=
      (hv.1.2.2.2.2.1 (x,t.val) ⟨hx,t.property⟩).differentiableAt (by norm_num) |>.hasFDerivAt
    have hFTC := F05_actual_segment_ftc (F05D_convex A i) hG hDerivative z.property w.property
    have hInt : (∫ r in (0 : ℝ)..1,
        (F05ActualJetComponent hα hv).2.1 (F05SpatialPath A i T z.property w.property t.property r)) =
        ∫ r in (0 : ℝ)..1,spatialD v (AffineMap.lineMap z.val w.val r,t.val) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr' : r ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hr
      change spatialD v (F05SpatialPath A i T z.property w.property t.property r).val = _
      rw [F05SpatialPath_eq A i T z.property w.property t.property hr']
    change v (w.val,t.val)-v (z.val,t.val)-
      (∫ r in (0 : ℝ)..1,
        (F05ActualJetComponent hα hv).2.1 (F05SpatialPath A i T z.property w.property t.property r)) (w.val-z.val) = 0
    rw [hInt]
    exact sub_eq_zero.mpr hFTC
  · intro z w t
    have hH : ContinuousOn (fun x : Space n => spatialDD v (x,t.val)) (F05D A i) :=
      hv.1.2.2.1.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx => ⟨hx,t.property⟩)
    have hDerivative (x : Space n) (hx : x ∈ F05D A i) :
        HasFDerivAt (fun y => spatialD v (y,t.val)) (spatialDD v (x,t.val)) x := by
      have hh := hv.1.2.2.2.2.1 (x,t.val) ⟨hx,t.property⟩
      exact ((hh.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
    have hFTC := F05_actual_segment_ftc (F05D_convex A i) hH hDerivative z.property w.property
    have hInt : (∫ r in (0 : ℝ)..1,
        (F05ActualJetComponent hα hv).2.2.1.val.1
          (F05SpatialPath A i T z.property w.property t.property r)) =
        ∫ r in (0 : ℝ)..1,spatialDD v (AffineMap.lineMap z.val w.val r,t.val) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr' : r ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hr
      change spatialDD v (F05SpatialPath A i T z.property w.property t.property r).val = _
      rw [F05SpatialPath_eq A i T z.property w.property t.property hr']
    change spatialD v (w.val,t.val)-spatialD v (z.val,t.val)-
      (∫ r in (0 : ℝ)..1,
        (F05ActualJetComponent hα hv).2.2.1.val.1
          (F05SpatialPath A i T z.property w.property t.property r)) (w.val-z.val) = 0
    rw [hInt]
    exact sub_eq_zero.mpr hFTC
  · intro z s t
    have hK : ContinuousOn (fun r : ℝ => timeD (F05Q A i T) v (z.val,r)) (Icc 0 T) :=
      hv.1.2.2.2.1.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun r hr => ⟨z.property,hr⟩)
    have hFiber : {r : ℝ | (z.val,r) ∈ F05Q A i T} = Icc 0 T := by
      ext r
      change (z.val ∈ F05D A i ∧ r ∈ Icc 0 T) ↔ r ∈ Icc 0 T
      exact and_iff_right z.property
    have hDerivative (r : ℝ) (hr : r ∈ Icc 0 T) :
        HasDerivWithinAt (fun a => v (z.val,a)) (timeD (F05Q A i T) v (z.val,r)) (Icc 0 T) r := by
      have hh := hv.1.2.2.2.2.2 (z.val,r) ⟨z.property,hr⟩
      rw [hFiber] at hh
      unfold timeD
      rw [hFiber]
      exact hh.hasDerivWithinAt
    have hFTC := F05_actual_time_ftc hK hDerivative s.property t.property
    have hInt : (∫ r in s.val..t.val,
        (F05ActualJetComponent hα hv).2.2.2.val.1 (F05TimePath A i hT z.property r)) =
        ∫ r in s.val..t.val,timeD (F05Q A i T) v (z.val,r) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr' : r ∈ Icc 0 T := (uIcc_subset_Icc s.property t.property) hr
      change timeD (F05Q A i T) v (F05TimePath A i hT z.property r).val = _
      rw [F05TimePath_eq A i hT z.property hr']
    change v (z.val,t.val)-v (z.val,s.val)-
      (∫ r in s.val..t.val,
        (F05ActualJetComponent hα hv).2.2.2.val.1 (F05TimePath A i hT z.property r)) = 0
    rw [hInt]
    exact sub_eq_zero.mpr hFTC

def F05ActualLocalFTC (A : AtlasData M) (i : Fin A.count)
    {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T) {v : Point n → ℝ}
    (hv : SchauderBound α (F05Q A i T) v C) : F05LocalFTCGraph A i α hT :=
  ⟨F05ActualJetComponent hα hv,F05ActualJetComponent_mem_FTC A i hα hT hv⟩

theorem F05ActualLocalFTC_norm_le (A : AtlasData M) (i : Fin A.count)
    {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T) {v : Point n → ℝ}
    (hv : SchauderBound α (F05Q A i T) v C) : ‖F05ActualLocalFTC A i hα hT hv‖ ≤ C :=
  F05ActualJetComponent_norm_le hα hv

end Yau.Proofs.F05Aux
