import Yau.LeafProofs.L17LocalizedSchauderForwardFTC
import Yau.LeafProofs.L17SchauderSpace

open Set Metric MeasureTheory
open scoped Topology Interval Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def ambientChartGradient (P : UniformChartPartition g) (T gamma : ℝ)
    (a : SchauderAmbient P T gamma) (p : P.centers) (t : Time T) (z : ComplexVector n) : D1 n :=
  if hz : z ∈ ball (0 : ComplexVector n) P.radius then
    ambientGradientCLM P T gamma a ⟨p,(⟨z,hz⟩,t)⟩ else 0

def ambientChartHessian (P : UniformChartPartition g) (T gamma : ℝ)
    (a : SchauderAmbient P T gamma) (p : P.centers) (t : Time T) (z : ComplexVector n) : D2 n :=
  if hz : z ∈ ball (0 : ComplexVector n) P.radius then
    ambientHessianCLM P T gamma a ⟨p,(⟨z,hz⟩,t)⟩ else 0

theorem ambientChartGradient_continuousOn (P : UniformChartPartition g) (T gamma : ℝ)
    (a : SchauderAmbient P T gamma) (p : P.centers) (t : Time T) :
    ContinuousOn (ambientChartGradient P T gamma a p t) (ball (0 : ComplexVector n) P.radius) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h : Continuous (fun z : ↥(ball (0 : ComplexVector n) P.radius) =>
      ambientGradientCLM P T gamma a ⟨p,(z,t)⟩) :=
    (ambientGradientCLM P T gamma a).continuous.comp
      (continuous_sigmaMk.comp (continuous_id.prodMk continuous_const))
  convert h using 1
  funext z
  simp only [Set.domRestrict_apply,ambientChartGradient,dite_eq_left z.property]

theorem ambientChartHessian_continuousOn (P : UniformChartPartition g) (T gamma : ℝ)
    (a : SchauderAmbient P T gamma) (p : P.centers) (t : Time T) :
    ContinuousOn (ambientChartHessian P T gamma a p t) (ball (0 : ComplexVector n) P.radius) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h : Continuous (fun z : ↥(ball (0 : ComplexVector n) P.radius) =>
      ambientHessianCLM P T gamma a ⟨p,(z,t)⟩) :=
    (ambientHessianCLM P T gamma a).continuous.comp
      (continuous_sigmaMk.comp (continuous_id.prodMk continuous_const))
  convert h using 1
  funext z
  simp only [Set.domRestrict_apply,ambientChartHessian,dite_eq_left z.property]

/-- Membership in the original closed Schauder graph follows from genuine
spatial derivatives, genuine closed-time derivatives, and the initial value. -/
theorem ambient_mem_schauderSpace_of_actual_derivatives (P : UniformChartPartition g)
    (T gamma : ℝ) (hT : 0 < T) (a : SchauderAmbient P T gamma)
    (hSpatial : ∀ (p : P.centers) (t : Time T) (z : ComplexVector n) (hz : z ∈ ball 0 P.radius),
      HasFDerivAt (fun w => ambientValueCLM P T gamma a (P.charts.chart p w,t))
        (ambientGradientCLM P T gamma a ⟨p,(⟨z,hz⟩,t)⟩) z)
    (hGradient : ∀ (p : P.centers) (t : Time T) (z : ComplexVector n) (hz : z ∈ ball 0 P.radius),
      HasFDerivAt (ambientChartGradient P T gamma a p t)
        (ambientHessianCLM P T gamma a ⟨p,(⟨z,hz⟩,t)⟩) z)
    (hTime : ∀ (x : M.Carrier) (t : Time T),
      HasDerivWithinAt (fun tau => ambientValueCLM P T gamma a (closedTimePath T hT x tau))
        (ambientTimeCLM P T gamma a (x,t)) (Icc (0 : ℝ) T) (t : ℝ))
    (hInitial : ∀ x : M.Carrier, ambientValueCLM P T gamma a (x,⟨0,⟨le_rfl,hT.le⟩⟩) = 0) :
    a ∈ SchauderSpace P T gamma hT := by
  refine ⟨?_,?_,hInitial⟩
  · intro p z z' t
    have hF := segment_integral_of_hasFDerivAt (convex_ball (0 : ComplexVector n) P.radius)
      (ambientChartGradient_continuousOn P T gamma a p t)
      (fun x hx => by simpa only [ambientChartGradient,dite_eq_left hx] using hSpatial p t x hx)
      z.property z'.property
    have hG := segment_integral_of_hasFDerivAt (convex_ball (0 : ComplexVector n) P.radius)
      (ambientChartHessian_continuousOn P T gamma a p t)
      (fun x hx => by simpa only [ambientChartHessian,dite_eq_left hx] using hGradient p t x hx)
      z.property z'.property
    constructor
    · change ambientValueCLM P T gamma a (chartPoint P T p (z',t))-
        ambientValueCLM P T gamma a (chartPoint P T p (z,t))-
        (∫ theta in (0 : ℝ)..1, ambientGradientCLM P T gamma a
          (localSegmentPath P T p z z' t theta) ((z' : ComplexVector n)-z)) = 0
      apply sub_eq_zero.mpr
      refine hF.trans ?_
      apply intervalIntegral.integral_congr
      intro theta htheta
      have ht : theta ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using htheta
      have hPath := (convex_ball (0 : ComplexVector n) P.radius).lineMap_mem z.property z'.property ht
      simp only [ambientChartGradient,dite_eq_left hPath]
      have hSeg : chartSegment P z z' theta = ⟨AffineMap.lineMap (z : ComplexVector n) z' theta,hPath⟩ :=
        Subtype.ext (chartSegment_of_mem P z z' ht)
      simp only [localSegmentPath,hSeg]
    · change ambientGradientCLM P T gamma a ⟨p,(z',t)⟩-
        ambientGradientCLM P T gamma a ⟨p,(z,t)⟩-
        (∫ theta in (0 : ℝ)..1, ambientHessianCLM P T gamma a
          (localSegmentPath P T p z z' t theta) ((z' : ComplexVector n)-z)) = 0
      apply sub_eq_zero.mpr
      have hG' : ambientGradientCLM P T gamma a ⟨p,(z',t)⟩-
          ambientGradientCLM P T gamma a ⟨p,(z,t)⟩ =
          ∫ theta in (0 : ℝ)..1, ambientChartHessian P T gamma a p t
            (AffineMap.lineMap (z : ComplexVector n) z' theta) ((z' : ComplexVector n)-z) := by
        simpa only [ambientChartGradient,dite_eq_left z.property,dite_eq_left z'.property] using hG
      refine hG'.trans ?_
      apply intervalIntegral.integral_congr
      intro theta htheta
      have ht : theta ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using htheta
      have hPath := (convex_ball (0 : ComplexVector n) P.radius).lineMap_mem z.property z'.property ht
      simp only [ambientChartHessian,dite_eq_left hPath]
      have hSeg : chartSegment P z z' theta = ⟨AffineMap.lineMap (z : ComplexVector n) z' theta,hPath⟩ :=
        Subtype.ext (chartSegment_of_mem P z z' ht)
      simp only [localSegmentPath,hSeg]
  · intro x s t
    have hf : Continuous (fun tau => ambientValueCLM P T gamma a (closedTimePath T hT x tau)) :=
      (ambientValueCLM P T gamma a).continuous.comp (closedTimePath_continuous T hT x)
    have hb : Continuous (fun tau => ambientTimeCLM P T gamma a (closedTimePath T hT x tau)) :=
      (ambientTimeCLM P T gamma a).continuous.comp (closedTimePath_continuous T hT x)
    have hFTC := interval_integral_of_hasDerivWithinAt hf hb
      (fun tau htau => by
        simpa only [closedTimePath,projIcc_of_mem hT.le htau] using hTime x ⟨tau,htau⟩)
      s.property t.property
    change ambientValueCLM P T gamma a (x,t)-ambientValueCLM P T gamma a (x,s)-
      (∫ tau in (s : ℝ)..(t : ℝ), ambientTimeCLM P T gamma a (closedTimePath T hT x tau)) = 0
    apply sub_eq_zero.mpr
    simpa only [closedTimePath,projIcc_val] using hFTC

end Yau.LeafProofs.L17LocalizedSchauderAux
