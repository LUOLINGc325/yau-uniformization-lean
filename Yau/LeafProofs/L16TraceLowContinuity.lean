import Yau.LeafProofs.L16CausalIntegralContinuity

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance traceLowContinuity_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance traceLowContinuity_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance

/-- The actual fixed-age heat value/gradient pair is jointly continuous for a
    bounded parabolic Holder source. -/
theorem heatAverage_firstJet_continuous_of_holder {n : ℕ} {α F r : ℝ}
    (hα : 0 < α) (hr : 0 < r) (hr1 : r ≤ 1) {B : Point n → ℝ}
    (hB : HolderBound α Set.univ B F) :
    Continuous (fun p : Point n => (heatAverage r (fun y => B (y,p.2)) p.1,
      fderiv ℝ (heatAverage r (fun y => B (y,p.2))) p.1)) := by
  obtain ⟨C,hC,hJet⟩ := heatAverage_first_jet_holder_bound (n := n) hα
  have hF0 : 0 ≤ F := hB.1
  have h := hJet B F hB r hr hr1
  have hHolder : HolderBound α Set.univ
      (fun p : Point n => (heatAverage r (fun y => B (y,p.2)) p.1,
        fderiv ℝ (heatAverage r (fun y => B (y,p.2))) p.1)) (C*F*r^(-(1/2 : ℝ))) :=
    ⟨by positivity,fun p hp => h.1 p,fun p hp q hq => h.2 p q⟩
  exact continuousOn_univ.mp (holderBound_continuousOn hα hHolder)

theorem traceSpatialGradientKernel_continuous {n : ℕ} {α F r : ℝ}
    (hα : 0 < α) (hr : 0 < r) (hr1 : r ≤ 1) {B : Point n → ℝ}
    (hB : HolderBound α Set.univ B F) (e : Space n) :
    Continuous (fun p : Point n => traceSpatialGradientKernel e B p.2 p.1 r) := by
  let P := halfSpaceBoundaryProjection e
  have hRet := (heatAverage_firstJet_continuous_of_holder hα hr hr1 hB).comp
    (show Continuous (fun p : Point n => (P p.1,p.2-r)) from by fun_prop)
  have hProfile : Continuous (fun a : ℝ => normalHeatProfile r a) :=
    continuous_iff_continuousAt.mpr fun a => (normalHeatProfile_hasDerivAt r a).continuousAt
  have hHC := hProfile.comp (show Continuous (fun p : Point n => inner ℝ e p.1) from by fun_prop)
  have hGC := (normalGaussianKernel_spatial_smooth r).continuous.comp
    (show Continuous (fun p : Point n => inner ℝ e p.1) from by fun_prop)
  have h := (hHC.smul (hRet.snd.clm_comp_const P)).add
    (((hGC.const_mul 2).mul hRet.fst).smul (continuous_const : Continuous (fun _ : Point n => innerSL ℝ e)))
  convert h using 1
  funext p
  rfl

/-- Causality is pointwise: the genuine heat kernels see the zero-past source
    whenever their age exceeds the observation time. -/
theorem traceSpatialGradientKernel_zero_past {n : ℕ} {B : Point n → ℝ}
    (hPast : ∀ y s, s ≤ 0 → B (y,s) = 0) (e : Space n) (p : Point n) {r : ℝ}
    (hr : p.2 ≤ r) : traceSpatialGradientKernel e B p.2 p.1 r = 0 := by
  have hSlice : (fun y => B (y,p.2-r)) = fun _ : Space n => (0 : ℝ) :=
    funext fun y => hPast y (p.2-r) (sub_nonpos.mpr hr)
  have hAvg : heatAverage r (fun y => B (y,p.2-r)) = fun _ : Space n => (0 : ℝ) := by
    rw [hSlice]
    funext y
    simp only [heatAverage_def,mul_zero,integral_zero]
  simp [traceSpatialGradientKernel,hAvg]

/-- Actual joint continuity of the physical gradient on the closed half space
    slab follows from its causal integrable kernel, including all corners. -/
theorem boundaryTraceGradient_continuousOn {n : ℕ} {α F T : ℝ}
    (hα : 0 < α) (hT : 0 < T) (hT1 : T ≤ 1)
    {e : Space n} (he : ‖e‖ = 1) {B : Point n → ℝ}
    (hB : HolderBound α Set.univ B F) (hPast : ∀ y s, s ≤ 0 → B (y,s) = 0) :
    ContinuousOn (boundaryTraceGradient e B) (cylinder {x | 0 ≤ inner ℝ e x} 0 T) := by
  obtain ⟨C,hC,hKernelBound⟩ := traceSpatialGradientKernel_bound (n := n)
  have hc : Continuous B := continuousOn_univ.mp (holderBound_continuousOn hα hB)
  have hb : ∀ p, |B p| ≤ F := fun p => hB.2.1 p (mem_univ _)
  have hPower : IntervalIntegrable (fun r : ℝ => r^(-(1/2 : ℝ))) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hBI := hPower.const_mul (C*F)
  have hCont : ContinuousOn (fun p : Point n => ∫ r in (0 : ℝ)..p.2,
      traceSpatialGradientKernel e B p.2 p.1 r) (cylinder {x | 0 ≤ inner ℝ e x} 0 T) := by
    apply causalVolterra_continuousOn hT
      (hTime := fun p hp => hp.2)
      (hInt := fun p hp => (traceSpatialGradientKernel_integral hc hb hp.2.1 e p.1 hp.1).1)
      (hZero := fun p hp r hr => traceSpatialGradientKernel_zero_past hPast e p hr)
      (hBound := fun p hp r hr => hKernelBound e he B F hc hb r hr.1 p.2 p.1 hp.1) hBI
    intro r hr
    exact (traceSpatialGradientKernel_continuous hα hr.1 (hr.2.trans hT1) hB e).continuousOn
  exact hCont.congr (fun p hp => (traceSpatialGradientKernel_integral hc hb hp.2.1 e p.1 hp.1).2.symm)

/-- The value kernel is continuous for each genuine positive age. -/
theorem normalTraceValueKernel_continuous {n : ℕ} {α F r : ℝ}
    (hα : 0 < α) (hr : 0 < r) (hr1 : r ≤ 1) {B : Point n → ℝ}
    (hB : HolderBound α Set.univ B F) (e : Space n) :
    Continuous (fun p : Point n => normalHeatProfile r (inner ℝ e p.1)*
      heatAverage r (fun y => B (y,p.2-r)) (halfSpaceBoundaryProjection e p.1)) := by
  have hRet := (heatAverage_firstJet_continuous_of_holder hα hr hr1 hB).comp
    (show Continuous (fun p : Point n => (halfSpaceBoundaryProjection e p.1,p.2-r)) from by fun_prop)
  have hProfile : Continuous (fun a : ℝ => normalHeatProfile r a) :=
    continuous_iff_continuousAt.mpr fun a => (normalHeatProfile_hasDerivAt r a).continuousAt
  exact (hProfile.comp (show Continuous (fun p : Point n => inner ℝ e p.1) from by fun_prop)).mul hRet.fst

/-- Actual joint continuity of the layer value, with no missing initial or
    lateral boundary trace. -/
theorem boundaryTraceLayer_continuousOn {n : ℕ} {α F T : ℝ}
    (hα : 0 < α) (hT : 0 < T) (hT1 : T ≤ 1) (e : Space n) {B : Point n → ℝ}
    (hB : HolderBound α Set.univ B F) (hPast : ∀ y s, s ≤ 0 → B (y,s) = 0) :
    ContinuousOn (boundaryTraceLayer e B) (cylinder {x | 0 ≤ inner ℝ e x} 0 T) := by
  have hc : Continuous B := continuousOn_univ.mp (holderBound_continuousOn hα hB)
  have hb : ∀ p, |B p| ≤ F := fun p => hB.2.1 p (mem_univ _)
  let K : Point n → ℝ → ℝ := fun p r => normalHeatProfile r (inner ℝ e p.1)*
    heatAverage r (fun y => B (y,p.2-r)) (halfSpaceBoundaryProjection e p.1)
  have hZero (p : Point n) {r : ℝ} (hr : p.2 ≤ r) : K p r = 0 := by
    have hSlice : (fun y => B (y,p.2-r)) = fun _ : Space n => (0 : ℝ) :=
      funext fun y => hPast y (p.2-r) (sub_nonpos.mpr hr)
    change normalHeatProfile r (inner ℝ e p.1) *
      heatAverage r (fun y => B (y,p.2-r)) (halfSpaceBoundaryProjection e p.1) = 0
    rw [hSlice]
    simp only [heatAverage_def,mul_zero,integral_zero]
  have hBound : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
      ∀ r ∈ Ioc 0 T, ‖K p r‖ ≤ F := by
    intro p hp r hr
    obtain ⟨hh0,hh1⟩ := normalHeatProfile_bounds hr.1 hp.1
    change |normalHeatProfile r (inner ℝ e p.1)*
      heatAverage r (fun y => B (y,p.2-r)) (halfSpaceBoundaryProjection e p.1)| ≤ F
    rw [abs_mul,abs_of_nonneg hh0]
    have hAvg := heatAverage_bound hr.1 (hc.comp (continuous_id.prodMk continuous_const))
      (fun y => hb (y,p.2-r)) (halfSpaceBoundaryProjection e p.1)
    exact (mul_le_mul_of_nonneg_left hAvg hh0).trans (mul_le_of_le_one_left hB.1 hh1)
  have hCont : ContinuousOn (fun p : Point n => ∫ r in (0 : ℝ)..p.2, K p r)
      (cylinder {x | 0 ≤ inner ℝ e x} 0 T) :=
    causalVolterra_continuousOn hT (K := K) (b := fun _ => F)
      (fun p hp => hp.2)
      (fun p hp => (normalTraceLayer_integrable_and_bound hc hb hp.2.1 hp.1
        (halfSpaceBoundaryProjection e p.1)).1)
      (fun p hp r hr => hZero p hr) hBound intervalIntegrable_const
      (fun r hr => (normalTraceValueKernel_continuous hα hr.1 (hr.2.trans hT1) hB e).continuousOn)
  exact hCont

end Yau.LeafProofs.L16Aux
