import Yau.LeafProofs.L16TraceSpatialGradient

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

/-- Causal kernels can be integrated on one fixed interval. Actual local
    integrability, vanishing beyond the observation time, and an integrable
    uniform bound imply joint continuity of the moving-upper-limit integral. -/
theorem causalVolterra_continuousOn {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Q : Set (Point n)} {T : ℝ} (hT : 0 < T)
    {K : Point n → ℝ → E} {b : ℝ → ℝ}
    (hTime : ∀ p ∈ Q, p.2 ∈ Icc 0 T)
    (hInt : ∀ p ∈ Q, IntervalIntegrable (K p) volume 0 p.2)
    (hZero : ∀ p ∈ Q, ∀ r, p.2 ≤ r → K p r = 0)
    (hBound : ∀ p ∈ Q, ∀ r ∈ Ioc 0 T, ‖K p r‖ ≤ b r)
    (hBI : IntervalIntegrable b volume 0 T)
    (hCont : ∀ r ∈ Ioc 0 T, ContinuousOn (fun p => K p r) Q) :
    ContinuousOn (fun p => ∫ r in (0 : ℝ)..p.2, K p r) Q := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 T)
  have hSub (p : Point n) (hp : p ∈ Q) : Ioc (0 : ℝ) p.2 ⊆ Ioc 0 T :=
    Ioc_subset_Ioc_right (hTime p hp).2
  have hAfter (p : Point n) (hp : p ∈ Q) {r : ℝ} (hr : r ∈ Ioc 0 T)
      (hrp : r ∉ Ioc (0 : ℝ) p.2) : p.2 ≤ r :=
    le_of_not_ge (fun h => hrp ⟨hr.1,h⟩)
  have hMeas (p : Point n) (hp : p ∈ Q) : AEStronglyMeasurable (K p) μ := by
    have hRestrict : μ.restrict (Ioc (0 : ℝ) p.2) = volume.restrict (Ioc (0 : ℝ) p.2) := by
      rw [Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr (hSub p hp)]
    have hInd : AEStronglyMeasurable ((Ioc (0 : ℝ) p.2).indicator (K p)) μ :=
      (aestronglyMeasurable_indicator_iff measurableSet_Ioc).mpr (by
        rw [hRestrict]
        exact (hInt p hp).1.aestronglyMeasurable)
    apply hInd.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    by_cases hrp : r ∈ Ioc (0 : ℝ) p.2
    · exact indicator_of_mem hrp _
    · rw [indicator_of_notMem hrp]
      exact (hZero p hp r (hAfter p hp hr hrp)).symm
  have hFixed (p : Point n) (hp : p ∈ Q) :
      (∫ r in (0 : ℝ)..p.2, K p r) = ∫ r in (0 : ℝ)..T, K p r := by
    rw [intervalIntegral.integral_of_le (hTime p hp).1,intervalIntegral.integral_of_le hT.le]
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc (hSub p hp)
    intro r hr
    exact hZero p hp r (hAfter p hp hr.1 hr.2)
  have hFixedCont : ContinuousOn (fun p => ∫ r in (0 : ℝ)..T, K p r) Q := by
    intro p hp
    apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := b)
    · filter_upwards [self_mem_nhdsWithin] with q hq
      simpa only [uIoc_of_le hT.le] using hMeas q hq
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact ae_of_all _ fun r hr => hBound q hq r (by simpa only [uIoc_of_le hT.le] using hr)
    · exact hBI
    · exact ae_of_all _ fun r hr => hCont r (by simpa only [uIoc_of_le hT.le] using hr) p hp
  exact hFixedCont.congr hFixed

end Yau.LeafProofs.L16Aux
