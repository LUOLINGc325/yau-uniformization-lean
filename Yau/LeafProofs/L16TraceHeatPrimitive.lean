import Yau.LeafProofs.L16TraceLayerMixed

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- The actual age primitive for the boundary heat kernel. Its Poisson term
    retains the genuine boundary source contribution; no time derivative of
    the source or extra initial compatibility is used. -/
theorem normalHeatAverage_integrated_heat_equation {n : ℕ} {α F H a t : ℝ}
    (hα : 0 < α) {g : Space n → ℝ} (hg : Continuous g) (hF : ∀ y, |g y| ≤ F)
    (hH0 : 0 ≤ H) (hH : ∀ x y, |g x-g y| ≤ H*‖x-y‖^α)
    (ha : 0 < a) (ht : 0 < t) (ξ : Space n) :
    IntervalIntegrable (fun r => -normalPoissonKernel a r*heatAverage r g ξ+
      normalHeatProfile r a*heatLaplacian (heatAverage r g) ξ) volume 0 t ∧
    (∫ r in (0 : ℝ)..t, -normalPoissonKernel a r*heatAverage r g ξ+
      normalHeatProfile r a*heatLaplacian (heatAverage r g) ξ) =
      normalHeatProfile t a*heatAverage t g ξ-g ξ := by
  let μ : Measure ℝ := volume.restrict (Ioo 0 t)
  have hμ : μ ≤ volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono_set volume (fun _ hr => hr.1)
  have hAI : AEStronglyMeasurable (fun r => heatAverage r g ξ) μ := by
    simpa only [Function.comp_def] using (retardedHeatAverage_aestronglyMeasurable
      (hg.comp continuous_fst) (ξ,(0 : ℝ))).mono_measure hμ
  have hAvgBound : ∀ᵐ r ∂μ, ‖heatAverage r g ξ‖ ≤ F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (heatAverage_bound hr.1 hg hF ξ)
  have hPI : Integrable (fun r => normalPoissonKernel a r*heatAverage r g ξ) μ := by
    simpa only [mul_comm] using
      (Integrable.mono_measure (normalPoissonKernel_probability ha).1 hμ).bdd_mul hAI hAvgBound
  have hLapI : Integrable (fun r => heatLaplacian (heatAverage r g) ξ) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      (heatAverage_laplacian_integral_of_holder hα hg hF hH0 hH ht ξ).1
  have hHb : ∀ᵐ r ∂μ, ‖normalHeatProfile r a‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [Real.norm_eq_abs,abs_of_nonneg (normalHeatProfile_bounds hr.1 ha.le).1]
    exact (normalHeatProfile_bounds hr.1 ha.le).2
  have hHI : Integrable (fun r => normalHeatProfile r a*heatLaplacian (heatAverage r g) ξ) μ := by
    change Integrable ((fun r => normalHeatProfile r a) •
      (fun r => heatLaplacian (heatAverage r g) ξ)) μ
    exact hLapI.bdd_smul 1
      ((normalHeatProfile_time_aestronglyMeasurable a).mono_measure hμ) hHb
  have hInt : IntervalIntegrable (fun r => -normalPoissonKernel a r*heatAverage r g ξ+
      normalHeatProfile r a*heatLaplacian (heatAverage r g) ξ) volume 0 t := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mpr
    change Integrable (fun r => -normalPoissonKernel a r*heatAverage r g ξ+
      normalHeatProfile r a*heatLaplacian (heatAverage r g) ξ) μ
    convert hPI.neg.add hHI using 1
    funext r
    simp only [Pi.add_apply,Pi.neg_apply]
    ring
  refine ⟨hInt,?_⟩
  have hD (r : ℝ) (hr : r ∈ Ioo 0 t) :
      HasDerivAt (fun s => normalHeatProfile s a*heatAverage s g ξ)
        (-normalPoissonKernel a r*heatAverage r g ξ+
          normalHeatProfile r a*heatLaplacian (heatAverage r g) ξ) r :=
    (normalHeatProfile_time_hasDerivAt hr.1 a).mul
      (heatAverage_hasDerivAt_laplacian_of_bounded hr.1 hg hF ξ)
  have hZero : Tendsto (fun r => normalHeatProfile r a*heatAverage r g ξ)
      (𝓝[>] (0 : ℝ)) (𝓝 (g ξ)) := by
    simpa only [one_mul] using (normalHeatProfile_tendsto_initial_one ha).mul
      (heatAverage_tendsto_initial_of_holder hα hg hF hH0 hH ξ)
  have hEnd : Tendsto (fun r => normalHeatProfile r a*heatAverage r g ξ)
      (𝓝[<] t) (𝓝 (normalHeatProfile t a*heatAverage t g ξ)) :=
    (((normalHeatProfile_time_hasDerivAt ht a).continuousAt.mul
      (heatAverage_hasDerivAt_laplacian_of_bounded ht hg hF ξ).continuousAt).tendsto).mono_left
      nhdsWithin_le_nhds
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht hD hInt hZero hEnd

end Yau.LeafProofs.L16Aux
