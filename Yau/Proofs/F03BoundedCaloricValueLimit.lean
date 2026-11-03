import Yau.Proofs.F03CaloricL2Limit

/-! Finite actual cylinder volume and bounded pointwise data produce their own L² limit. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Parabolic
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem bounded_cylinder_value_toLp_limit
    (O : Set (Space d)) (l r : ℝ) (hO : IsOpen O) (hOc : IsCompact (closure O))
    (u : ℕ → Point d → ℝ) (v : Point d → ℝ)
    (hu : ∀ j, ContinuousOn (u j) (O ×ˢ Ioo l r))
    (B : ℝ) (hB : 0 ≤ B) (hBound : ∀ j p,p ∈ O ×ˢ Ioo l r → |u j p| ≤ B)
    (hPoint : ∀ p ∈ O ×ˢ Ioo l r,Tendsto (fun j => u j p) atTop (𝓝 (v p))) :
    ∃ hf : ∀ j, MemLp (u j) 2 (volume.restrict (O ×ˢ Ioo l r)),
      ∃ hv : MemLp v 2 (volume.restrict (O ×ˢ Ioo l r)),
        Tendsto (fun j => (hf j).toLp (u j)) atTop (𝓝 (hv.toLp v)) := by
  let μ : Measure (Point d) := volume.restrict (O ×ˢ Ioo l r)
  have hDsub : O ×ˢ Ioo l r ⊆ closure O ×ˢ Icc l r :=
    Set.prod_mono subset_closure Ioo_subset_Icc_self
  letI : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono hDsub).trans_lt
      (hOc.prod isCompact_Icc).measure_lt_top⟩
  have hf : ∀ j, MemLp (u j) 2 μ := by
    intro j
    apply MemLp.of_bound ((hu j).aestronglyMeasurable (hO.prod isOpen_Ioo).measurableSet) B
    filter_upwards [ae_restrict_mem (hO.prod isOpen_Ioo).measurableSet] with p hp
    simpa only [Real.norm_eq_abs] using hBound j p hp
  have hpt : ∀ᵐ p ∂μ,Tendsto (fun j => u j p) atTop (𝓝 (v p)) := by
    filter_upwards [ae_restrict_mem (hO.prod isOpen_Ioo).measurableSet] with p hp
    exact hPoint p hp
  have hvMeas : AEStronglyMeasurable v μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun j => (hf j).aestronglyMeasurable) hpt
  have hbound : ∀ j, ∀ᵐ p ∂μ,‖u j p‖ ≤ B := by
    intro j
    filter_upwards [ae_restrict_mem (hO.prod isOpen_Ioo).measurableSet] with p hp
    simpa only [Real.norm_eq_abs] using hBound j p hp
  have hv := (bounded_pointwise_integral_sq_tendsto μ u v hf hvMeas B hB hbound hpt).1
  exact ⟨hf,hv,bounded_pointwise_toLp_tendsto μ u v hf hv B hB hbound hpt⟩

end Yau.Proofs.F03Aux
