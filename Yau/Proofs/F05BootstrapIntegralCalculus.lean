import Yau.Proofs.F05BootstrapClosedDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiation of an actual compact rectangle integral, including its
closed spatial face. Compact continuity supplies every dominating bound. -/

open Set Filter MeasureTheory
open scoped Topology Interval
noncomputable section
namespace Yau.Proofs.F05Aux

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem F05_compact_parameter_integral_continuous {X : Set E} (hX : IsCompact X)
    {a b : ℝ} {W : E → ℝ → V}
    (hW : ContinuousOn (fun z : E × ℝ => W z.1 z.2) (X ×ˢ uIcc a b)) :
    ContinuousOn (fun x => ∫ t in a..b, W x t) X := by
  obtain ⟨C,hC⟩ := (hX.prod isCompact_uIcc).exists_bound_of_continuousOn hW
  have hSlice (x : E) (hx : x ∈ X) : ContinuousOn (W x) (uIcc a b) :=
    hW.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hx,ht⟩)
  intro x hx
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => C)
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hSlice y hy).intervalIntegrable.aestronglyMeasurable_restrict_uIoc
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact Eventually.of_forall (fun t ht => hC (y,t) ⟨hy,uIoc_subset_uIcc ht⟩)
  · exact intervalIntegrable_const
  · exact Eventually.of_forall (fun t ht =>
      (hW.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun y hy => ⟨hy,uIoc_subset_uIcc ht⟩)) x hx)

theorem F05_compact_parameter_integral_derivative {X : Set E}
    (hX : IsCompact X) (hConv : Convex ℝ X) (hClosure : closure (interior X) = X)
    {a b : ℝ} {W : E → ℝ → V} {G : E → ℝ → E →L[ℝ] V}
    (hW : ContinuousOn (fun z : E × ℝ => W z.1 z.2) (X ×ˢ uIcc a b))
    (hG : ContinuousOn (fun z : E × ℝ => G z.1 z.2) (X ×ˢ uIcc a b))
    (hDeriv : ∀ t ∈ uIcc a b, ∀ x ∈ X, HasFDerivWithinAt (fun y => W y t) (G x t) X x)
    {x : E} (hx : x ∈ X) :
    HasFDerivWithinAt (fun y => ∫ t in a..b, W y t) (∫ t in a..b, G x t) X x := by
  have hWC := F05_compact_parameter_integral_continuous hX hW
  have hGC := F05_compact_parameter_integral_continuous hX hG
  obtain ⟨C,hC⟩ := (hX.prod isCompact_uIcc).exists_bound_of_continuousOn hG
  have hSlice (y : E) (hy : y ∈ X) : ContinuousOn (W y) (uIcc a b) :=
    hW.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hy,ht⟩)
  have hGSlice (y : E) (hy : y ∈ X) : ContinuousOn (G y) (uIcc a b) :=
    hG.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hy,ht⟩)
  have hInterior (y : E) (hy : y ∈ interior X) :
      HasFDerivAt (fun y => ∫ t in a..b, W y t) (∫ t in a..b, G y t) y := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
      (s := interior X) (F' := G) (bound := fun _ => C) (isOpen_interior.mem_nhds hy)
    · filter_upwards [isOpen_interior.mem_nhds hy] with z hz
      exact (hSlice z (interior_subset hz)).intervalIntegrable.aestronglyMeasurable_restrict_uIoc
    · exact (hSlice y (interior_subset hy)).intervalIntegrable
    · exact (hGSlice y (interior_subset hy)).intervalIntegrable.aestronglyMeasurable_restrict_uIoc
    · exact ae_restrict_of_forall_mem measurableSet_uIoc (fun t ht z hz =>
        hC (z,t) ⟨interior_subset hz,uIoc_subset_uIcc ht⟩)
    · exact intervalIntegrable_const
    · exact ae_restrict_of_forall_mem measurableSet_uIoc (fun t ht z hz =>
        (hDeriv t (uIoc_subset_uIcc ht) z (interior_subset hz)).hasFDerivAt
          (mem_of_superset (isOpen_interior.mem_nhds hz) interior_subset))
  rw [← hClosure]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hInterior y hy).differentiableAt.differentiableWithinAt)
    hConv.interior isOpen_interior
  · intro y hy
    rw [hClosure] at hy
    exact (hWC y hy).mono interior_subset
  · apply ((hGC x hx).mono interior_subset).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hInterior y hy).fderiv.symm

end Yau.Proofs.F05Aux
