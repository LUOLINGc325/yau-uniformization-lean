import Yau.Proofs.F04ClosedTimeFTC

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

/-- A continuous genuine energy derivative lifts the actual pivot derivative
 through an injective continuous inclusion. The Banach primitive is constructed
 in the energy space, and equality follows from the true pivot FTC. -/
theorem injective_derivative_lift_on_closed_interval
    {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (j : V →L[ℝ] H) (hj : Function.Injective j) {T : ℝ} (hT : 0 < T)
    (v w : ℝ → V) (hw : Continuous w)
    (hjv : ContinuousOn (fun t => j (v t)) (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => j (v s)) (j (w t)) (Icc 0 T) t) :
    ContDiffOn ℝ 1 v (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt v (w t) (Icc 0 T) t := by
  let F : ℝ → V := fun t => v 0 + ∫ s in (0 : ℝ)..t, w s
  have hF (t : ℝ) : HasDerivAt F (w t) t := by
    exact (intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 t)
      hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt).const_add (v 0)
  have hEq : EqOn v F (Icc 0 T) := by
    intro t ht
    have hFTC := closed_time_FTC hjv (j.continuous.comp hw).continuousOn.integrableOn_Icc
      (fun s hs => (hd s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2))
      ⟨le_rfl, hT.le⟩ ht
    simp only [Function.comp_def] at hFTC
    apply hj
    change j (v t) = j (v 0 + ∫ s in (0 : ℝ)..t, w s)
    rw [map_add, ← j.intervalIntegral_comp_comm (hw.intervalIntegrable 0 t), hFTC]
    abel
  have hDv (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt v (w t) (Icc 0 T) t :=
    (hF t).hasDerivWithinAt.congr_of_mem hEq ht
  refine ⟨?_, hDv⟩
  apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hT)).mpr
  refine ⟨fun t ht => (hDv t ht).differentiableWithinAt, hw.continuousOn.congr ?_⟩
  intro t ht
  exact (hDv t ht).derivWithin (uniqueDiffOn_Icc hT t ht)

end Yau.F04Proof
