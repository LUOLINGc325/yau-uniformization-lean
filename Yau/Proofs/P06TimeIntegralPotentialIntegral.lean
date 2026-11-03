import Yau.Proofs.P06TimeIntegralPotentialJets

/-! Dominated differentiation of the genuine integral from zero. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
namespace Yau.NodeProofs.P06Aux.TimePotential
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Positive-time continuity and a finite-time bound suffice for integrability;
the value assigned at zero is immaterial. -/
theorem intervalIntegrable_of_positive_continuous_bound {v : ℝ → F}
    (hv : ContinuousOn v (Ioi 0)) {T B : ℝ} (hT : 0 < T)
    (hb : ∀ s, 0 < s → s ≤ T → ‖v s‖ ≤ B) :
    IntervalIntegrable v volume 0 T := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).2
  have hm : AEStronglyMeasurable v (volume.restrict (Ioc 0 T)) :=
    (hv.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
  apply (integrable_const B : Integrable (fun _ : ℝ => B) (volume.restrict (Ioc 0 T))).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact hb s hs.1 hs.2

/-- A natural generic version of the original initial-jet condition. -/
def CompactJetInitial {S : Set E} (u : ℝ → E → F) (f : E → F) : Prop :=
  ∀ K : Set E, IsCompact K → K ⊆ S → ∀ j : ℕ,
    ∀ ε > 0, ∃ τ > 0, ∀ s, 0 < s → s < τ → ∀ z ∈ K,
      ‖iteratedFDeriv ℝ j (fun w => u s w - f w) z‖ < ε

variable {S : Set E} (hS : IsOpen S) {u : ℝ → E → F} {f : E → F}
    (hu : ContDiffOn ℝ ∞ (fun p : E × ℝ => u p.2 p.1) (S ×ˢ Ioi 0))
    (hf : ContDiffOn ℝ ∞ f S) (hinit : CompactJetInitial (S := S) u f)

include hS hu hf hinit

/-- Every order of space jet is time integrable all the way to zero. -/
theorem spatialJet_intervalIntegrable (j : ℕ) {z : E} (hz : z ∈ S)
    {T : ℝ} (hT : 0 < T) :
    IntervalIntegrable (fun s => iteratedFDeriv ℝ j (u s) z) volume 0 T := by
  obtain ⟨B, _, hb⟩ := compact_spatialJet_bound hS hu hf hinit isCompact_singleton
    (show {z} ⊆ S from fun w hw => by simpa only [mem_singleton_iff.mp hw] using hz) j hT
  apply intervalIntegrable_of_positive_continuous_bound (B := B) _ hT
    (fun s hs hsT => hb s hs hsT z (mem_singleton z))
  exact (spatialJets_contDiffOn hS hu j).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun s hs => ⟨hz, hs⟩)

/-- The derivative of the time integral of each spatial jet is the integral
of its actual derivative. A single compact spatial neighborhood dominates the
whole interval, including the initial end. -/
theorem hasFDerivAt_integral_spatialJet [ProperSpace E] [CompleteSpace F]
    (j : ℕ) {z : E} (hz : z ∈ S) {T : ℝ} (hT : 0 < T) :
    HasFDerivAt (fun w => ∫ s in (0 : ℝ)..T, iteratedFDeriv ℝ j (u s) w)
      (∫ s in (0 : ℝ)..T, fderiv ℝ (iteratedFDeriv ℝ j (u s)) z) z := by
  letI : NormedAddCommGroup (E →L[ℝ] (E [×j]→L[ℝ] F)) := inferInstance
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hz)
  have hhalf : 0 < r / 2 := by positivity
  have hKS : Metric.closedBall z (r / 2) ⊆ S :=
    (Metric.closedBall_subset_ball (by linarith : r / 2 < r)).trans hrs
  obtain ⟨B, _, hb⟩ := compact_spatialJet_bound hS hu hf hinit
    (isCompact_closedBall z (r / 2)) hKS (j + 1) hT
  have hji := spatialJet_intervalIntegrable hS hu hf hinit j hz hT
  have hdc : ContinuousOn (fun s => fderiv ℝ (iteratedFDeriv ℝ j (u s)) z) (Ioi 0) := by
    intro s hs
    have hjoint := (spatialJets_contDiffOn hS hu j).contDiffAt
      ((hS.prod (isOpen_Ioi : IsOpen (Ioi (0 : ℝ)))).mem_nhds
        (show (z, s) ∈ S ×ˢ Ioi 0 from ⟨hz, hs⟩))
    have harg : ContDiffAt ℝ ∞ (fun q : ℝ × E => (q.2, q.1)) (s, z) :=
      contDiffAt_snd.prodMk contDiffAt_fst
    have hcomp := hjoint.comp (s, z) harg
    change ContDiffAt ℝ ∞
      (Function.uncurry (fun (r : ℝ) (w : E) => iteratedFDeriv ℝ j (u r) w)) (s, z) at hcomp
    exact (hcomp.fderiv (m := 0) (g := fun _ : ℝ => z) contDiffAt_const (by simp)).continuousAt.continuousWithinAt
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (s := Metric.closedBall z (r / 2)) (bound := fun _ => B)
    (Metric.closedBall_mem_nhds z hhalf)
  · filter_upwards [hS.mem_nhds hz] with w hw
    exact (spatialJet_intervalIntegrable hS hu hf hinit j hw hT).def'.aestronglyMeasurable
  · exact hji
  · rw [uIoc_of_le hT.le]
    exact (hdc.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
  · rw [uIoc_of_le hT.le]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    intro w hw
    rw [norm_fderiv_iteratedFDeriv]
    exact hb s hs.1 hs.2 w hw
  · exact intervalIntegrable_const
  · rw [uIoc_of_le hT.le]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    intro w hw
    have hjoint := (spatialJets_contDiffOn hS hu j).contDiffAt
      ((hS.prod (isOpen_Ioi : IsOpen (Ioi (0 : ℝ)))).mem_nhds
        (show (w, s) ∈ S ×ˢ Ioi 0 from ⟨hKS hw, hs.1⟩))
    have harg : ContDiffAt ℝ ∞ (fun v : E => (v, s)) w :=
      contDiffAt_id.prodMk contDiffAt_const
    have hslice := hjoint.comp w harg
    exact (hslice.differentiableAt (by simp)).hasFDerivAt

end Yau.NodeProofs.P06Aux.TimePotential
