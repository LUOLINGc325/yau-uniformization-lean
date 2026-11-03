import Yau.Proofs.F04ClosedTimeDerivative
import Yau.Proofs.F04LpParameterContinuity

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

variable {n : ℕ} {M : ComplexManifold n}

def timeClamp (S : ℝ) (hS : 0 ≤ S) (t : ℝ) : ℝ := Set.projIcc 0 S hS t

theorem timeClamp_mem (S : ℝ) (hS : 0 ≤ S) (t : ℝ) : timeClamp S hS t ∈ Icc 0 S :=
  (Set.projIcc 0 S hS t).property

theorem continuous_timeClamp (S : ℝ) (hS : 0 ≤ S) : Continuous (timeClamp S hS) := by
  unfold timeClamp
  fun_prop

theorem timeClamp_eq_of_mem (S : ℝ) (hS : 0 ≤ S) {t : ℝ} (ht : t ∈ Icc 0 S) :
    timeClamp S hS t = t := by
  simp only [timeClamp, Set.projIcc_of_mem hS ht]

theorem compact_scalar_profile_bound
    {S : ℝ} (hS : 0 ≤ S) (v : M.Carrier → ℝ → ℝ)
    (hv : ContinuousOn (fun p : M.Carrier × ℝ => v p.1 p.2) (univ ×ˢ Icc 0 S))
    (K : Set M.Carrier) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ t : ℝ, ‖v x (timeClamp S hS t)‖ ≤ C := by
  obtain ⟨A, hA⟩ := (hK.prod isCompact_Icc).bddAbove_image
    (hv.norm.mono (prod_mono (subset_univ _) (Subset.refl _)))
  refine ⟨max A 0, le_max_right _ _, ?_⟩
  intro x hx t
  exact (hA ⟨(x, timeClamp S hS t), ⟨hx, timeClamp_mem S hS t⟩, rfl⟩).trans (le_max_left _ _)

/-- A continuous scalar profile on a compact physical slab yields the actual
globally clamped continuous L2 profile on every measurable subdomain. -/
theorem compact_scalar_profile_L2
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O K : Set M.Carrier) (hO : MeasurableSet O) (hK : IsCompact K) (hOK : O ⊆ K)
    {S : ℝ} (hS : 0 ≤ S) (v : M.Carrier → ℝ → ℝ)
    (hv : ContinuousOn (fun p : M.Carrier × ℝ => v p.1 p.2) (univ ×ˢ Icc 0 S)) :
    ∃ hf : ∀ t : ℝ, MemLp (fun x => v x (timeClamp S hS t)) 2 (μ.restrict O),
      Continuous (fun t => (hf t).toLp (fun x => v x (timeClamp S hS t))) := by
  let := Yau.LeafProofs.L18Aux.riemannianVolume_locallyFinite g μ hμ
  let : IsFiniteMeasure (μ.restrict O) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (lt_of_le_of_lt (measure_mono hOK) hK.measure_lt_top)⟩
  obtain ⟨C, _hC, hb⟩ := compact_scalar_profile_bound hS v hv K hK
  have hxcont (t : ℝ) : Continuous (fun x => v x (timeClamp S hS t)) :=
    hv.comp_continuous (continuous_id.prodMk continuous_const)
      (fun x => ⟨mem_univ x, timeClamp_mem S hS t⟩)
  have htcont (x : M.Carrier) : Continuous (fun t => v x (timeClamp S hS t)) :=
    hv.comp_continuous (continuous_const.prodMk (continuous_timeClamp S hS))
      (fun t => ⟨mem_univ x, timeClamp_mem S hS t⟩)
  have hf (t : ℝ) : MemLp (fun x => v x (timeClamp S hS t)) 2 (μ.restrict O) := by
    apply MemLp.of_bound (hxcont t).aestronglyMeasurable C
    filter_upwards [ae_restrict_mem hO] with x hx
    exact hb x (hOK hx) t
  refine ⟨hf, continuous_iff_continuousAt.mpr (fun t => ?_)⟩
  apply toLp_tendsto_of_dominated_differences (μ.restrict O)
    (fun s x => v x (timeClamp S hS s)) hf (fun x => v x (timeClamp S hS t)) (hf t)
    (fun _ => 2 * C) (memLp_const (2 * C))
  · apply Eventually.of_forall
    intro s
    filter_upwards [ae_restrict_mem hO] with x hx
    exact (norm_sub_le _ _).trans (by linarith [hb x (hOK hx) s, hb x (hOK hx) t])
  · exact ae_of_all _ (fun x => (htcont x).tendsto t)

end Yau.F04Proof
