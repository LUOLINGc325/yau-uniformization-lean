import Yau.Proofs.F04FiniteMass

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace Yau.F04Proof

variable {A : Type*} [TopologicalSpace A] [T2Space A]
  [MeasurableSpace A] [BorelSpace A] {μ : Measure A} [IsLocallyFiniteMeasure μ]
  {I : Set ℝ} {v w : A → ℝ → ℝ} {K : Set A}

omit [T2Space A] in
theorem compact_integral_continuousOn (hK : IsCompact K)
    (hv : ContinuousOn (fun p : A × ℝ => v p.1 p.2) (univ ×ˢ I))
    (hsupp : ∀ x t, t ∈ I → x ∉ K → v x t = 0) :
    ContinuousOn (fun t => ∫ x, v x t ∂μ) I := by
  apply continuousOn_integral_of_compact_support (f := fun t x => v x t) hK
  · exact hv.comp continuous_swap.continuousOn (fun _ hp => ⟨hp.2, hp.1⟩)
  · intro t x ht hx
    exact hsupp x t ht hx

/-- The derivative requires joint continuity of the actual derivative, and
only the fixed compact cutoff is used to dominate the integrals. -/
theorem compact_integral_hasDerivAt (hI : IsOpen I) (hK : IsCompact K)
    (hv : ContinuousOn (fun p : A × ℝ => v p.1 p.2) (univ ×ˢ I))
    (hw : ContinuousOn (fun p : A × ℝ => w p.1 p.2) (univ ×ˢ I))
    (hvsupp : ∀ x t, t ∈ I → x ∉ K → v x t = 0)
    (hwsupp : ∀ x t, t ∈ I → x ∉ K → w x t = 0)
    (hd : ∀ x t, t ∈ I → HasDerivAt (v x) (w x t) t)
    {t : ℝ} (ht : t ∈ I) :
    Integrable (fun x => v x t) μ ∧ Integrable (fun x => w x t) μ ∧
      HasDerivAt (fun s => ∫ x, v x s ∂μ) (∫ x, w x t ∂μ) t := by
  have hvc (s : ℝ) (hs : s ∈ I) : Continuous (fun x => v x s) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hv.continuousAt ((isOpen_univ.prod hI).mem_nhds ⟨mem_univ _, hs⟩)).comp
      (continuous_id.prodMk continuous_const).continuousAt
  have hwc (s : ℝ) (hs : s ∈ I) : Continuous (fun x => w x s) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hw.continuousAt ((isOpen_univ.prod hI).mem_nhds ⟨mem_univ _, hs⟩)).comp
      (continuous_id.prodMk continuous_const).continuousAt
  have hiv (s : ℝ) (hs : s ∈ I) : Integrable (fun x => v x s) μ := by
    apply (hvc s hs).integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro x hx
    by_contra hxK
    exact hx (hvsupp x s hs hxK)
  have hiw (s : ℝ) (hs : s ∈ I) : Integrable (fun x => w x s) μ := by
    apply (hwc s hs).integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro x hx
    by_contra hxK
    exact hx (hwsupp x s hs hxK)
  obtain ⟨l, r, htlr, hloc, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds (hI.mem_nhds ht)
  have hc : ContinuousOn (fun p : A × ℝ => ‖w p.1 p.2‖) (K ×ˢ Icc l r) :=
    hw.norm.mono (fun _ hp => ⟨mem_univ _, hsub hp.2⟩)
  obtain ⟨C, hC⟩ := (hK.prod isCompact_Icc).bddAbove_image hc
  let b : A → ℝ := K.indicator (fun _ => C)
  have hb : Integrable b μ :=
    (integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun s x => v x s) (F' := fun s x => w x s) (bound := b) hloc
    (by filter_upwards [hI.mem_nhds ht] with s hs using (hiv s hs).aestronglyMeasurable)
    (hiv t ht) (hiw t ht).aestronglyMeasurable
    (ae_of_all _ (fun x s hs => by
      by_cases hx : x ∈ K
      · exact (show ‖w x s‖ ≤ C from hC ⟨(x, s), ⟨hx, hs.1, hs.2⟩, rfl⟩).trans_eq
          (by simp [b, hx])
      · simp [b, hx, hwsupp x s (hsub hs) hx])) hb
    (ae_of_all _ (fun x s hs => hd x s (hsub hs)))
  exact ⟨hiv t ht, hdiff.1, hdiff.2⟩

end Yau.F04Proof
