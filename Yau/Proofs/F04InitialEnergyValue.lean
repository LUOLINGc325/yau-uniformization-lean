import Yau.Proofs.F04InitialTrace
import Yau.Proofs.F04ClassicalWeakGradient

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem initial_energy_value_and_trace {n : ℕ} {O V : Set (Space n)} {S s K : ℝ}
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : V ⊆ O)
    (hs : 0 < s) (hsS : s ≤ S) (hK : 0 ≤ K) {u : Point n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioo 0 S))
    (hbound : ∀ x ∈ V, ∀ t ∈ Ioo 0 s, |u (x, t)| ≤ K * t) :
    MemLp u 2 (productVolume V (Ioo 0 s)) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo 0 s, (∫ x in V, |u (x, t)| ^ 2) ≤ C) ∧
      InitialTrace V 0 u (fun _ => 0) := by
  have hVfin : volume V < ⊤ := (measure_mono subset_closure).trans_lt hVc.measure_lt_top
  have : IsFiniteMeasure (volume.restrict V) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hVfin⟩
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) s)) := ⟨by simp⟩
  have hsub : V ×ˢ Ioo (0 : ℝ) s ⊆ O ×ˢ Ioo 0 S :=
    fun p hp => ⟨hVO hp.1, hp.2.1, hp.2.2.trans_le hsS⟩
  have hmeas : AEStronglyMeasurable u (productVolume V (Ioo 0 s)) := by
    rw [dg_productVolume_eq_restrict]
    exact (hu.continuousOn.mono hsub).aestronglyMeasurable (hV.prod isOpen_Ioo).measurableSet
  have hfull : ∀ᵐ p ∂productVolume V (Ioo 0 s), ‖u p‖ ≤ K * s := by
    rw [dg_productVolume_eq_restrict]
    filter_upwards [ae_restrict_mem (hV.prod isOpen_Ioo).measurableSet] with p hp
    rw [Real.norm_eq_abs]
    exact (hbound p.1 hp.1 p.2 hp.2).trans (mul_le_mul_of_nonneg_left hp.2.2.le hK)
  have hfinite : IsFiniteMeasure (productVolume V (Ioo 0 s)) := inferInstanceAs
    (IsFiniteMeasure ((volume.restrict V).prod (volume.restrict (Ioo (0 : ℝ) s))))
  refine ⟨MemLp.of_bound hmeas (K * s) hfull, ?_, ?_⟩
  · refine ⟨(K * s) ^ 2 * (volume.restrict V).real univ, by positivity, ?_⟩
    intro t ht
    have hh := (linear_growth_slice_bound (μ := volume.restrict V) hK t ht
      ((ae_restrict_iff' hV.measurableSet).mpr (Eventually.of_forall
        (fun x hx => hbound x hx t ht)))).2
    apply hh.trans
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg hK ht.1.le) (mul_le_mul_of_nonneg_left ht.2.le hK) 2)
      measureReal_nonneg
  · change Tendsto (fun t => ∫ x in V, |u (x, t) - 0| ^ 2) (𝓝[>] 0) (𝓝 0)
    simpa only [sub_zero] using linear_growth_initial_trace (μ := volume.restrict V) hs hK
      (fun t ht => (ae_restrict_iff' hV.measurableSet).mpr
        (Eventually.of_forall (fun x hx => hbound x hx t ht)))

end Yau.F04Proof
