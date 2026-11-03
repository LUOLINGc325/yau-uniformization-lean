import Yau.LeafProofs.L16LionsTimeTrace

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L16HilbertTimeRegularization Yau.LeafProofs.L16LionsApproximation
  Yau.LeafProofs.L16LionsLimit

/-- The native reflected approximants converge uniformly to any supplied
continuous trace of the original weak curve, at both closed-time endpoints. -/
theorem reflectedSmooth_uniform_to_same_trace
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (J : V →L[ℝ] H) (hJ : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 < T)
    {U : ℝ → V} {R : ℝ → StrongDual ℝ V}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T)))
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    (hw : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding J (U t)) =
        -(∫ t in Ioo 0 T, η t • R t))
    (a : ℝ → H) (ha : ContinuousOn a (Icc 0 T))
    (hae : ∀ᵐ t ∂volume.restrict (Ioo 0 T), J (U t) = a t) :
    TendstoUniformlyOn (fun k t => J (reflectedSmooth T U k t)) a atTop (Icc 0 T) := by
  obtain ⟨b, hb, hbae, huni, _⟩ := smooth_approximation_trace_chain J hJ hT hU hR
    (fun k => (reflectedSmooth_contDiff hT hU k).of_le (by simp))
    (fun k => (reflectedDualSmooth_contDiff hT hR k).continuous.continuousOn)
    (fun k _ ht => reflectedSmooth_derivative (hilbertEmbedding J) hT hU hR hw k ht)
    (reflectedSmooth_L2_tendsto hT hU) (reflectedDualSmooth_L2_tendsto hT hR)
  have hba : b =ᵐ[volume.restrict (Ioo 0 T)] a := by
    filter_upwards [hbae, hae] with t hb ht
    exact hb.symm.trans ht
  rw [restrict_Ioo_eq_restrict_Icc] at hba
  exact huni.congr_right (Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hT) hba hb ha)

end Yau.F04Proof
