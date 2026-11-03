import Yau.Proofs.F04VariationalTime

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L16HilbertTimeRegularization Yau.LeafProofs.L16LionsTimeTrace

/-- The full quadratic chain holds for the original supplied continuous
 pivot trace at every pair of closed endpoints. -/
theorem hilbert_weak_same_trace_energy
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (j : V →L[ℝ] H) (hj : ‖j‖ ≤ 1) {T : ℝ} (hT : 0 < T)
    {U : ℝ → V} {R : ℝ → StrongDual ℝ V}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T)))
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    (hw : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding j (U t)) =
        -(∫ t in Ioo 0 T, η t • R t))
    (a : ℝ → H) (ha : ContinuousOn a (Icc 0 T))
    (hae : ∀ᵐ t ∂volume.restrict (Ioo 0 T), j (U t) = a t) :
    ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      ‖a t‖ ^ 2 - ‖a s‖ ^ 2 = 2 * ∫ q in s..t, R q (U q) := by
  obtain ⟨b, hb, hbae, hchain⟩ := hilbert_time_trace_chain j hj hT hU hR hw
  have hba : b =ᵐ[volume.restrict (Ioo 0 T)] a := by
    filter_upwards [hbae, hae] with t hbt hat
    exact hbt.symm.trans hat
  rw [restrict_Ioo_eq_restrict_Icc] at hba
  have heq := Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hT) hba hb ha
  intro s hs t ht
  rw [← heq hs, ← heq ht]
  exact hchain s hs t ht

end Yau.F04Proof
