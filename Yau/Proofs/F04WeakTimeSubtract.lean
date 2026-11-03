import Yau.Proofs.F04WeakTimeBinding

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L16HilbertTimeRegularization

/-- Subtraction preserves the genuine dual-valued distributional time
 derivative, using the actual Bochner integrals of the original functions. -/
theorem hilbert_weak_time_subtract
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (j : V →L[ℝ] H) {T : ℝ} (hT : 0 < T)
    {U U₂ : ℝ → V} {R R₂ : ℝ → StrongDual ℝ V}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T)))
    (hU₂ : MemLp U₂ 2 (volume.restrict (Ioo 0 T)))
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    (hR₂ : MemLp R₂ 2 (volume.restrict (Ioo 0 T)))
    (hw : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding j (U t)) =
        -(∫ t in Ioo 0 T, η t • R t))
    (hw₂ : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding j (U₂ t)) =
        -(∫ t in Ioo 0 T, η t • R₂ t)) :
    ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding j (U t - U₂ t)) =
        -(∫ t in Ioo 0 T, η t • (R t - R₂ t)) := by
  intro η hη hcη hsη
  have hdη := ((hη.of_le (by simp) : ContDiff ℝ 1 η).continuous_deriv_one)
  have hiU := integrableOn_continuous_smul_test hT.le
    ((hilbertEmbedding j).integrable_comp (hU.integrable (by norm_num))) hdη
  have hiU₂ := integrableOn_continuous_smul_test hT.le
    ((hilbertEmbedding j).integrable_comp (hU₂.integrable (by norm_num))) hdη
  have hiR := integrableOn_continuous_smul_test hT.le (hR.integrable (by norm_num)) hη.continuous
  have hiR₂ := integrableOn_continuous_smul_test hT.le (hR₂.integrable (by norm_num)) hη.continuous
  have hleft : (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding j (U t - U₂ t)) =
      (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding j (U t)) -
        ∫ t in Ioo 0 T, deriv η t • hilbertEmbedding j (U₂ t) := by
    simp_rw [map_sub, smul_sub]
    exact integral_sub hiU hiU₂
  have hright : (∫ t in Ioo 0 T, η t • (R t - R₂ t)) =
      (∫ t in Ioo 0 T, η t • R t) - ∫ t in Ioo 0 T, η t • R₂ t := by
    simp_rw [smul_sub]
    exact integral_sub hiR hiR₂
  rw [hleft, hright, hw η hη hcη hsη, hw₂ η hη hcη hsη]
  abel

end Yau.F04Proof
