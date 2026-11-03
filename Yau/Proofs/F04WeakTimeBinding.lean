import Yau.Proofs.F04SameTraceApproximation

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L16HilbertTimeRegularization

theorem integrableOn_continuous_smul_test
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} (hT : 0 ≤ T) {q : ℝ → E} (hq : IntegrableOn q (Ioo 0 T))
    {η : ℝ → ℝ} (hη : Continuous η) : IntegrableOn (fun t => η t • q t) (Ioo 0 T) := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mp
  exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr hq).continuousOn_smul
    hη.continuousOn

/-- Scalar distributional tests against every actual energy vector give the
genuine dual-valued weak derivative identity used by the native time trace. -/
theorem hilbert_weak_time_of_scalar_tests
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (j : V →L[ℝ] H) {T : ℝ} (hT : 0 < T)
    {U : ℝ → V} {R : ℝ → StrongDual ℝ V}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T)))
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    (a : ℝ → H) (hae : ∀ᵐ t ∂volume.restrict (Ioo 0 T), j (U t) = a t)
    (hw : ∀ v : V, ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, η t * R t v) =
        -(∫ t in Ioo 0 T, deriv η t * inner ℝ (a t) (j v))) :
    ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding j (U t)) =
        -(∫ t in Ioo 0 T, η t • R t) := by
  intro η hη hcη hsη
  have hiU := integrableOn_continuous_smul_test hT.le
    ((hilbertEmbedding j).integrable_comp (hU.integrable (by norm_num)))
    ((hη.of_le (by simp) : ContDiff ℝ 1 η).continuous_deriv_one)
  have hiR := integrableOn_continuous_smul_test hT.le
    (hR.integrable (by norm_num)) hη.continuous
  apply ContinuousLinearMap.ext
  intro v
  let ev : StrongDual ℝ V →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
  change ev (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding j (U t)) =
    ev (-(∫ t in Ioo 0 T, η t • R t))
  rw [map_neg, ← ev.integral_comp_comm hiU, ← ev.integral_comp_comm hiR]
  change (∫ t in Ioo 0 T, deriv η t * inner ℝ (j (U t)) (j v)) =
    -(∫ t in Ioo 0 T, η t * R t v)
  have he : (∫ t in Ioo 0 T, deriv η t * inner ℝ (j (U t)) (j v)) =
      ∫ t in Ioo 0 T, deriv η t * inner ℝ (a t) (j v) := by
    apply integral_congr_ae
    filter_upwards [hae] with t ht
    rw [ht]
  rw [he]
  linarith only [hw v η hη hcη hsη]

end Yau.F04Proof
