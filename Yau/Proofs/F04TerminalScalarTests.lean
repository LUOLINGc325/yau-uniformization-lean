import Yau.Proofs.F04TerminalTimeTrace

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ContDiff

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L16HilbertTimeRegularization

/-- The actual terminal-zero vector weak identity gives the original scalar
 compact-test identity on the same supplied continuous trace. -/
theorem hilbert_terminal_scalar_tests
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (j : V →L[ℝ] H) {T : ℝ} (hT : 0 < T)
    {U : ℝ → V} {R : ℝ → StrongDual ℝ V} {a : ℝ → H}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T)))
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    (hAE : ∀ᵐ t ∂volume.restrict (Ioo 0 T), j (U t) = a t)
    (hw : ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → η T = 0 →
      (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding j (U t)) = -(∫ t in Ioo 0 T, η t • R t)) :
    ∀ v : V, ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, η t * R t v) = -(∫ t in Ioo 0 T, deriv η t * inner ℝ (a t) (j v)) := by
  intro v η hη _hcη hsη
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by simp)
  have hηT : η T = 0 := image_eq_zero_of_notMem_tsupport (fun ht => (hsη ht).2.false)
  have hiU := integrableOn_continuous_smul_test hT.le
    ((hilbertEmbedding j).integrable_comp (hU.integrable (by norm_num))) hη1.continuous_deriv_one
  have hiR := integrableOn_continuous_smul_test hT.le (hR.integrable (by norm_num)) hη.continuous
  let ev : StrongDual ℝ V →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
  have he := congrArg ev (hw η hη1 hηT)
  rw [map_neg, ← ev.integral_comp_comm hiU, ← ev.integral_comp_comm hiR] at he
  change (∫ t in Ioo 0 T, deriv η t * inner ℝ (j (U t)) (j v)) = -(∫ t in Ioo 0 T, η t * R t v) at he
  have hTrace : (∫ t in Ioo 0 T, deriv η t * inner ℝ (j (U t)) (j v)) =
      ∫ t in Ioo 0 T, deriv η t * inner ℝ (a t) (j v) := by
    apply integral_congr_ae
    filter_upwards [hAE] with t ht
    rw [ht]
  rw [hTrace] at he
  linarith only [he]

end Yau.F04Proof
