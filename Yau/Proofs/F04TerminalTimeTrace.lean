import Yau.Proofs.F04SameTraceEnergy
import Yau.LeafProofs.L16EnergyTimeInitial

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L16HilbertTimeRegularization Yau.LeafProofs.L16LionsTimeTrace
  Yau.LeafProofs.L16EnergyTimeInitial

/-- The terminal-zero identities inherited from the actual finite equations
 produce a continuous zero-initial trace. Interior tests alone are not used to
 infer its initial value. -/
theorem hilbert_terminal_weak_zero_trace
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (j : V →L[ℝ] H) (hj : ‖j‖ ≤ 1) (hjd : DenseRange j) {T : ℝ} (hT : 0 < T)
    {U : ℝ → V} {R : ℝ → StrongDual ℝ V}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T)))
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    (hw : ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → η T = 0 →
      (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding j (U t)) =
        -(∫ t in Ioo 0 T, η t • R t)) :
    ∃ a : ℝ → H, ContinuousOn a (Icc 0 T) ∧ a 0 = 0 ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 T), j (U t) = a t) ∧
      (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
        ‖a t‖ ^ 2 - ‖a s‖ ^ 2 = 2 * ∫ r in s..t, R r (U r)) ∧
      ∀ v : V, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
        inner ℝ (a t - a s) (j v) = ∫ r in s..t, R r v := by
  have hCompact : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding j (U t)) = -(∫ t in Ioo 0 T, η t • R t) := by
    intro η hη _hcη hsη
    apply hw η (hη.of_le (by simp))
    exact image_eq_zero_of_notMem_tsupport (fun ht => (hsη ht).2.false)
  obtain ⟨a, ha, hAE, hChain, hInc⟩ := hilbert_time_trace_pairings j hj hT hU hR hCompact
  have hAffine : ∀ v : V,
      (∫ t in Ioo 0 T, deriv (initialTimeTest T) t * inner ℝ (j (U t)) (j v)) =
        -(∫ t in Ioo 0 T, initialTimeTest T t * R t v) := by
    intro v
    have hη := (initialTimeTest_smooth T).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
    have hηT : initialTimeTest T T = 0 := by simp only [initialTimeTest, div_self hT.ne', sub_self]
    have hiU := integrableOn_continuous_smul_test hT.le
      ((hilbertEmbedding j).integrable_comp (hU.integrable (by norm_num))) hη.continuous_deriv_one
    have hiR := integrableOn_continuous_smul_test hT.le (hR.integrable (by norm_num)) hη.continuous
    let ev : StrongDual ℝ V →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
    have he := congrArg ev (hw (initialTimeTest T) hη hηT)
    rw [map_neg, ← ev.integral_comp_comm hiU, ← ev.integral_comp_comm hiR] at he
    exact he
  have h0 := hilbert_initial_trace_zero j hjd hT hR hAE hInc hAffine
  exact ⟨a, ha, h0, hAE, hChain, hInc⟩

end Yau.F04Proof
