import Yau.Proofs.C04BoundedGeometryChartsCayleyModel

/-! Fixed operator-space compactness supplies uniform jets before the geometric family. -/
noncomputable section
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L21Aux
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem exists_coframe_cayley_model_jet_bounds (n : ℕ) :
    ∃ d : ℝ, 0 < d ∧ ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ A : ComplexVector n →L[ℝ] ComplexVector n,
        ‖A - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ d →
        A.IsInvertible ∧ (coframeComplexModel n A + stdComplex n).IsInvertible ∧
          ∀ m, ‖iteratedFDeriv ℝ m (coframeCayleyGraphModel n) A‖ ≤ C m := by
  obtain ⟨d₀, hd₀, hb⟩ := exists_coframe_cayley_model_neighborhood n
  let d := d₀ / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hcond (A : ComplexVector n →L[ℝ] ComplexVector n)
      (hA : ‖A - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ d) :
      A.IsInvertible ∧ (coframeComplexModel n A + stdComplex n).IsInvertible :=
    hb A (by dsimp [d] at hA; linarith)
  have hbound (m : ℕ) : ∃ C : ℝ, 0 < C ∧
      ∀ A : ComplexVector n →L[ℝ] ComplexVector n,
        ‖A - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ d →
        ‖iteratedFDeriv ℝ m (coframeCayleyGraphModel n) A‖ ≤ C := by
    let S := Metric.closedBall (ContinuousLinearMap.id ℝ (ComplexVector n)) d
    have hc : IsCompact S := isCompact_closedBall _ _
    have hs : ContinuousOn (iteratedFDeriv ℝ m (coframeCayleyGraphModel n)) S := by
      intro A hA
      have hn : ‖A - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ d := by
        simpa only [S, Metric.mem_closedBall, dist_eq_norm] using hA
      have HH := coframeCayleyGraphModel_smoothAt A (hcond A hn).1 (hcond A hn).2
      exact (HH.continuousAt_iteratedFDeriv (by simp)).continuousWithinAt
    obtain ⟨C, hC, hbound⟩ := (hc.image_of_continuousOn hs).isBounded.exists_pos_norm_le
    refine ⟨C, hC, ?_⟩
    intro A hA
    exact hbound _ ⟨A, by simpa only [S, Metric.mem_closedBall, dist_eq_norm] using hA, rfl⟩
  choose C hC hbC using hbound
  refine ⟨d, hd, C, hC, ?_⟩
  intro A hA
  exact ⟨(hcond A hA).1, (hcond A hA).2, fun m => hbC m A hA⟩

end Yau.Proofs.C04ChartsAux
