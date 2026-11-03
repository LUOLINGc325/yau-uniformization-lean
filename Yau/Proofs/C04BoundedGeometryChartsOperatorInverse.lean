import Yau.LeafProofs.L21LocalChart

/-! All derivatives of operator inversion on one fixed compact neighborhood
of the identity. These constants precede the geometric family. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Proofs.C04ChartsAux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem exists_operator_inverse_jet_bounds :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ m (A : E →L[ℝ] E), ‖A - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 2 : ℝ) →
        ‖iteratedFDeriv ℝ m (ContinuousLinearMap.inverse : (E →L[ℝ] E) → E →L[ℝ] E) A‖ ≤ C m := by
  classical
  have hbound (m : ℕ) : ∃ C : ℝ, 0 < C ∧
      ∀ A : E →L[ℝ] E, ‖A - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 2 : ℝ) →
        ‖iteratedFDeriv ℝ m (ContinuousLinearMap.inverse : (E →L[ℝ] E) → E →L[ℝ] E) A‖ ≤ C := by
    let S := Metric.closedBall (ContinuousLinearMap.id ℝ E) (1 / 2 : ℝ)
    have hc : IsCompact S := isCompact_closedBall _ _
    have hd : ContinuousOn
        (iteratedFDeriv ℝ m (ContinuousLinearMap.inverse : (E →L[ℝ] E) → E →L[ℝ] E)) S := by
      intro A hA
      have hnorm : ‖A - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 2 : ℝ) := by
        simpa only [S, Metric.mem_closedBall, dist_eq_norm] using hA
      have hi := Yau.LeafProofs.L21Aux.isInvertible_of_norm_sub_id_lt_one A
        (lt_of_le_of_lt hnorm (by norm_num))
      have hs : ContDiffAt ℝ ∞
          (ContinuousLinearMap.inverse : (E →L[ℝ] E) → E →L[ℝ] E) A :=
        hi.contDiffAt_map_inverse
      exact (hs.continuousAt_iteratedFDeriv (by simp)).continuousWithinAt
    obtain ⟨C, hC, hb⟩ := (hc.image_of_continuousOn hd).isBounded.exists_pos_norm_le
    refine ⟨C, hC, ?_⟩
    intro A hA
    apply hb
    exact ⟨A, by simpa only [S, Metric.mem_closedBall, dist_eq_norm] using hA, rfl⟩
  choose C hC hb using hbound
  exact ⟨C, hC, hb⟩

end Yau.Proofs.C04ChartsAux
