import Yau.LeafProofs.L10InteriorCalculus

/-! A cutoff and its global derivative budget are selected before all coefficients. -/

noncomputable section
open scoped ContDiff Topology

namespace Yau.LeafProofs

theorem exists_elliptic_cutoff (n : ℕ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ (η : ComplexVector n → ℝ) (M : ℝ),
      0 < M ∧ ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Metric.ball 0 R ∧ (∀ x, |η x| ≤ 1) ∧
      (∀ x i, |fderiv ℝ η x (realVec i)| ≤ M) ∧
      ∀ x ∈ Metric.ball (0 : ComplexVector n) r, η =ᶠ[𝓝 x] 1 := by
  let η : ContDiffBump (0 : ComplexVector n) :=
    ⟨r, (r + R) / 2, hr, by linarith⟩
  obtain ⟨M₀, hM₀⟩ := (η.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    ((η.contDiff : ContDiff ℝ ∞ (η : ComplexVector n → ℝ)).continuous_fderiv (by simp))
  refine ⟨η, max 1 M₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    η.contDiff, η.hasCompactSupport, ?_, ?_, ?_, ?_⟩
  · rw [η.tsupport_eq]
    apply Metric.closedBall_subset_ball
    dsimp [η]
    linarith
  · intro x
    rw [abs_of_nonneg (show 0 ≤ η x from η.nonneg)]
    exact η.le_one
  · intro x i
    have hn : ‖realVec i‖ = 1 := by
      rw [← complexVector_realOrthonormalBasis_apply]
      exact (complexVector_realOrthonormalBasis n).norm_eq_one _
    calc
      _ = ‖fderiv ℝ (η : ComplexVector n → ℝ) x (realVec i)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (η : ComplexVector n → ℝ) x‖ * ‖realVec i‖ :=
        (fderiv ℝ (η : ComplexVector n → ℝ) x).le_opNorm _
      _ ≤ max 1 M₀ := by rw [hn, mul_one]; exact (hM₀ x).trans (le_max_right _ _)
  · intro x hx
    exact η.eventuallyEq_one_of_mem_ball hx

end Yau.LeafProofs
