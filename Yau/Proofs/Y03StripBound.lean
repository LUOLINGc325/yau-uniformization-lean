import Yau.Proofs.Y03StripCurve

/-! Finite-dimensional compactness supplies a uniform bound on the infinite strip. -/

open scoped Topology Matrix Matrix.Norms.Elementwise
open Set

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem dualNormMat_abs_le {H : Herm n} {ξ : ComplexVector n} {B R : ℝ}
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hH : ∀ i j, ‖H⁻¹ i j‖ ≤ B)
    (hξ : ∀ i, ‖ξ i‖ ≤ R) : |dualNormMat H ξ| ≤ (n : ℝ) ^ 2 * B * R ^ 2 := by
  unfold dualNormMat Matrix.mulVec dotProduct
  calc
    _ ≤ ‖∑ i, star (WithLp.ofLp ξ) i * ∑ j, (H⁻¹).transpose i j * WithLp.ofLp ξ j‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∑ i, ‖star (WithLp.ofLp ξ) i * ∑ j, (H⁻¹).transpose i j * WithLp.ofLp ξ j‖ := norm_sum_le _ _
    _ ≤ ∑ i, R * (∑ j : Fin n, B * R) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Pi.star_apply, norm_star]
      apply mul_le_mul (hξ i) _ (norm_nonneg _) hR
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (hH j i) (hξ j) (norm_nonneg _) hB
    _ = _ := by simp; ring

theorem stripCovector_uniform_bound (μ : Fin n → ℝ) (a : ComplexVector n) (T : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 0 ≤ z.re → z.re ≤ T → ∀ i, ‖stripCovector μ a z i‖ ≤ R := by
  have hc : ContinuousOn (fun τ : ℝ => stripCovector μ a (τ : ℂ)) (Icc 0 T) :=
    ((stripCovector_contDiff μ a).continuous.comp Complex.continuous_ofReal).continuousOn
  obtain ⟨R₀, hR₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max 1 R₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro z hz₀ hzT i
  have heq : ‖stripCovector μ a z i‖ = ‖stripCovector μ a (z.re : ℂ) i‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [stripCovector_norm_sq, stripCovector_norm_sq, Complex.ofReal_re]
  rw [heq]
  exact (PiLp.norm_apply_le _ i).trans ((hR₀ z.re ⟨hz₀, hzT⟩).trans (le_max_right _ _))

theorem inverse_matrix_uniform_bound (H : ℝ → Herm n) (T : ℝ)
    (hc : ∀ i j, ContinuousOn (fun τ => (H τ)⁻¹ i j) (Icc 0 T)) :
    ∃ B : ℝ, 0 < B ∧ ∀ τ ∈ Icc 0 T, ∀ i j, ‖(H τ)⁻¹ i j‖ ≤ B := by
  have hcont : ContinuousOn (fun τ => (H τ)⁻¹) (Icc 0 T) := by
    exact continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hc i j
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max 1 B₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro τ hτ i j
  exact (norm_le_pi_norm (((H τ)⁻¹ : Herm n) i) j).trans
    ((norm_le_pi_norm (fun i j => ((H τ)⁻¹ : Herm n) i j) i).trans
      ((hB₀ τ hτ).trans (le_max_right _ _)))

theorem dualNormMat_strip_bounded (H : ℝ → Herm n) (μ : Fin n → ℝ) (a : ComplexVector n) (T : ℝ)
    (hc : ∀ i j, ContinuousOn (fun τ => (H τ)⁻¹ i j) (Icc 0 T)) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ T →
      dualNormMat (H z.re) (stripCovector μ a z) ≤ C := by
  obtain ⟨B, hB, hH⟩ := inverse_matrix_uniform_bound H T hc
  obtain ⟨R, hR, hξ⟩ := stripCovector_uniform_bound μ a T
  refine ⟨(n : ℝ) ^ 2 * B * R ^ 2, ?_⟩
  intro z hz₀ hzT
  exact (le_abs_self _).trans (dualNormMat_abs_le hB.le hR.le (hH z.re ⟨hz₀, hzT⟩) (hξ z hz₀ hzT))

end Yau.Blueprint.Alignment.Y03Proof
