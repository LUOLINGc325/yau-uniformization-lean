import Yau.Proofs.F01BoundaryRatio

/-! The small derivative budget controls the actual integral in R. Together
with the genuine FTC identity it keeps every rescaled point in the sublevel. -/
open Set
open scoped ContDiff Interval
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem boundaryRatio_budget_of_derivative_bound (u : E → ℝ) (z₀ z : E)
    {L c M δ : ℝ} (hL : 0 < L) (hc : 0 ≤ c) (hM : 0 ≤ M) (hz : ‖z‖ ≤ 2)
    (hD : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ u (z₀ + (t * (c * δ)) • z)‖ ≤ M)
    (hbudget : 2 * c * M / L ≤ 1 / 2) :
    |c / L * (∫ t in (0 : ℝ)..1, fderiv ℝ u (z₀ + (t * (c * δ)) • z) z)| ≤ 1 / 2 := by
  have hI : |∫ t in (0 : ℝ)..1, fderiv ℝ u (z₀ + (t * (c * δ)) • z) z| ≤ 2 * M := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := 2 * M)
      (f := fun t => fderiv ℝ u (z₀ + (t * (c * δ)) • z) z) (by
        intro t ht
        rw [uIoc_of_le zero_le_one] at ht
        calc
          _ ≤ ‖fderiv ℝ u (z₀ + (t * (c * δ)) • z)‖ * ‖z‖ :=
            ContinuousLinearMap.le_opNorm _ _
          _ ≤ M * 2 := mul_le_mul (hD t ⟨ht.1.le, ht.2⟩) hz (norm_nonneg _) hM
          _ = 2 * M := by ring)
    simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h
  calc
    _ = (c / L) * |∫ t in (0 : ℝ)..1, fderiv ℝ u (z₀ + (t * (c * δ)) • z) z| := by
      rw [abs_mul, abs_of_nonneg (div_nonneg hc hL.le)]
    _ ≤ (c / L) * (2 * M) := mul_le_mul_of_nonneg_left hI (div_nonneg hc hL.le)
    _ = 2 * c * M / L := by ring
    _ ≤ 1 / 2 := hbudget

theorem rescaled_point_below_level {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u U) (z₀ z : E) {L c M δ : ℝ}
    (hL : 0 < L) (hc : 0 ≤ c) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hbase : 1 - u z₀ / L = δ) (hz : ‖z‖ ≤ 2)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, z₀ + (t * (c * δ)) • z ∈ U)
    (hD : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ u (z₀ + (t * (c * δ)) • z)‖ ≤ M)
    (hbudget : 2 * c * M / L ≤ 1 / 2) : u (z₀ + (c * δ) • z) < L := by
  have hb := boundaryRatio_budget_of_derivative_bound u z₀ z hL hc hM hz hD hbudget
  have hr := (boundaryRatio_bounds_of_integral_budget u L c z₀ δ z hb).1
  have hR : 0 < boundaryRatio u L c z₀ δ z := by linarith
  have hg := boundary_gap_factorization hU hu z₀ z L c δ hL.ne' hbase hseg
  apply (div_lt_one hL).mp
  nlinarith [mul_pos hδ hR]

end Yau.NodeProofs.F01Aux
