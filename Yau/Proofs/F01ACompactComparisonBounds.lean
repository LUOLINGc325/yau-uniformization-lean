import Yau.Proofs.F01ClosedTimeBounds
import Yau.Proofs.F01RayleighPenalty

/-! Uniform compact bounds extracted from the actual comparison Q and
the scalar caps. These constants depend on the fixed compact weight bound
and horizon, rather than the approximating background's global geometry. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux

def compactComparisonBudget (a D H M ν : ℝ) : ℝ :=
  a * D * H + a * H ^ 2 / 2 + D * M + ν * H

def compactLogdetLowerBudget (a D H M ν : ℝ) : ℝ :=
  2 * (D * M + a * H ^ 2 / 2 + ν * H) / D

theorem comparison_scalar_compact_bounds
    {a D H M ν t P U φ : ℝ}
    (ha : 0 ≤ a) (hD : 0 < D) (hH : 0 ≤ H) (hM : 0 ≤ M) (hν : 0 ≤ ν)
    (hDH : 2 * H ≤ D) (ht0 : 0 ≤ t) (htH : t ≤ H)
    (hP : P ≤ a * t) (hU : U ≤ a * t ^ 2 / 2) (hφ : -M ≤ φ)
    (hQ : 0 ≤ (D - t) * P + U - D * φ + ν * t) :
    (D - t) * P + U - D * φ + ν * t ≤ compactComparisonBudget a D H M ν ∧
      -compactLogdetLowerBudget a D H M ν ≤ P := by
  have hDt : 0 ≤ D - t := by linarith
  have hPcap : P ≤ a * H := hP.trans (mul_le_mul_of_nonneg_left htH ha)
  have hUcap : U ≤ a * H ^ 2 / 2 := by
    have hs : t ^ 2 ≤ H ^ 2 := by nlinarith
    exact hU.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs ha) (by norm_num))
  have hφcap : -D * φ ≤ D * M := by nlinarith [mul_le_mul_of_nonneg_left hφ hD.le]
  have hνcap : ν * t ≤ ν * H := mul_le_mul_of_nonneg_left htH hν
  have hLinear : (D - t) * P ≤ D * (a * H) :=
    (mul_le_mul_of_nonneg_left hPcap hDt).trans
      (mul_le_mul_of_nonneg_right (by linarith : D - t ≤ D) (mul_nonneg ha hH))
  refine ⟨by dsimp only [compactComparisonBudget]; linarith, ?_⟩
  have hS : 0 ≤ D * M + a * H ^ 2 / 2 + ν * H := by positivity
  have hLower : -(D * M + a * H ^ 2 / 2 + ν * H) ≤ (D - t) * P := by linarith
  have hDtHalf : D / 2 ≤ D - t := by linarith
  by_cases hP0 : 0 ≤ P
  · have hA : 0 ≤ compactLogdetLowerBudget a D H M ν := by
      unfold compactLogdetLowerBudget
      positivity
    linarith
  · have hhalf := mul_le_mul_of_nonpos_right hDtHalf (le_of_not_ge hP0)
    have hbound : -(D * M + a * H ^ 2 / 2 + ν * H) ≤ (D / 2) * P := hLower.trans hhalf
    unfold compactLogdetLowerBudget
    rw [← neg_div]
    apply (div_le_iff₀ hD).mpr
    nlinarith

theorem rayleighPenalty_le_twice_product {a q : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) :
    rayleighPenalty a q ≤ 2 * a * q := by
  have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + a * q)
  unfold rayleighPenalty
  linarith

end Yau.NodeProofs.F01Aux
