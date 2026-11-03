import Yau.LeafProofs.L17AtlasCutoffs

/-! Actual scale identities and all-order bounds for the atlas bump functions. -/

noncomputable section

open scoped ContDiff

namespace Yau.LeafProofs.L17Aux

theorem innerChartBump_rescale (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (z : ComplexVector n) :
    innerChartBump n ρ hρ z = innerChartBump n 1 zero_lt_one (ρ⁻¹ • z) := by
  have hratio : (ρ / 2) / (ρ / 4) = 2 := by field_simp; norm_num
  simp only [ContDiffBump.apply, innerChartBump, sub_zero, hratio]
  norm_num
  congr 1
  rw [smul_smul]
  congr 1

theorem outerChartBump_rescale (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (z : ComplexVector n) :
    outerChartBump n ρ hρ z = outerChartBump n 1 zero_lt_one (ρ⁻¹ • z) := by
  have hratio : ρ / (ρ / 2) = 2 := by field_simp
  simp only [ContDiffBump.apply, outerChartBump, sub_zero, hratio]
  norm_num
  congr 1
  rw [smul_smul]
  congr 1

theorem exists_scaled_innerChartBump_jet_bound (n : ℕ) :
    ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧ ∀ (ρ : ℝ) (hρ : 0 < ρ) k (z : ComplexVector n),
      ‖iteratedFDeriv ℝ k (innerChartBump n ρ hρ) z‖ ≤ B k * (ρ⁻¹) ^ k := by
  classical
  let b := innerChartBump n 1 zero_lt_one
  have hbounded (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ z : ComplexVector n,
      ‖iteratedFDeriv ℝ k b z‖ ≤ C := by
    obtain ⟨C, hC, hb⟩ := b.hasCompactSupport.exists_bound_iteratedFDeriv b.contDiff k
    exact ⟨C + 1, by linarith, fun z => (hb k le_rfl z).trans (by linarith)⟩
  choose B hB hb using hbounded
  refine ⟨B, hB, ?_⟩
  intro ρ hρ k z
  have heq : (innerChartBump n ρ hρ : ComplexVector n → ℝ) =
      (fun w => b (ρ⁻¹ • w)) := funext (innerChartBump_rescale n hρ)
  rw [heq, congrFun (iteratedFDeriv_comp_const_smul ρ⁻¹
    (b.contDiff.of_le (by simp : (k : ℕ∞ω) ≤ ∞))) z, norm_smul,
    Real.norm_eq_abs, abs_pow, abs_of_pos (inv_pos.mpr hρ)]
  exact (mul_le_mul_of_nonneg_left (hb k _) (by positivity)).trans_eq (mul_comm _ _)

theorem exists_scaled_outerChartBump_jet_bound (n : ℕ) :
    ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧ ∀ (ρ : ℝ) (hρ : 0 < ρ) k (z : ComplexVector n),
      ‖iteratedFDeriv ℝ k (outerChartBump n ρ hρ) z‖ ≤ B k * (ρ⁻¹) ^ k := by
  classical
  let b := outerChartBump n 1 zero_lt_one
  have hbounded (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ z : ComplexVector n,
      ‖iteratedFDeriv ℝ k b z‖ ≤ C := by
    obtain ⟨C, hC, hb⟩ := b.hasCompactSupport.exists_bound_iteratedFDeriv b.contDiff k
    exact ⟨C + 1, by linarith, fun z => (hb k le_rfl z).trans (by linarith)⟩
  choose B hB hb using hbounded
  refine ⟨B, hB, ?_⟩
  intro ρ hρ k z
  have heq : (outerChartBump n ρ hρ : ComplexVector n → ℝ) =
      (fun w => b (ρ⁻¹ • w)) := funext (outerChartBump_rescale n hρ)
  rw [heq, congrFun (iteratedFDeriv_comp_const_smul ρ⁻¹
    (b.contDiff.of_le (by simp : (k : ℕ∞ω) ≤ ∞))) z, norm_smul,
    Real.norm_eq_abs, abs_pow, abs_of_pos (inv_pos.mpr hρ)]
  exact (mul_le_mul_of_nonneg_left (hb k _) (by positivity)).trans_eq (mul_comm _ _)

end Yau.LeafProofs.L17Aux
