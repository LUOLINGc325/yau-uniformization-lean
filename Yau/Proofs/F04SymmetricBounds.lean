import Yau.Proofs.F04HermitianOrder

open scoped Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

theorem symmetric_real_smul_bound {n : ℕ} (G A : Herm n) (b r : ℝ)
    (hl : HermLE (((-b : ℝ) : ℂ) • G) A) (hu : HermLE A ((b : ℂ) • G)) :
    HermLE (((-(|r| * b) : ℝ) : ℂ) • G) ((r : ℂ) • A) ∧
      HermLE ((r : ℂ) • A) (((|r| * b : ℝ) : ℂ) • G) := by
  by_cases hr : 0 ≤ r
  · have hL : (((-(|r| * b) : ℝ) : ℂ) • G) = (r : ℂ) • (((-b : ℝ) : ℂ) • G) := by
      rw [abs_of_nonneg hr]
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_neg, Complex.ofReal_mul]
      ring
    have hU : (((|r| * b : ℝ) : ℂ) • G) = (r : ℂ) • ((b : ℂ) • G) := by
      rw [abs_of_nonneg hr]
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul]
      ring
    rw [hL, hU]
    exact ⟨hermLE_real_smul hr hl, hermLE_real_smul hr hu⟩
  · have hrneg : r < 0 := lt_of_not_ge hr
    have hnr : 0 ≤ -r := (neg_pos.mpr hrneg).le
    have hA : (r : ℂ) • A = -(((-r : ℝ) : ℂ) • A) := by
      ext i j
      simp only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, Complex.ofReal_neg, neg_mul, neg_neg]
    have hL : (((-(|r| * b) : ℝ) : ℂ) • G) =
        -(((-r : ℝ) : ℂ) • ((b : ℂ) • G)) := by
      rw [abs_of_neg hrneg]
      ext i j
      simp only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, Complex.ofReal_neg, Complex.ofReal_mul]
      ring
    have hU : (((|r| * b : ℝ) : ℂ) • G) =
        -(((-r : ℝ) : ℂ) • (((-b : ℝ) : ℂ) • G)) := by
      rw [abs_of_neg hrneg]
      ext i j
      simp only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, Complex.ofReal_neg, Complex.ofReal_mul]
      ring
    rw [hA, hL, hU]
    exact ⟨hermLE_neg (hermLE_real_smul hnr hu), hermLE_neg (hermLE_real_smul hnr hl)⟩

end Yau.F04Proof
