import Yau.Blueprint.VariationContracts
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

/-! The frozen spectral expression is the actual continuous functional
calculus. This identifies its positive and negative parts with the finite
matrix order, including matrices indexed by an empty cotangent index. -/

open scoped Matrix ComplexOrder MatrixOrder

noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n : ℕ}

theorem hermitianScalar_eq_cfc (g : ℝ → ℝ) (A : CotangentMatrix n)
    (hA : A.IsHermitian) : hermitianScalar g A = cfc g A := by
  simpa only [hermitianScalar, dif_pos hA, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Function.comp_def, RCLike.ofReal_eq_complex_ofReal]
    using (hA.cfc_eq g).symm

theorem matrixPositive_eq_posPart (A : CotangentMatrix n) (hA : A.IsHermitian) :
    matrixPositive A = A⁺ := by
  rw [matrixPositive, hermitianScalar_eq_cfc _ A hA, CFC.posPart_def,
    cfcₙ_eq_cfc (hf0 := by simp)]
  rfl

theorem matrixNegative_eq_negPart (A : CotangentMatrix n) (hA : A.IsHermitian) :
    matrixNegative A = A⁻ := by
  rw [matrixNegative, hermitianScalar_eq_cfc _ A hA, CFC.negPart_def,
    cfcₙ_eq_cfc (hf0 := by simp)]
  rfl

theorem matrixPositive_posSemidef (A : CotangentMatrix n) :
    (matrixPositive A).PosSemidef := by
  by_cases hA : A.IsHermitian
  · rw [matrixPositive_eq_posPart A hA]
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg A)
  · simp only [matrixPositive, hermitianScalar, dif_neg hA]
    exact Matrix.PosSemidef.zero

theorem matrixNegative_posSemidef (A : CotangentMatrix n) :
    (matrixNegative A).PosSemidef := by
  by_cases hA : A.IsHermitian
  · rw [matrixNegative_eq_negPart A hA]
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg A)
  · simp only [matrixNegative, hermitianScalar, dif_neg hA]
    exact Matrix.PosSemidef.zero

theorem matrixPositive_sub_matrixNegative (A : CotangentMatrix n) (hA : A.IsHermitian) :
    matrixPositive A - matrixNegative A = A := by
  rw [matrixPositive_eq_posPart A hA, matrixNegative_eq_negPart A hA]
  exact CFC.posPart_sub_negPart A (show IsSelfAdjoint A from hA)

theorem matrixPositive_mul_matrixNegative (A : CotangentMatrix n) (hA : A.IsHermitian) :
    matrixPositive A * matrixNegative A = 0 := by
  rw [matrixPositive_eq_posPart A hA, matrixNegative_eq_negPart A hA]
  exact CFC.posPart_mul_negPart A

theorem matrixNegative_mul_matrixPositive (A : CotangentMatrix n) (hA : A.IsHermitian) :
    matrixNegative A * matrixPositive A = 0 := by
  rw [matrixPositive_eq_posPart A hA, matrixNegative_eq_negPart A hA]
  exact CFC.negPart_mul_posPart A

theorem matrix_mul_negative_sq (A : CotangentMatrix n) (hA : A.IsHermitian) :
    A * matrixNegative A ^ 2 = -(matrixNegative A ^ 3) := by
  calc
    A * matrixNegative A ^ 2 =
        (matrixPositive A - matrixNegative A) * matrixNegative A ^ 2 := by
      rw [matrixPositive_sub_matrixNegative A hA]
    _ = matrixPositive A * matrixNegative A * matrixNegative A - matrixNegative A ^ 3 := by
      noncomm_ring
    _ = -(matrixNegative A ^ 3) := by
      rw [matrixPositive_mul_matrixNegative A hA, zero_mul, zero_sub]

theorem trace_mul_negative_sq (A : CotangentMatrix n) (hA : A.IsHermitian) :
    (Matrix.trace (A * matrixNegative A ^ 2)).re =
      -(Matrix.trace (matrixNegative A ^ 3)).re := by
  rw [matrix_mul_negative_sq A hA, Matrix.trace_neg, Complex.neg_re]

theorem trace_negative_pow_nonneg (A : CotangentMatrix n) (k : ℕ) :
    0 ≤ (Matrix.trace (matrixNegative A ^ k)).re :=
  (Complex.nonneg_iff.mp ((matrixNegative_posSemidef A).pow k).trace_nonneg).1

/-- A first-power eigenvalue bound from the third power, without division
by the eigenvalue and without a nonzero-rank assumption. -/
theorem nonneg_le_threshold_add_cube {x τ : ℝ} (hx : 0 ≤ x) (hτ : 0 < τ) :
    x ≤ τ + x ^ 3 / τ ^ 2 := by
  by_cases h : x ≤ τ
  · exact h.trans (le_add_of_nonneg_right (div_nonneg (pow_nonneg hx _) (sq_nonneg τ)))
  · have hτx : τ ≤ x := le_of_lt (lt_of_not_ge h)
    have hs := mul_self_le_mul_self hτ.le hτx
    have hm := mul_le_mul_of_nonneg_left hs hx
    have hcube : x ≤ x ^ 3 / τ ^ 2 := (le_div_iff₀ (sq_pos_of_pos hτ)).2 (by nlinarith)
    linarith

end Yau.Blueprint.V04Proof
