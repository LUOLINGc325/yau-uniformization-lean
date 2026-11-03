import Yau.Proofs.V03MatrixBoundaryEntryProduct

/-! The original component-summed boundary seminorm of UᴴBU is controlled
by those of the actual ambient tensor and frame. No finite-energy premise
or positive-rank premise is needed for this finite algebra estimate. -/

open scoped Topology Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem boundaryDSq_matrix_triple_le {U : ℝ → Matrix κ ι ℂ} {B : ℝ → Matrix κ κ ℂ}
    (hU : ∀ b i, Continuous (fun θ => U θ b i))
    (hB : ∀ b c, Continuous (fun θ => B θ b c))
    (hUp : ∀ b i, Function.Periodic (fun θ => U θ b i) (2 * Real.pi))
    (hBp : ∀ b c, Function.Periodic (fun θ => B θ b c) (2 * Real.pi))
    {M : ℝ} (hM : 0 ≤ M) (hU1 : ∀ θ b i, ‖U θ b i‖ ≤ 1)
    (hBM : ∀ θ b c, ‖B θ b c‖ ≤ M) (i j : ι) (b c : κ) :
    boundaryDSq (fun θ (_ : Unit) => star (U θ b i) * B θ b c * U θ c j) ≤
      (3 * ENNReal.ofReal (2 * M ^ 2) + 4) * (matrixDSq U + matrixDSq B) := by
  have hh := boundaryDSq_triple_le (hU b i) (hB b c) (hU c j)
    (hUp b i) (hBp b c) (hUp c j) hM (fun θ => hU1 θ b i)
    (fun θ => hBM θ b c) (fun θ => hU1 θ c j)
  have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  rw [htwo] at hh
  calc
    _ ≤ 2 * (ENNReal.ofReal (2 * M ^ 2) * matrixDSq U + 2 * matrixDSq B) +
        ENNReal.ofReal (2 * M ^ 2) * matrixDSq U := by
      apply hh.trans
      gcongr
      · exact matrixDSq_entry_le U b i
      · exact matrixDSq_entry_le B b c
      · exact matrixDSq_entry_le U c j
    _ = (3 * ENNReal.ofReal (2 * M ^ 2)) * matrixDSq U + 4 * matrixDSq B := by ring
    _ ≤ (3 * ENNReal.ofReal (2 * M ^ 2) + 4) * (matrixDSq U + matrixDSq B) := by
      rw [mul_add]
      apply add_le_add
      · gcongr
        exact le_add_of_nonneg_right (by positivity)
      · gcongr
        exact le_add_of_nonneg_left (by positivity)

theorem matrix_contraction_entry_eq_sum (U : Matrix κ ι ℂ) (B : Matrix κ κ ℂ) (i j : ι) :
    (Uᴴ * B * U) i j = ∑ bc : κ × κ, star (U bc.1 i) * B bc.1 bc.2 * U bc.2 j := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum,
    Fintype.sum_prod_type, mul_assoc]

theorem matrixDSq_contraction_le {U : ℝ → Matrix κ ι ℂ} {B : ℝ → Matrix κ κ ℂ}
    (hU : ∀ b i, Continuous (fun θ => U θ b i))
    (hB : ∀ b c, Continuous (fun θ => B θ b c))
    (hUp : ∀ b i, Function.Periodic (fun θ => U θ b i) (2 * Real.pi))
    (hBp : ∀ b c, Function.Periodic (fun θ => B θ b c) (2 * Real.pi))
    {M : ℝ} (hM : 0 ≤ M) (hU1 : ∀ θ b i, ‖U θ b i‖ ≤ 1)
    (hBM : ∀ θ b c, ‖B θ b c‖ ≤ M) :
    matrixDSq (fun θ => (U θ)ᴴ * B θ * U θ) ≤
      (Fintype.card (ι × ι) : ENNReal) * (Fintype.card (κ × κ) : ENNReal) ^ 2 *
        (3 * ENNReal.ofReal (2 * M ^ 2) + 4) * (matrixDSq U + matrixDSq B) := by
  classical
  have hentry (i j : ι) : boundaryDSq (fun θ (_ : Unit) => ((U θ)ᴴ * B θ * U θ) i j) ≤
      (Fintype.card (κ × κ) : ENNReal) ^ 2 *
        (3 * ENNReal.ofReal (2 * M ^ 2) + 4) * (matrixDSq U + matrixDSq B) := by
    simp_rw [matrix_contraction_entry_eq_sum]
    have hperiod (bc : κ × κ) : Function.Periodic
        (fun θ => star (U θ bc.1 i) * B θ bc.1 bc.2 * U θ bc.2 j) (2 * Real.pi) := by
      have hstar : Function.Periodic (fun θ => star (U θ bc.1 i)) (2 * Real.pi) :=
        fun θ => congrArg star (hUp bc.1 i θ)
      exact (hstar.mul (hBp bc.1 bc.2)).mul (hUp bc.2 j)
    calc
      _ ≤ (Fintype.card (κ × κ) : ENNReal) * ∑ bc : κ × κ,
          boundaryDSq (fun θ (_ : Unit) => star (U θ bc.1 i) * B θ bc.1 bc.2 * U θ bc.2 j) := by
        exact boundaryDSq_sum_le
          (fun bc => ((hU bc.1 i).star.mul (hB bc.1 bc.2)).mul (hU bc.2 j))
          hperiod
      _ ≤ (Fintype.card (κ × κ) : ENNReal) * ∑ _bc : κ × κ,
          (3 * ENNReal.ofReal (2 * M ^ 2) + 4) * (matrixDSq U + matrixDSq B) := by
        gcongr with bc
        exact boundaryDSq_matrix_triple_le hU hB hUp hBp hM hU1 hBM i j bc.1 bc.2
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  change boundaryDSq (fun θ (ij : ι × ι) => ((U θ)ᴴ * B θ * U θ) ij.1 ij.2) ≤ _
  rw [boundaryDSq_eq_sum_singleton (fun θ (ij : ι × ι) => ((U θ)ᴴ * B θ * U θ) ij.1 ij.2)]
  calc
    _ ≤ ∑ _ij : ι × ι, (Fintype.card (κ × κ) : ENNReal) ^ 2 *
        (3 * ENNReal.ofReal (2 * M ^ 2) + 4) * (matrixDSq U + matrixDSq B) :=
      Finset.sum_le_sum (fun ij _ => hentry ij.1 ij.2)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end Yau.Blueprint.V03Proof
