import Yau.Proofs.C02ComplexPullbackOperator
import Yau.Proofs.C02OperatorSmoothInverse

/-! The sum with the standard complex structure has a genuine uniformly
bounded inverse under the fixed zeroth-order closeness bound. -/

noncomputable section
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ}

theorem complex_sum_isInvertible_and_inverse_norm
    (J : ComplexVector n →L[ℝ] ComplexVector n)
    (hJ : ‖J - complexStructureCLM n‖ ≤ 1 / 4) :
    (J + complexStructureCLM n).IsInvertible ∧ ‖(J + complexStructureCLM n).inverse‖ ≤ 1 := by
  let I := complexStructureCLM n
  let A : ComplexVector n →L[ℝ] ComplexVector n := (-1 / 2 : ℝ) • I
  let V : ComplexVector n →L[ℝ] ComplexVector n := (2 : ℝ) • I
  let S := J + I
  let Q := A.comp S
  have hI (z : ComplexVector n) : I (I z) = -z := by
    change Complex.I • (Complex.I • z) = -z
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have hAV : A.comp V = ContinuousLinearMap.id ℝ (ComplexVector n) := by
    apply ContinuousLinearMap.ext
    intro z
    change (-1 / 2 : ℝ) • I ((2 : ℝ) • I z) = z
    rw [map_smul, hI]
    module
  have hVA : V.comp A = ContinuousLinearMap.id ℝ (ComplexVector n) := by
    apply ContinuousLinearMap.ext
    intro z
    change (2 : ℝ) • I ((-1 / 2 : ℝ) • I z) = z
    rw [map_smul, hI]
    module
  have hA : ‖A‖ ≤ 1 / 2 := by
    calc
      ‖A‖ = (1 / 2 : ℝ) * ‖I‖ := by
        simp only [A, norm_smul, Real.norm_eq_abs]
        norm_num
      _ ≤ (1 / 2 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (complexStructureCLM_norm_le_one n) (by norm_num)
      _ = 1 / 2 := by ring
  have hEq : Q - ContinuousLinearMap.id ℝ (ComplexVector n) = A.comp (J - I) := by
    apply ContinuousLinearMap.ext
    intro z
    change (-1 / 2 : ℝ) • I (J z + I z) - z = (-1 / 2 : ℝ) • I (J z - I z)
    rw [map_add, map_sub, hI]
    module
  have hQclose : ‖Q - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ 1 / 4 := by
    rw [hEq]
    exact (A.opNorm_comp_le _).trans (by nlinarith [norm_nonneg (J - I)])
  have hQ := isInvertible_of_close_identity Q hQclose
  have hV := ContinuousLinearMap.IsInvertible.of_inverse hVA hAV
  have hS : S = V.comp Q := by
    dsimp only [Q]
    rw [← ContinuousLinearMap.comp_assoc, hVA, ContinuousLinearMap.id_comp]
  have hSinv : S.IsInvertible := by rw [hS]; exact hV.comp hQ
  refine ⟨hSinv, ?_⟩
  have hVi : V.inverse = A := ContinuousLinearMap.inverse_eq hVA hAV
  rw [show J + complexStructureCLM n = S from rfl, hS, hV.inverse_comp_of_left, hVi]
  exact (Q.inverse.opNorm_comp_le A).trans
    (by nlinarith [norm_actual_inverse_of_close_identity Q hQclose, norm_nonneg Q.inverse, norm_nonneg A])

end Yau.Blueprint.C02Proof
