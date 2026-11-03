import Yau.LeafProofs.L17ScalarEllipticity

/-! Multiplication and genuine inverses for the scalar realification. -/

noncomputable section

open scoped Matrix

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ}

theorem scalarRealification_mul (A B : Matrix (Fin n) (Fin n) ℂ) :
    scalarRealification (A * B) = scalarRealification A * scalarRealification B := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [scalarRealification, Matrix.mul_apply, Complex.mul_re, Complex.mul_im,
      Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
  all_goals ring

theorem scalarRealification_inverse (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUnit A.det) : scalarRealification A⁻¹ = (scalarRealification A)⁻¹ := by
  classical
  have hprod : scalarRealification A * scalarRealification A⁻¹ = 1 := by
    rw [← scalarRealification_mul, Matrix.mul_nonsing_inv _ hA, scalarRealification_one]
  have hdet : IsUnit (scalarRealification A).det := by
    apply isUnit_iff_ne_zero.mpr
    have hd := congrArg Matrix.det hprod
    rw [Matrix.det_mul, Matrix.det_one] at hd
    intro hz
    rw [hz, zero_mul] at hd
    exact zero_ne_one hd
  symm
  calc
    (scalarRealification A)⁻¹ = (scalarRealification A)⁻¹ *
        (scalarRealification A * scalarRealification A⁻¹) := by rw [hprod, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]

theorem twice_scalarRealification_inverse (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUnit A.det) :
    ((2 : ℝ) • scalarRealification A)⁻¹ =
      (1 / 2 : ℝ) • scalarRealification A⁻¹ := by
  classical
  let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hdet : (scalarRealification A).det ≠ 0 := by
    have hh : scalarRealification A * scalarRealification A⁻¹ = 1 := by
      rw [← scalarRealification_mul, Matrix.mul_nonsing_inv _ hA, scalarRealification_one]
    have hd := congrArg Matrix.det hh
    rw [Matrix.det_mul, Matrix.det_one] at hd
    intro hz
    rw [hz, zero_mul] at hd
    exact zero_ne_one hd
  rw [Matrix.inv_smul (A := scalarRealification A) (2 : ℝ) (isUnit_iff_ne_zero.mpr hdet),
    ← scalarRealification_inverse A hA]
  simp only [invOf_eq_inv, one_div]

end Yau.LeafProofs.L17Aux
