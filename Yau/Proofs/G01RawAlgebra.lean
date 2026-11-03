import Yau.Proofs.G01Realification

noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.G01Aux
open Yau
variable {n : ℕ}

theorem rawReal_add (A B : Matrix (Fin n) (Fin n) ℂ) :
    rawReal (A + B) = rawReal A + rawReal B := by
  ext a b
  simp only [rawReal, Matrix.add_apply, Complex.add_re, Complex.add_im]
  split_ifs <;> ring

theorem rawReal_neg (A : Matrix (Fin n) (Fin n) ℂ) :
    rawReal (-A) = -rawReal A := by
  ext a b
  simp only [rawReal, Matrix.neg_apply, Complex.neg_re, Complex.neg_im]
  split_ifs <;> ring

theorem rawReal_sub (A B : Matrix (Fin n) (Fin n) ℂ) :
    rawReal (A - B) = rawReal A - rawReal B := by
  rw [sub_eq_add_neg, rawReal_add, rawReal_neg, sub_eq_add_neg]

theorem rawReal_real_smul (c : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    rawReal ((c : ℂ) • A) = c • rawReal A := by
  ext a b
  simp only [rawReal, Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  split_ifs <;> ring

theorem rawReal_conjTranspose (A : Matrix (Fin n) (Fin n) ℂ) :
    rawReal Aᴴ = (rawReal A)ᵀ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [rawReal, Matrix.conjTranspose_apply, Matrix.transpose_apply]

theorem rawReal_zero : rawReal (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  ext a b
  simp [rawReal]

theorem rawReal_sum {ι : Type*} (s : Finset ι)
    (A : ι → Matrix (Fin n) (Fin n) ℂ) :
    rawReal (∑ i ∈ s, A i) = ∑ i ∈ s, rawReal (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rawReal_zero]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, rawReal_add, ih]

end Yau.NodeProofs.G01Aux
