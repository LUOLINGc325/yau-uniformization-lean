import Yau.Proofs.V03CauchyBinet

/-! The division-free Cramer identity for all row and column tuples.
Repeated indices and zero minors are included in the same polynomial identity. -/

open scoped Matrix ComplexOrder
open Finset

noncomputable section
namespace Yau.Blueprint.V02Proof

variable {ι κ β : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β]

/-- Push a coefficient vector along an arbitrary column tuple. -/
def tuplePush (c : ι → β) (v : ι → ℂ) : β → ℂ :=
  fun k => ∑ i, if c i = k then v i else 0

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem mulVec_tuplePush (A : Matrix κ β ℂ) (c : ι → β) (v : ι → ℂ) :
    A *ᵥ tuplePush c v = A.submatrix id c *ᵥ v := by
  ext j
  simp only [Matrix.mulVec, dotProduct, tuplePush, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp [mul_ite, Matrix.submatrix_apply]

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β] in
/-- The selected minor factors through the actual tangent dimension. -/
theorem product_tuple_minor (J : Matrix κ ι ℂ) (T : Matrix ι β ℂ)
    (r : ι → κ) (c : ι → β) :
    (J * T).submatrix r c = J.submatrix r id * T.submatrix id c := by
  ext i j
  rfl

/-- No inverse or nonzero determinant is used. -/
theorem product_adjugate_cramer (P Q : Matrix ι ι ℂ) :
    Q * (P * Q).adjugate * P = (P * Q).det • (1 : Matrix ι ι ℂ) := by
  rw [Matrix.adjugate_mul_distrib, ← Matrix.mul_assoc,
    Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul,
    Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, Matrix.det_mul]
  congr 1
  exact mul_comm _ _

/-- The coefficient of an individual minor, defined for every tuple. -/
def tupleCramer (A : Matrix κ β ℂ) (r : ι → κ) (c : ι → β)
    (Y : κ → ℂ) : β → ℂ :=
  tuplePush c ((A.submatrix r c).adjugate *ᵥ (Y ∘ r))

theorem mulVec_tupleCramer (J : Matrix κ ι ℂ) (T : Matrix ι β ℂ)
    (r : ι → κ) (c : ι → β) (v : ι → ℂ) :
    (J * T) *ᵥ tupleCramer (J * T) r c (J *ᵥ v) =
      ((J * T).submatrix r c).det • (J *ᵥ v) := by
  have hJ : (J *ᵥ v) ∘ r = J.submatrix r id *ᵥ v := by
    ext i
    rfl
  have hA : (J * T).submatrix id c = J * T.submatrix id c := by
    ext i j
    rfl
  rw [tupleCramer, mulVec_tuplePush, hJ, hA, product_tuple_minor]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc J, Matrix.mul_assoc J,
    product_adjugate_cramer, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mulVec]
/-- Sum over every pair of row and column tuples; the empty dimension is allowed. -/
def tupleMinorSq (J : Matrix κ ι ℂ) (T : Matrix ι β ℂ) : ℝ :=
  ∑ r : ι → κ, ∑ c : ι → β, ‖((J * T).submatrix r c).det‖ ^ 2

theorem tupleMinorSq_factor (J : Matrix κ ι ℂ) (T : Matrix ι β ℂ) :
    tupleMinorSq J T =
      (∑ r : ι → κ, ‖(J.submatrix r id).det‖ ^ 2) *
        ∑ c : ι → β, ‖(T.submatrix id c).det‖ ^ 2 := by
  simp only [tupleMinorSq, product_tuple_minor, Matrix.det_mul, norm_mul, mul_pow,
    sum_mul, mul_sum]
  rw [sum_comm]

theorem tupleMinorSq_eq_gram_product (J : Matrix κ ι ℂ) (T : Matrix ι β ℂ) :
    tupleMinorSq J T = (Fintype.card (Equiv.Perm ι) : ℝ) ^ 2 *
      (Jᴴ * J).det.re * (T * Tᴴ).det.re := by
  have hc : (Fintype.card (Equiv.Perm ι) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm ι) ≠ 0)
  have hJ := V03Proof.gram_det_re_eq_sum_tuple_minors J
  have hT := V03Proof.gram_det_re_eq_sum_tuple_minors Tᴴ
  have hm (c : ι → β) : ‖(Tᴴ.submatrix c id).det‖ ^ 2 =
      ‖(T.submatrix id c).det‖ ^ 2 := by
    have he : Tᴴ.submatrix c id = (T.submatrix id c)ᴴ := rfl
    rw [he, Matrix.det_conjTranspose, norm_star]
  simp only [Matrix.conjTranspose_conjTranspose, hm] at hT
  rw [tupleMinorSq_factor]
  rw [hJ, hT]
  field_simp

theorem tupleMinorSq_pos (J : Matrix κ ι ℂ) (T : Matrix ι β ℂ)
    (hJ : (Jᴴ * J).PosDef) (hT : (T * Tᴴ).PosDef) :
    0 < tupleMinorSq J T := by
  rw [tupleMinorSq_eq_gram_product]
  have hc : 0 < (Fintype.card (Equiv.Perm ι) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm ι))
  exact mul_pos (mul_pos (sq_pos_of_pos hc) (Complex.pos_iff.mp hJ.det_pos).1)
    (Complex.pos_iff.mp hT.det_pos).1

end Yau.Blueprint.V02Proof
