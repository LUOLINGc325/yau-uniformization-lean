import Yau.Proofs.V04WallErrorContraction

/-! The full contracted inverse-Hessian identity, using the same Jacobi
matrix that defines the Ricci form in the local calculation. -/

set_option maxHeartbeats 2000000
open scoped Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def tracePermutation : (ι × ι × ι × ι) ≃ (ι × ι × ι × ι) where
  toFun := fun ⟨j, a, b, i⟩ => (i, j, a, b)
  invFun := fun ⟨i, j, a, b⟩ => (j, a, b, i)
  left_inv := by rintro ⟨i, j, a, b⟩; rfl
  right_inv := by rintro ⟨i, j, a, b⟩; rfl

private def secondPermutation : (ι × ι × ι × ι) ≃ (ι × ι × ι × ι) where
  toFun := fun ⟨i, j, p, q⟩ => (p, q, i, j)
  invFun := fun ⟨i, j, p, q⟩ => (p, q, i, j)
  left_inv := by rintro ⟨i, j, p, q⟩; rfl
  right_inv := by rintro ⟨i, j, p, q⟩; rfl

theorem trace_four_product_jacobi (U D B : Matrix ι ι ℂ) :
    Matrix.trace (U * D * U * B) =
      ∑ i, ∑ j, ∑ a, ∑ b, U j a * D a b * U b i * B i j := by
  let f : (ι × ι × ι × ι) → ℂ := fun ⟨j, a, b, i⟩ => U j a * D a b * U b i * B i j
  let g : (ι × ι × ι × ι) → ℂ := fun ⟨i, j, a, b⟩ => U j a * D a b * U b i * B i j
  have hp := Fintype.sum_equiv (tracePermutation (ι := ι)) f g (by
    rintro ⟨j, a, b, i⟩; rfl)
  simpa only [f, g, Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_assoc, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc] using hp

theorem trace_two_product_jacobi (U S : Matrix ι ι ℂ) :
    Matrix.trace (U * S) = ∑ i, ∑ j, U j i * S i j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]

theorem inverse_hessian_jacobi_second
    (U : Matrix ι ι ℂ) (S : ι → ι → Matrix ι ι ℂ)
    (hS : ∀ i j p q, S i j p q = S p q i j) (l k : ι) :
    (∑ i, ∑ j, U j i * (U * S i j * U) l k) =
      ∑ p, ∑ q, U l p * (∑ i, ∑ j, U j i * S p q i j) * U q k := by
  let f : (ι × ι × ι × ι) → ℂ := fun ⟨i, j, p, q⟩ => U j i * U l p * S i j p q * U q k
  let g : (ι × ι × ι × ι) → ℂ := fun ⟨p, q, i, j⟩ => U l p * U j i * S p q i j * U q k
  have hp := Fintype.sum_equiv (secondPermutation (ι := ι)) f g (by
    rintro ⟨i, j, p, q⟩
    dsimp [f, g, secondPermutation]
    rw [hS i j p q]
    ring)
  have hleft : (∑ i, ∑ j, U j i * (U * S i j * U) l k) = ∑ x, f x := by
    simp only [f, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [matrix_three_mul_apply U (S i j) U l k]
    simp only [Finset.mul_sum, mul_assoc]
  have hright : (∑ p, ∑ q, U l p * (∑ i, ∑ j, U j i * S p q i j) * U q k) = ∑ x, g x := by
    simp only [g, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact hleft.trans (hp.trans hright.symm)

theorem contracted_inverse_hessian_identity
    (U : Matrix ι ι ℂ) (D B : ι → Matrix ι ι ℂ) (S : ι → ι → Matrix ι ι ℂ)
    (hD : ∀ j p q, D j p q = D q p j)
    (hB : ∀ i p q, B i p q = B p i q)
    (hS : ∀ i j p q, S i j p q = S p q i j) (l k : ι) :
    (∑ i, ∑ j, U j i *
      (U * D j * U * B i * U + U * B i * U * D j * U - U * S i j * U) l k) -
      (∑ i, ∑ j, (-U * B i * U) j k * (-U * D j * U) l i) =
      (U * Matrix.of (fun p s => Matrix.trace (U * D s * U * B p) - Matrix.trace (U * S p s)) * U) l k := by
  let Q : ℂ := ∑ p, ∑ s, U l p *
    (∑ i, ∑ j, ∑ a, ∑ b, U j a * D s a b * U b i * B p i j) * U s k
  let V : ℂ := ∑ p, ∑ s, U l p * (∑ i, ∑ j, U j i * S p s i j) * U s k
  have hR : (U * Matrix.of (fun p s => Matrix.trace (U * D s * U * B p) -
      Matrix.trace (U * S p s)) * U) l k = Q - V := by
    rw [matrix_three_mul_apply U (Matrix.of (fun p s =>
      Matrix.trace (U * D s * U * B p) - Matrix.trace (U * S p s))) U l k]
    simp only [Matrix.of_apply]
    simp_rw [trace_four_product_jacobi, trace_two_product_jacobi]
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.sum_mul, Q, V, mul_assoc]
  rw [hR]
  simp only [Matrix.add_apply, Matrix.sub_apply, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Matrix.neg_mul, Matrix.neg_apply, neg_mul_neg]
  rw [inverse_hessian_cross_cancel U D B hB l k,
    inverse_hessian_jacobi_quadratic U D B hD hB l k,
    inverse_hessian_jacobi_second U S hS l k]
  dsimp [Q, V]
  ring

end Yau.Blueprint.V04Proof.WallErrorAux
