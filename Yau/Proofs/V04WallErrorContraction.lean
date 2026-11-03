import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! The finite-index cancellations in the inverse-metric symplectic
identity. These are polynomial identities, valid for every finite index
type, including the empty one. -/

set_option maxHeartbeats 2000000

open scoped Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def crossPermutation :
    (ι × ι × ι × ι × ι × ι) ≃ (ι × ι × ι × ι × ι × ι) where
  toFun := fun ⟨i, j, p, q, r, s⟩ => (r, j, i, s, p, q)
  invFun := fun ⟨i, j, p, q, r, s⟩ => (p, j, r, s, i, q)
  left_inv := by rintro ⟨i, j, p, q, r, s⟩; rfl
  right_inv := by rintro ⟨i, j, p, q, r, s⟩; rfl

private def jacobiPermutation :
    (ι × ι × ι × ι × ι × ι) ≃ (ι × ι × ι × ι × ι × ι) where
  toFun := fun ⟨i, j, p, q, r, s⟩ => (p, s, i, q, r, j)
  invFun := fun ⟨i, j, p, q, r, s⟩ => (p, s, i, q, r, j)
  left_inv := by rintro ⟨i, j, p, q, r, s⟩; rfl
  right_inv := by rintro ⟨i, j, p, q, r, s⟩; rfl

theorem matrix_five_mul_apply (A B C D E : Matrix ι ι ℂ) (l k : ι) :
    (A * B * C * D * E) l k =
      ∑ p, ∑ q, ∑ r, ∑ s, A l p * B p q * C q r * D r s * E s k := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Finset.mul_sum, mul_assoc]

theorem matrix_three_mul_apply (A B C : Matrix ι ι ℂ) (l k : ι) :
    (A * B * C) l k = ∑ p, ∑ q, A l p * B p q * C q k := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Finset.mul_sum, mul_assoc]

theorem inverse_hessian_cross_cancel
    (U : Matrix ι ι ℂ) (D B : ι → Matrix ι ι ℂ)
    (hB : ∀ i p q, B i p q = B p i q) (l k : ι) :
    (∑ i, ∑ j, U j i * (U * D j * U * B i * U) l k) =
      ∑ i, ∑ j, (U * B i * U) j k * (U * D j * U) l i := by
  let f : (ι × ι × ι × ι × ι × ι) → ℂ := fun ⟨i, j, p, q, r, s⟩ =>
    U j i * U l p * D j p q * U q r * B i r s * U s k
  let g : (ι × ι × ι × ι × ι × ι) → ℂ := fun ⟨i, j, p, q, r, s⟩ =>
    U j p * B i p q * U q k * U l r * D j r s * U s i
  have hp := Fintype.sum_equiv (crossPermutation (ι := ι)) f g (by
    rintro ⟨i, j, p, q, r, s⟩
    dsimp [f, g, crossPermutation]
    rw [hB r i s]
    ring)
  have hleft : (∑ i, ∑ j, U j i * (U * D j * U * B i * U) l k) = ∑ a, f a := by
    simp only [f, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [matrix_five_mul_apply U (D j) U (B i) U l k]
    simp only [Finset.mul_sum, mul_assoc]
  have hright : (∑ i, ∑ j, (U * B i * U) j k * (U * D j * U) l i) = ∑ a, g a := by
    simp only [g, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [matrix_three_mul_apply U (B i) U j k]
    simp only [Finset.sum_mul]
    simp_rw [matrix_three_mul_apply U (D j) U l i]
    simp only [Finset.mul_sum, mul_assoc]
  exact hleft.trans (hp.trans hright.symm)

/-- The second quadratic inverse term is precisely the quadratic Jacobi
term after the two Kähler symmetries are applied. -/
theorem inverse_hessian_jacobi_quadratic
    (U : Matrix ι ι ℂ) (D B : ι → Matrix ι ι ℂ)
    (hD : ∀ j p q, D j p q = D q p j)
    (hB : ∀ i p q, B i p q = B p i q) (l k : ι) :
    (∑ i, ∑ j, U j i * (U * B i * U * D j * U) l k) =
      ∑ p, ∑ s, U l p *
        (∑ i, ∑ j, ∑ a, ∑ b, U j a * D s a b * U b i * B p i j) * U s k := by
  let f : (ι × ι × ι × ι × ι × ι) → ℂ := fun ⟨i, j, p, q, r, s⟩ =>
    U j i * U l p * B i p q * U q r * D j r s * U s k
  let g : (ι × ι × ι × ι × ι × ι) → ℂ := fun ⟨p, s, i, j, a, b⟩ =>
    U l p * U j a * D s a b * U b i * B p i j * U s k
  have hp := Fintype.sum_equiv (jacobiPermutation (ι := ι)) f g (by
    rintro ⟨i, j, p, q, r, s⟩
    dsimp [f, g, jacobiPermutation]
    rw [hB i p q, hD j r s]
    ring)
  have hleft : (∑ i, ∑ j, U j i * (U * B i * U * D j * U) l k) = ∑ a, f a := by
    simp only [f, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [matrix_five_mul_apply U (B i) U (D j) U l k]
    simp only [Finset.mul_sum, mul_assoc]
  have hright : (∑ p, ∑ s, U l p *
      (∑ i, ∑ j, ∑ a, ∑ b, U j a * D s a b * U b i * B p i j) * U s k) = ∑ a, g a := by
    simp only [g, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro s _
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact hleft.trans (hp.trans hright.symm)

end Yau.Blueprint.V04Proof.WallErrorAux
