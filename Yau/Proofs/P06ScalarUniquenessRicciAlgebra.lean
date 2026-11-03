import Yau.Proofs.P06ScalarUniquenessAlgebra

/-! Finite dimensional positivity of the inverse metric curvature trace. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.P06Aux
open Yau
variable {n : ℕ}

theorem scalarUniqueness_sum_four_exchange (F : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, F i j k l := by
  calc
    _ = ∑ i, ∑ k, ∑ l, ∑ j, F i j k l := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm

def scalarUniqueness_curvatureDirection
    (R : Fin n → Fin n → Fin n → Fin n → ℂ) (v : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun a b => ∑ i, ∑ j, R i j b a * v i * star (v j)

theorem scalarUniqueness_curvatureDirection_hermitian
    (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hs : ∀ i j k l, star (R i j k l) = R j i l k) (v : Fin n → ℂ) :
    (scalarUniqueness_curvatureDirection R v).IsHermitian := by
  ext a b
  simp only [scalarUniqueness_curvatureDirection, Matrix.conjTranspose_apply,
    star_sum, star_mul, star_star, hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem scalarUniqueness_curvatureDirection_quadratic
    (R : Fin n → Fin n → Fin n → Fin n → ℂ) (v w : Fin n → ℂ) :
    star w ⬝ᵥ (scalarUniqueness_curvatureDirection R v *ᵥ w) =
      ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * v i * star (v j) * w k * star (w l) := by
  simp only [dotProduct, Matrix.mulVec, scalarUniqueness_curvatureDirection,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [scalarUniqueness_sum_four_exchange]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem scalarUniqueness_curvatureDirection_posSemidef
    (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hs : ∀ i j k l, star (R i j k l) = R j i l k)
    (hpos : ∀ v w : Fin n → ℂ,
      0 ≤ (∑ i, ∑ j, ∑ k, ∑ l, R i j k l * v i * star (v j) * w k * star (w l)).re)
    (v : Fin n → ℂ) :
    (scalarUniqueness_curvatureDirection R v).PosSemidef := by
  have hh := scalarUniqueness_curvatureDirection_hermitian R hs v
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro w
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hh.im_star_dotProduct_mulVec_self w).symm⟩
  rw [scalarUniqueness_curvatureDirection_quadratic]
  exact hpos v w

theorem scalarUniqueness_curvatureContraction_quadratic
    (H : Matrix (Fin n) (Fin n) ℂ)
    (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (v : Fin n → ℂ) :
    star v ⬝ᵥ ((fun a b => ∑ k, ∑ l, H⁻¹ k l * R b a k l) *ᵥ v) =
      Matrix.trace (H⁻¹ * scalarUniqueness_curvatureDirection R v) := by
  simp only [dotProduct, Matrix.mulVec, scalarUniqueness_curvatureDirection,
    Pi.star_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [scalarUniqueness_sum_four_exchange]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Yau.NodeProofs.P06Aux
