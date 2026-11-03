import Yau.Proofs.Y06LayerPerturbation
import Yau.Proofs.Y06ProjectionNorm
import Yau.Proofs.Y06AllowedProjection

/-! The actual affine backward step solves the complete homogeneous layer
equation after the complementary allowed part is restored. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n m : ℕ}

theorem diagonal_inverse_eq (a : Fin n → ℂ) (ha : ∀ i, a i ≠ 0) :
    (Matrix.diagonal a)⁻¹ = Matrix.diagonal (fun i => (a i)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact inv_mul_cancel₀ (ha i)

theorem diagonal_linear_comp_coeff (a : Fin n → ℂ) (P : PolyMap n)
    (i : Fin n) (β : Fin n →₀ ℕ) :
    ((linearPolynomial (Matrix.diagonal a)).comp P i).coeff β = a i * (P i).coeff β := by
  classical
  have heq : (linearPolynomial (Matrix.diagonal a)).comp P i = C (a i) * P i := by
    change (linearPoly (Matrix.diagonal a)).comp P i = _
    rw [linearPoly_comp_apply]
    simp [Matrix.diagonal_apply, apply_ite]
  rw [heq, coeff_C_mul]

theorem diagonal_projection_cancel (a : Fin n → ℂ) (ha : ∀ i, a i ≠ 0)
    (w : Fin n → ℝ) (P : PolyMap n) :
    (linearPolynomial (Matrix.diagonal a)).comp
        (forbiddenProjection w ((linearPolynomial (Matrix.diagonal (fun i => (a i)⁻¹))).comp P)) =
      forbiddenProjection w P := by
  classical
  funext i
  ext β
  rw [diagonal_linear_comp_coeff, forbiddenProjection_coeff, forbiddenProjection_coeff,
    diagonal_linear_comp_coeff]
  split_ifs
  · rw [← mul_assoc, mul_inv_cancel₀ (ha i), one_mul]
  · rw [mul_zero]

def backwardAffineStep (D J : Herm n) (w : Fin n → ℝ) (B X : PolyMap n) : PolyMap n :=
  backwardOperator D J w X + forbiddenProjection w ((linearPolynomial D⁻¹).comp B)

theorem backwardAffineStep_homogeneous (D J : Herm n) (w : Fin n → ℝ)
    {B X : PolyMap n} (hB : Homogeneous B m) (hX : Homogeneous X m) :
    Homogeneous (backwardAffineStep D J w B X) m :=
  homogeneous_add (backwardOperator_homogeneous D J w hX)
    (forbiddenProjection_homogeneous w (homogeneous_linear_comp hB D⁻¹))

theorem backwardAffineStep_forbidden (D J : Herm n) (w : Fin n → ℝ) (B X : PolyMap n) :
    forbiddenProjection w (backwardAffineStep D J w B X) = backwardAffineStep D J w B X := by
  unfold backwardAffineStep backwardOperator
  rw [forbiddenProjection_add, forbiddenProjection_idempotent, forbiddenProjection_idempotent]

theorem backwardAffineStep_layer_equation (a : Fin n → ℂ) (ha : ∀ i, a i ≠ 0)
    (J : Herm n) (w : Fin n → ℝ) (B X : PolyMap n) :
    let Z := (linearPolynomial J⁻¹).comp (X.comp (linearPolynomial (J * Matrix.diagonal a))) + B
    (linearPolynomial (Matrix.diagonal a)).comp (backwardAffineStep (Matrix.diagonal a) J w B X) +
      allowedProjection w Z = Z := by
  let Z := (linearPolynomial J⁻¹).comp (X.comp (linearPolynomial (J * Matrix.diagonal a))) + B
  have heq : backwardAffineStep (Matrix.diagonal a) J w B X =
      forbiddenProjection w ((linearPolynomial (Matrix.diagonal a)⁻¹).comp Z) := by
    unfold backwardAffineStep backwardOperator
    rw [linearPolynomial_comp_add, forbiddenProjection_add]
  change (linearPolynomial (Matrix.diagonal a)).comp (backwardAffineStep (Matrix.diagonal a) J w B X) +
    allowedProjection w Z = Z
  rw [heq, diagonal_inverse_eq a ha, diagonal_projection_cancel a ha, add_comm]
  exact allowed_forbidden_sum w Z

theorem backwardAffineStep_coeffNorm_bound (D J : Herm n) (w : Fin n → ℝ) (B X : PolyMap n)
    {a F : ℝ} (hT : (backwardOperator D J w X).coeffNorm ≤ a * X.coeffNorm)
    (hF : (forbiddenProjection w ((linearPolynomial D⁻¹).comp B)).coeffNorm ≤ F) :
    (backwardAffineStep D J w B X).coeffNorm ≤ a * X.coeffNorm + F :=
  (coeffNorm_add_le _ _).trans (add_le_add hT hF)

end Yau.Proofs.Y06Aux
