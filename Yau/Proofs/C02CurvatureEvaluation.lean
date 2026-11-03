import Yau.Proofs.C02CurvaturePositivity

/-! Complex tensor evaluation and the simultaneous Hermitian projection.
This finite algebra does not assume that a tensor has a geometric realization. -/

noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.Blueprint.C02Proof
variable {n : ℕ}

def curvatureEvaluation (C : CurvatureArray n) (a b c d : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, C i j k l * star (a i) * b j * star (c k) * d l

def curvatureAdjoint (C : CurvatureArray n) : CurvatureArray n :=
  fun i j k l => star (C j i l k)

def curvatureHermitianPart (C : CurvatureArray n) : CurvatureArray n :=
  (1 / 2 : ℂ) • (C + curvatureAdjoint C)

theorem curvatureEvaluation_add (C D : CurvatureArray n) (a b c d : Fin n → ℂ) :
    curvatureEvaluation (C + D) a b c d =
      curvatureEvaluation C a b c d + curvatureEvaluation D a b c d := by
  simp only [curvatureEvaluation, Pi.add_apply, Matrix.add_apply, add_mul,
    Finset.sum_add_distrib]

theorem curvatureEvaluation_smul (r : ℂ) (C : CurvatureArray n) (a b c d : Fin n → ℂ) :
    curvatureEvaluation (r • C) a b c d = r * curvatureEvaluation C a b c d := by
  simp only [curvatureEvaluation, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

theorem curvatureEvaluation_adjoint (C : CurvatureArray n) (a b c d : Fin n → ℂ) :
    curvatureEvaluation (curvatureAdjoint C) a b c d =
      star (curvatureEvaluation C b a d c) := by
  simp only [curvatureEvaluation, curvatureAdjoint, star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
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

theorem curvatureHermitianPart_symmetry (C : CurvatureArray n) (i j k l : Fin n) :
    star (curvatureHermitianPart C j i l k) = curvatureHermitianPart C i j k l := by
  simp only [curvatureHermitianPart, curvatureAdjoint, Pi.smul_apply, Matrix.smul_apply,
    smul_eq_mul, Pi.add_apply, Matrix.add_apply, star_mul, star_add, star_star]
  norm_num
  ring

theorem curvatureEvaluation_eq_quadratic (C : CurvatureArray n) (v w : Fin n → ℂ) :
    curvatureEvaluation C w w v v = star w ⬝ᵥ (curvaturePartial C v *ᵥ w) := by
  simp only [curvatureEvaluation, curvaturePartial, dotProduct, Matrix.mulVec, Pi.star_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem curvatureEvaluation_hermitianPart_re (C : CurvatureArray n) (v w : Fin n → ℂ) :
    (curvatureEvaluation (curvatureHermitianPart C) w w v v).re =
      (curvatureEvaluation C w w v v).re := by
  rw [curvatureHermitianPart, curvatureEvaluation_smul, curvatureEvaluation_add,
    curvatureEvaluation_adjoint]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  norm_num
  ring

theorem curvatureHermitianPart_positive (C : CurvatureArray n)
    (hC : ∀ v w : Fin n → ℂ, 0 ≤ (curvatureEvaluation C w w v v).re) :
    CurvaturePositive (curvatureHermitianPart C) := by
  refine ⟨curvatureHermitianPart_symmetry C, ?_⟩
  intro v w
  rw [← curvatureEvaluation_eq_quadratic, curvatureEvaluation_hermitianPart_re]
  exact hC v w

end Yau.Blueprint.C02Proof
