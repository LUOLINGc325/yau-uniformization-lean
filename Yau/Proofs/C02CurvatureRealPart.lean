import Yau.Proofs.C02CurvatureEvaluation

/-! The Hermitian projection preserves the scalar trace and the real
curvature contraction whenever that contraction has its genuine last-pair
skew symmetry. This removes any need to posit an extra Chern symmetry. -/

noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.Blueprint.C02Proof
variable {n : ℕ}

theorem curvatureTrace_hermitianPart (C : CurvatureArray n) :
    curvatureTrace (curvatureHermitianPart C) = curvatureTrace C := by
  change Complex.reCLM (∑ k, ∑ i, curvatureHermitianPart C i i k k) =
    Complex.reCLM (∑ k, ∑ i, C i i k k)
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  change (curvatureHermitianPart C i i k k).re = (C i i k k).re
  simp only [curvatureHermitianPart, curvatureAdjoint, Pi.smul_apply, Matrix.smul_apply,
    smul_eq_mul, Pi.add_apply, Matrix.add_apply, Complex.mul_re, Complex.add_re,
    Complex.star_def, Complex.conj_re]
  norm_num
  ring

def realCurvatureEvaluation (C : CurvatureArray n) (U V W Z : Fin n → ℂ) : ℝ :=
  2 * (curvatureEvaluation C Z W V U - curvatureEvaluation C Z W U V).re

theorem realCurvatureEvaluation_adjoint (C : CurvatureArray n) (U V W Z : Fin n → ℂ) :
    realCurvatureEvaluation (curvatureAdjoint C) U V W Z =
      -realCurvatureEvaluation C U V Z W := by
  simp only [realCurvatureEvaluation, curvatureEvaluation_adjoint, Complex.sub_re,
    Complex.star_def, Complex.conj_re]
  ring

theorem realCurvatureEvaluation_hermitianPart_average
    (C : CurvatureArray n) (U V W Z : Fin n → ℂ) :
    realCurvatureEvaluation (curvatureHermitianPart C) U V W Z =
      (realCurvatureEvaluation C U V W Z +
        realCurvatureEvaluation (curvatureAdjoint C) U V W Z) / 2 := by
  simp only [realCurvatureEvaluation, curvatureHermitianPart, curvatureEvaluation_smul,
    curvatureEvaluation_add, Complex.mul_re, Complex.add_re, Complex.sub_re]
  norm_num
  ring

theorem realCurvatureEvaluation_hermitianPart
    (C : CurvatureArray n) (U V W Z : Fin n → ℂ)
    (hskew : realCurvatureEvaluation C U V Z W = -realCurvatureEvaluation C U V W Z) :
    realCurvatureEvaluation (curvatureHermitianPart C) U V W Z =
      realCurvatureEvaluation C U V W Z := by
  rw [realCurvatureEvaluation_hermitianPart_average, realCurvatureEvaluation_adjoint, hskew]
  ring

end Yau.Blueprint.C02Proof
