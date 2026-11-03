import Yau.Proofs.C02CurvatureRealPart

/-! Four-slot change of a complex curvature coefficient array. The same
matrix acts in every slot; the conjugate-linear slots retain their stars. -/

noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.Blueprint.C02Proof
variable {n : ℕ}

def curvatureBasisTransform (C : CurvatureArray n) (S : Matrix (Fin n) (Fin n) ℂ) :
    CurvatureArray n := fun i j k l =>
  ∑ a, ∑ b, ∑ c, ∑ d, C a b c d * star (S a i) * S b j * star (S c k) * S d l

theorem curvatureEvaluation_basisTransform (C : CurvatureArray n)
    (S : Matrix (Fin n) (Fin n) ℂ) (u v w z : Fin n → ℂ) :
    curvatureEvaluation (curvatureBasisTransform C S) u v w z =
      curvatureEvaluation C (S *ᵥ u) (S *ᵥ v) (S *ᵥ w) (S *ᵥ z) := by
  simp only [curvatureEvaluation, curvatureBasisTransform, Matrix.mulVec, dotProduct,
    star_sum, star_mul, Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    rw [Finset.sum_comm]
  conv_lhs =>
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    arg 2
    ext v3
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    arg 2
    ext v3
    arg 2
    ext v4
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    arg 2
    ext v3
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    arg 2
    ext v3
    arg 2
    ext v4
    arg 2
    ext v5
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    arg 2
    ext v3
    arg 2
    ext v4
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    arg 2
    ext v3
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    arg 2
    ext v3
    arg 2
    ext v4
    arg 2
    ext v5
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    arg 2
    ext v3
    arg 2
    ext v4
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    arg 2
    ext v3
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    arg 2
    ext v3
    arg 2
    ext v4
    arg 2
    ext v5
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    arg 2
    ext v3
    arg 2
    ext v4
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    arg 2
    ext v3
    arg 2
    ext v4
    arg 2
    ext v5
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a0 _
  apply Finset.sum_congr rfl
  intro a1 _
  apply Finset.sum_congr rfl
  intro a2 _
  apply Finset.sum_congr rfl
  intro a3 _
  apply Finset.sum_congr rfl
  intro a4 _
  apply Finset.sum_congr rfl
  intro a5 _
  apply Finset.sum_congr rfl
  intro a6 _
  apply Finset.sum_congr rfl
  intro a7 _
  ring

theorem curvatureBasisTransform_hermitianPart_positive (C : CurvatureArray n)
    (S : Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ v w, 0 ≤ (curvatureEvaluation C w w v v).re) :
    CurvaturePositive (curvatureHermitianPart (curvatureBasisTransform C S)) := by
  apply curvatureHermitianPart_positive
  intro v w
  rw [curvatureEvaluation_basisTransform]
  exact hC (S *ᵥ v) (S *ᵥ w)

theorem realCurvatureEvaluation_basisTransform (C : CurvatureArray n)
    (S : Matrix (Fin n) (Fin n) ℂ) (u v w z : Fin n → ℂ) :
    realCurvatureEvaluation (curvatureBasisTransform C S) u v w z =
      realCurvatureEvaluation C (S *ᵥ u) (S *ᵥ v) (S *ᵥ w) (S *ᵥ z) := by
  simp only [realCurvatureEvaluation, curvatureEvaluation_basisTransform]

end Yau.Blueprint.C02Proof
