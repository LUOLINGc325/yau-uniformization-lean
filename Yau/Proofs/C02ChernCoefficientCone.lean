import Yau.Proofs.C02CurvatureBasisTransform

/-! The original nonnegative bisectional predicate supplies the finite
positive coefficient cone in every chosen complex basis. -/

noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

def actualChernArray (h : HermitianField M) (p : M.Carrier) : CurvatureArray n :=
  fun a b c d => chernCurvature h p b a d c

theorem actualChernArray_bisectional (h : HermitianField M) (p : M.Carrier)
    (v w : Fin n → ℂ) :
    (curvatureEvaluation (actualChernArray h p) w w v v).re =
      bisectionalForm h p (WithLp.toLp 2 w) (WithLp.toLp 2 v) := by
  change (∑ a, ∑ b, ∑ c, ∑ d,
      chernCurvature h p b a d c * star (w a) * w b * star (v c) * v d).re =
    (∑ a, ∑ b, ∑ c, ∑ d,
      chernCurvature h p a b c d * w a * star (w b) * v c * star (v d)).re
  apply congrArg Complex.re
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem actualChernArray_basis_positive (h : HermitianField M)
    (hBisec : NonnegBisectional h) (p : M.Carrier) (S : Matrix (Fin n) (Fin n) ℂ) :
    CurvaturePositive (curvatureHermitianPart (curvatureBasisTransform (actualChernArray h p) S)) := by
  apply curvatureBasisTransform_hermitianPart_positive
  intro v w
  rw [actualChernArray_bisectional]
  exact hBisec p _ _

end Yau.Blueprint.C02Proof
