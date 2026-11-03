import Yau.Proofs.C02CurvatureCompact
import Yau.Proofs.C02CurvatureRealPart
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! A fixed finite-dimensional linear map takes complex curvature
coefficients to their physical real orthonormal components. Its norm is a
dimension constant, chosen before every geometric field. -/

noncomputable section
open scoped Matrix Matrix.Norms.Elementwise
namespace Yau.Blueprint.C02Proof
variable {n : ℕ}
local instance coefficient_array_group : NormedAddCommGroup (CurvatureArray n) := inferInstance
local instance coefficient_array_space : NormedSpace ℝ (CurvatureArray n) := inferInstance
local instance coefficient_vector_group : NormedAddCommGroup (EuclideanSpace ℝ (Fin 4 → RIdx n)) := inferInstance
local instance coefficient_vector_space : NormedSpace ℝ (EuclideanSpace ℝ (Fin 4 → RIdx n)) := inferInstance

theorem curvatureEvaluation_real_smul (C : CurvatureArray n) (r : ℝ)
    (u v w z : Fin n → ℂ) :
    curvatureEvaluation (r • C) u v w z = r • curvatureEvaluation C u v w z := by
  simp only [curvatureEvaluation, Pi.smul_apply, Matrix.smul_apply, Finset.smul_sum,
    smul_mul_assoc]

theorem realCurvatureEvaluation_add (C D : CurvatureArray n) (u v w z : Fin n → ℂ) :
    realCurvatureEvaluation (C + D) u v w z =
      realCurvatureEvaluation C u v w z + realCurvatureEvaluation D u v w z := by
  simp only [realCurvatureEvaluation, curvatureEvaluation_add, Complex.sub_re, Complex.add_re]
  ring

theorem realCurvatureEvaluation_real_smul (C : CurvatureArray n) (r : ℝ)
    (u v w z : Fin n → ℂ) :
    realCurvatureEvaluation (r • C) u v w z = r * realCurvatureEvaluation C u v w z := by
  simp only [realCurvatureEvaluation, curvatureEvaluation_real_smul, Complex.sub_re, Complex.smul_re]
  ring

def realCurvatureCoefficientLinear (n : ℕ) :
    CurvatureArray n →ₗ[ℝ] EuclideanSpace ℝ (Fin 4 → RIdx n) where
  toFun C := WithLp.toLp 2 (fun I => (1 / 4 : ℝ) * realCurvatureEvaluation C
    (WithLp.ofLp (realVec (I 0))) (WithLp.ofLp (realVec (I 1)))
    (WithLp.ofLp (realVec (I 2))) (WithLp.ofLp (realVec (I 3))))
  map_add' C D := by
    ext I
    change (1 / 4 : ℝ) * realCurvatureEvaluation (C + D) _ _ _ _ = _
    rw [realCurvatureEvaluation_add]
    change (1 / 4 : ℝ) * (_ + _) = (1 / 4 : ℝ) * _ + (1 / 4 : ℝ) * _
    ring
  map_smul' r C := by
    ext I
    change (1 / 4 : ℝ) * realCurvatureEvaluation (r • C) _ _ _ _ =
      r * ((1 / 4 : ℝ) * realCurvatureEvaluation C _ _ _ _)
    rw [realCurvatureEvaluation_real_smul]
    ring

def realCurvatureCoefficientOperator (n : ℕ) :
    CurvatureArray n →L[ℝ] EuclideanSpace ℝ (Fin 4 → RIdx n) := by
  let e : CurvatureArray n ≃ₗ[ℝ] (Fin n → Fin n → Fin n → Fin n → ℂ) :=
    { toFun := fun C i j k l => C i j k l
      invFun := fun C i j k l => C i j k l
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  letI : FiniteDimensional ℝ (CurvatureArray n) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  exact (realCurvatureCoefficientLinear n).toContinuousLinearMap

theorem exists_realCurvatureCoefficient_norm_bound (n : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : CurvatureArray n,
      ‖realCurvatureCoefficientLinear n C‖ ≤ A * ‖C‖ := by
  exact (realCurvatureCoefficientOperator n).bound

end Yau.Blueprint.C02Proof
