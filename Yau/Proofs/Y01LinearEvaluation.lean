import Yau.Proofs.Y01PolynomialCalculus
import Yau.Proofs.Y01PrimaryAlgebra

/-! Polynomial linear parts are the genuine center Fréchet derivatives. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open MvPolynomial Yau.Blueprint Yau.Proofs.Y02Aux
open scoped ContDiff

variable {n : ℕ}

theorem linearPoly_eval (A : Herm n) (z : ComplexVector n) :
    (linearPoly A).eval z = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A z := by
  ext i
  change (eval fun j => z j) (linearPoly A i) =
    (WithLp.ofLp (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A z)) i
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [linearPoly, linearForm, Matrix.mulVec, dotProduct]

theorem fderiv_polyMap_eval (P : PolyMap n) :
    fderiv ℂ P.eval 0 = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P.linearPart := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  have hdiff : DifferentiableAt ℂ P.eval 0 :=
    (polyMap_eval_contDiff P).differentiable (by simp) 0
  have hcomp := ((EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).hasFDerivAt.comp 0 hdiff.hasFDerivAt).fderiv
  change fderiv ℂ (polyEval (P i)) 0 =
    (EuclideanSpace.proj i).comp (fderiv ℂ P.eval 0) at hcomp
  have hv := congrArg (fun L => L v) hcomp
  rw [fderiv_polyEval] at hv
  simp only [sum_apply, smul_apply, polyEval_zero, coeff_pderiv, zero_add,
    Finsupp.zero_apply, Nat.cast_zero, zero_add, mul_one, coordinate_proj_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul] at hv
  change ((fderiv ℂ P.eval 0) v) i =
    (WithLp.ofLp (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P.linearPart v)) i
  rw [Matrix.ofLp_toEuclideanCLM]
  exact hv.symm

end Yau.Proofs.Y01Aux
