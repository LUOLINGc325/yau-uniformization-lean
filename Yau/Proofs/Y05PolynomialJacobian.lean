import Yau.Proofs.Y05Jacobian
import Yau.Proofs.Y01DirectionalCoefficients
import Yau.Proofs.Y02JacobianComposition

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment MvPolynomial
open scoped ContDiff

variable {n : ℕ}

/-- The formal polynomial Jacobian evaluates to the determinant of the
actual complex Fréchet derivative. -/
theorem scalarEval_jacDet (P : PolyMap n) (z : ComplexVector n) :
    scalarEval P.jacDet z = LinearMap.det (fderiv ℂ P.eval z).toLinearMap := by
  have hPd : DifferentiableAt ℂ P.eval z :=
    (Yau.Proofs.Y01Aux.polyMap_eval_contDiff P).differentiable (by simp) z
  have hentry (i j : Fin n) : scalarEval (pderiv j (P i)) z =
      jacobianMatrix (fderiv ℂ P.eval z) i j := by
    let L : ComplexVector n →L[ℂ] ℂ := EuclideanSpace.proj i
    have hcomp := L.hasFDerivAt.comp z hPd.hasFDerivAt
    have hfd : fderiv ℂ (Yau.Proofs.Y01Aux.polyEval (P i)) z =
        L.comp (fderiv ℂ P.eval z) := by
      convert! hcomp.fderiv using 1
    have H := congrArg (fun D : ComplexVector n →L[ℂ] ℂ => D (stdVec j)) hfd
    rw [Yau.Proofs.Y01Aux.fderiv_polyEval_stdVec] at H
    simpa only [L, jacobianMatrix, ContinuousLinearMap.comp_apply,
      Yau.Proofs.Y01Aux.coordinate_proj_apply, scalarEval, Yau.Proofs.Y01Aux.polyEval] using H
  let e : MvPolynomial (Fin n) ℂ →+* ℂ := MvPolynomial.eval (fun i => z i)
  have he : (Yau.Proofs.Y02Aux.jacobianMatrix P).map e =
      jacobianMatrix (fderiv ℂ P.eval z) := by
    apply Matrix.ext
    intro i j
    exact hentry i j
  change e (Yau.Proofs.Y02Aux.jacobianMatrix P).det = _
  exact (e.map_det _).trans ((congrArg Matrix.det he).trans (jacobianMatrix_det _))

end Yau.Proofs.Y05Aux
