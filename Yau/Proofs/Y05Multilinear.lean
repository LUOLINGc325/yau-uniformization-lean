import Yau.Blueprint.Alignment
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Algebra.MvPolynomial.Degrees

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment MvPolynomial
open scoped BigOperators

variable {n m : ℕ}

theorem sum_standard_vectors (z : ComplexVector n) : ∑ i, z i • stdVec i = z := by
  ext j
  simp [stdVec, Pi.single_apply]

/-- The diagonal of an actual multilinear form, written in the fixed coordinates. -/
def diagonalPolynomial (A : (ComplexVector n) [×m]→L[ℂ] ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ I : Fin m → Fin n,
    C (A (fun j => stdVec (I j))) * ∏ j : Fin m, X (I j)

theorem scalarEval_diagonalPolynomial
    (A : (ComplexVector n) [×m]→L[ℂ] ℂ) (z : ComplexVector n) :
    scalarEval (diagonalPolynomial A) z = A (fun _ => z) := by
  classical
  simp only [diagonalPolynomial, scalarEval, map_sum, map_mul, map_prod, eval_C, eval_X]
  have H := A.toMultilinearMap.map_sum (fun (_j : Fin m) (i : Fin n) => z i • stdVec i)
  simp only [sum_standard_vectors] at H
  change A (fun _ => z) = ∑ I : Fin m → Fin n, A (fun j => z (I j) • stdVec (I j)) at H
  rw [H]
  apply Finset.sum_congr rfl
  intro I _
  rw [A.map_smul_univ]
  simp only [smul_eq_mul]
  ring

theorem diagonalPolynomial_degree
    (A : (ComplexVector n) [×m]→L[ℂ] ℂ) :
    (diagonalPolynomial A).totalDegree ≤ m := by
  classical
  apply totalDegree_finsetSum_le
  intro I _
  apply (totalDegree_mul _ _).trans
  have hprod : (∏ j : Fin m, (X (I j) : MvPolynomial (Fin n) ℂ)).totalDegree ≤ m := by
    simpa using
      (totalDegree_finsetProd (Finset.univ : Finset (Fin m))
        (fun j => (X (I j) : MvPolynomial (Fin n) ℂ)))
  simpa only [totalDegree_C, zero_add] using hprod

end Yau.Proofs.Y05Aux
