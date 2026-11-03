import Yau.Proofs.Y01JetAlgebra

/-! Smooth evaluation and the genuine Fréchet derivative of multivariate polynomials. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open MvPolynomial
open scoped ContDiff

variable {n : ℕ}

def polyEval (p : MvPolynomial (Fin n) ℂ) (z : ComplexVector n) : ℂ :=
  MvPolynomial.eval (fun i => z i) p

@[simp] theorem polyEval_C (c : ℂ) : polyEval (C c : MvPolynomial (Fin n) ℂ) = fun _ => c := by
  funext z
  exact eval_C _

@[simp] theorem polyEval_add (p q : MvPolynomial (Fin n) ℂ) :
    polyEval (p + q) = polyEval p + polyEval q := by
  funext z
  exact map_add _ _ _

@[simp] theorem polyEval_mul (p q : MvPolynomial (Fin n) ℂ) :
    polyEval (p * q) = polyEval p * polyEval q := by
  funext z
  exact map_mul _ _ _

@[simp] theorem polyEval_X (j : Fin n) :
    polyEval (X j) = (EuclideanSpace.proj j : ComplexVector n →L[ℂ] ℂ) := by
  funext z
  exact eval_X _

@[simp] theorem coordinate_proj_apply (j : Fin n) (z : ComplexVector n) :
    (EuclideanSpace.proj j) z = z j := rfl

@[simp] theorem polyEval_zero_polynomial : polyEval (0 : MvPolynomial (Fin n) ℂ) = 0 := by
  funext z
  exact map_zero _

theorem polyEval_contDiff (p : MvPolynomial (Fin n) ℂ) : ContDiff ℂ ∞ (polyEval p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [polyEval_C] using (contDiff_const : ContDiff ℂ ∞ (fun _ : ComplexVector n => c))
  | add p q hp hq => simpa only [polyEval_add, Pi.add_def] using hp.add hq
  | mul_X p j hp =>
    simpa only [polyEval_mul, polyEval_X, Pi.mul_def] using hp.mul (EuclideanSpace.proj j).contDiff

theorem polyMap_eval_contDiff (P : PolyMap n) : ContDiff ℂ ∞ P.eval := by
  apply contDiff_euclidean.2
  intro i
  exact polyEval_contDiff (P i)

@[simp] theorem polyEval_zero (p : MvPolynomial (Fin n) ℂ) : polyEval p 0 = p.coeff 0 := by
  change MvPolynomial.eval (fun _ => 0) p = _
  rw [eval_zero']
  rfl

theorem hasFDerivAt_polyEval (p : MvPolynomial (Fin n) ℂ) (z : ComplexVector n) :
    HasFDerivAt (polyEval p)
      (∑ j, polyEval (pderiv j p) z • (EuclideanSpace.proj j : ComplexVector n →L[ℂ] ℂ)) z := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [polyEval_C]
    have hz : (∑ j, polyEval (pderiv j (C c)) z •
        (EuclideanSpace.proj j : ComplexVector n →L[ℂ] ℂ)) = 0 := by
      ext v
      simp [polyEval]
    rw [hz]
    exact hasFDerivAt_const c z
  | add p q hp hq =>
    rw [polyEval_add]
    apply (hp.add hq).congr_fderiv
    ext v
    simp [polyEval, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    have h := hp.mul (EuclideanSpace.proj j).hasFDerivAt
    rw [polyEval_mul, polyEval_X]
    apply h.congr_fderiv
    ext v
    simp only [pderiv_mul, map_add, polyEval_add, polyEval_mul, polyEval_X,
      Pi.add_apply, Pi.mul_apply, pderiv_X, Pi.single_apply, polyEval_C,
      sum_apply, smul_apply, smul_eq_mul, add_apply, coordinate_proj_apply,
      add_mul, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [apply_ite, ite_apply, polyEval_zero_polynomial, Pi.zero_apply, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [Finset.mul_sum]
    rw [add_comm (polyEval p z * v j)]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    ring

theorem fderiv_polyEval (p : MvPolynomial (Fin n) ℂ) (z : ComplexVector n) :
    fderiv ℂ (polyEval p) z =
      ∑ j, polyEval (pderiv j p) z • (EuclideanSpace.proj j : ComplexVector n →L[ℂ] ℂ) :=
  (hasFDerivAt_polyEval p z).fderiv

end Yau.Proofs.Y01Aux
