import Yau.Proofs.Y02Order

/-! The formal polynomial chain rule and the exact determinant of composition. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

open MvPolynomial

variable {n : ℕ}

theorem pderiv_bind (Q : PolyMap n) (p : ScalarPoly n) (j : Fin n) :
    pderiv j (bind₁ Q p) = ∑ k, bind₁ Q (pderiv k p) * pderiv j (Q k) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p k hp =>
    rw [map_mul, bind₁_X_right, pderiv_mul, hp]
    simp only [pderiv_mul, map_add, map_mul, bind₁_X_right, add_mul, Finset.sum_add_distrib]
    have hfirst : (∑ t, (bind₁ Q (pderiv t p) * Q k) * pderiv j (Q t)) =
        (∑ t, bind₁ Q (pderiv t p) * pderiv j (Q t)) * Q k := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    rw [hfirst]
    congr 1
    simp [pderiv_X, Pi.single_apply]

set_option backward.isDefEq.respectTransparency false in
theorem jacobianMatrix_comp (P Q : PolyMap n) :
    jacobianMatrix (P.comp Q) =
      (jacobianMatrix P).map (bind₁ Q) * jacobianMatrix Q := by
  apply Matrix.ext
  intro i j
  change pderiv j (bind₁ Q (P i)) = ∑ k, bind₁ Q (pderiv k (P i)) * pderiv j (Q k)
  exact pderiv_bind Q (P i) j

set_option backward.isDefEq.respectTransparency false in
theorem jacDet_comp (P Q : PolyMap n) :
    (P.comp Q).jacDet = bind₁ Q P.jacDet * Q.jacDet := by
  change (jacobianMatrix (P.comp Q)).det = _
  rw [jacobianMatrix_comp, Matrix.det_mul]
  congr 1
  exact ((bind₁ Q).map_det (jacobianMatrix P)).symm

theorem jacDet_id : (PolyMap.id : PolyMap n).jacDet = 1 := by
  have hmatrix : jacobianMatrix (PolyMap.id : PolyMap n) = 1 := by
    apply Matrix.ext
    intro i j
    simp [jacobianMatrix, PolyMap.id, pderiv_X, Pi.single_apply, Matrix.one_apply]
  change (jacobianMatrix (PolyMap.id : PolyMap n)).det = _
  rw [hmatrix, Matrix.det_one]

end Yau.Proofs.Y02Aux
