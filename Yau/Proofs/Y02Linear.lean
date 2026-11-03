import Yau.Proofs.Y02JetExtraction
import Yau.Proofs.Y02CompositionBounds
import Yau.Proofs.Y02Estimates
import Yau.Proofs.Y02JacobianComposition

/-! Linear polynomial maps, their actual inverse, and the original matrix norm. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

open MvPolynomial Yau.Blueprint

variable {n : ℕ}

def linearPoly (A : Matrix (Fin n) (Fin n) ℂ) : PolyMap n := fun i => linearForm (A i)

theorem linearPoly_comp_apply (A : Matrix (Fin n) (Fin n) ℂ) (P : PolyMap n) (i : Fin n) :
    (linearPoly A).comp P i = ∑ j, C (A i j) * P j := bind_linearForm (A i) P

set_option backward.isDefEq.respectTransparency false in
theorem linearPoly_comp (A B : Matrix (Fin n) (Fin n) ℂ) :
    (linearPoly A).comp (linearPoly B) = linearPoly (A * B) := by
  funext i
  rw [linearPoly_comp_apply]
  simp only [linearPoly, linearForm, Matrix.mul_apply, map_sum, Finset.mul_sum,
    Finset.sum_mul, map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

set_option backward.isDefEq.respectTransparency false in
theorem linearPoly_one : linearPoly (1 : Matrix (Fin n) (Fin n) ℂ) = PolyMap.id := by
  funext i
  simp [linearPoly, linearForm, Matrix.one_apply, PolyMap.id]

theorem linearForm_coeff_single (l : Fin n → ℂ) (j : Fin n) :
    (linearForm l).coeff (Finsupp.single j 1) = l j := by
  classical
  simp [linearForm, coeff_sum, coeff_C_mul, coeff_X,
    Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]

theorem linearPoly_linearPart (A : Matrix (Fin n) (Fin n) ℂ) : (linearPoly A).linearPart = A := by
  apply Matrix.ext
  intro i j
  exact linearForm_coeff_single (A i) j

set_option backward.isDefEq.respectTransparency false in
theorem linearPoly_comp_linearPart (A : Matrix (Fin n) (Fin n) ℂ) (P : PolyMap n) :
    ((linearPoly A).comp P).linearPart = A * P.linearPart := by
  apply Matrix.ext
  intro i j
  change ((linearPoly A).comp P i).coeff (Finsupp.single j 1) = _
  rw [linearPoly_comp_apply, coeff_sum, Matrix.mul_apply]
  simp only [coeff_C_mul, PolyMap.linearPart]

theorem linearPoly_automorphism (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0) :
    IsPolyAutomorphism (linearPoly A) (linearPoly A⁻¹) := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  constructor
  · rw [linearPoly_comp, Matrix.mul_nonsing_inv A hunit, linearPoly_one]
  · rw [linearPoly_comp, Matrix.nonsing_inv_mul A hunit, linearPoly_one]

theorem linearPoly_degree_le (A : Matrix (Fin n) (Fin n) ℂ) : (linearPoly A).degree ≤ 1 := by
  unfold PolyMap.degree
  apply Finset.sup_le
  intro i hi
  exact (linearForm_homogeneous (A i)).totalDegree_le

theorem linearPoly_fixesZero (A : Matrix (Fin n) (Fin n) ℂ) : (linearPoly A).FixesZero := by
  intro i
  exact (linearForm_homogeneous (A i)).coeff_eq_zero (by simp)

set_option backward.isDefEq.respectTransparency false in
theorem linearPoly_jacDet (A : Matrix (Fin n) (Fin n) ℂ) :
    (linearPoly A).jacDet = C A.det := by
  have heq : jacobianMatrix (linearPoly A) = A.map (C : ℂ →+* ScalarPoly n) := by
    apply Matrix.ext
    intro i j
    exact pderiv_linearForm (A i) j
  change (jacobianMatrix (linearPoly A)).det = _
  rw [heq]
  exact ((C : ℂ →+* ScalarPoly n).map_det A).symm

theorem linearPoly_comp_jacDet (A : Matrix (Fin n) (Fin n) ℂ) (P : PolyMap n) :
    ((linearPoly A).comp P).jacDet = C A.det * P.jacDet := by
  rw [jacDet_comp, linearPoly_jacDet, bind₁_C_right]

theorem linearPoly_coeffNorm_le_sum (A : Matrix (Fin n) (Fin n) ℂ) :
    (linearPoly A).coeffNorm ≤ ∑ i, ∑ j, ‖A i j‖ := by
  change (∑ i, polynomialCoeffNorm (linearForm (A i))) ≤ _
  apply Finset.sum_le_sum
  intro i hi
  apply (polynomialCoeffNorm_sum _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [C_mul_X_eq_monomial, polynomialCoeffNorm_monomial]

theorem linearPoly_coeffNorm_le_matOpNorm (A : Matrix (Fin n) (Fin n) ℂ) :
    (linearPoly A).coeffNorm ≤ (n : ℝ) ^ 2 * matOpNorm A := by
  apply (linearPoly_coeffNorm_le_sum A).trans
  calc
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, matOpNorm A :=
      Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => norm_entry_le_matOpNorm A i j
    _ = _ := by simp [sq, nsmul_eq_mul, mul_assoc]

theorem linearPoly_linearPart_eq_homogeneousPart (P : PolyMap n) :
    linearPoly P.linearPart = homogeneousPart 1 P := by
  classical
  funext i
  apply MvPolynomial.ext
  intro a
  change (linearForm (P.linearPart i)).coeff a = (homogeneousComponent 1 (P i)).coeff a
  rw [coeff_homogeneousComponent]
  by_cases ha : a.degree = 1
  · have hex : a ∈ Set.range (fun j : Fin n => Finsupp.single j 1) := by
      rw [Finsupp.range_single_one]
      exact ha
    obtain ⟨j, rfl⟩ := hex
    rw [linearForm_coeff_single]
    simp [PolyMap.linearPart]
  · rw [ite_eq_right ha]
    exact (linearForm_homogeneous _).coeff_eq_zero ha

theorem linearPoly_linearPart_coeffNorm_le (P : PolyMap n) :
    (linearPoly P.linearPart).coeffNorm ≤ P.coeffNorm := by
  rw [linearPoly_linearPart_eq_homogeneousPart]
  exact coeffNorm_homogeneousPart_le 1 P

theorem jetEq_linearPoly_comp {d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {P Q : PolyMap n}
    (h : PolyMap.JetEq P Q d) : PolyMap.JetEq ((linearPoly A).comp P) ((linearPoly A).comp Q) d := by
  intro i a ha
  rw [linearPoly_comp_apply, linearPoly_comp_apply, coeff_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coeff_C_mul, coeff_C_mul, h j a ha]

end Yau.Proofs.Y02Aux
