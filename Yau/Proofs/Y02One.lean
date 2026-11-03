import Yau.Proofs.Y02Algebra

/-! The one-dimensional volume-jet condition forces linearity. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

open MvPolynomial

def scalarMap (a : ℂ) : PolyMap 1 := fun _ => C a * X 0

theorem scalarMap_comp (a b : ℂ) : (scalarMap a).comp (scalarMap b) = scalarMap (a * b) := by
  funext i
  simp only [PolyMap.comp, scalarMap, map_mul, bind₁_C_right, bind₁_X_right]
  rw [← mul_assoc, ← map_mul]

theorem scalarMap_one : scalarMap 1 = PolyMap.id := by
  funext i
  fin_cases i
  simp [scalarMap, PolyMap.id]

theorem scalarMap_automorphism {a : ℂ} (ha : a ≠ 0) :
    IsPolyAutomorphism (scalarMap a) (scalarMap a⁻¹) := by
  constructor
  · rw [scalarMap_comp, mul_inv_cancel₀ ha, scalarMap_one]
  · rw [scalarMap_comp, inv_mul_cancel₀ ha, scalarMap_one]

theorem scalarMap_degree_le (a : ℂ) : (scalarMap a).degree ≤ 1 := by
  unfold PolyMap.degree
  apply Finset.sup_le
  intro i hi
  exact (totalDegree_mul _ _).trans (by simp)

theorem scalarMap_coeffNorm (a : ℂ) : (scalarMap a).coeffNorm = ‖a‖ := by
  classical
  by_cases ha : a = 0
  · simp [scalarMap, PolyMap.coeffNorm, ha]
  · simp [scalarMap, PolyMap.coeffNorm, C_mul_X_eq_monomial, support_monomial, ha]

theorem scalarMap_linearPart (a : ℂ) : (scalarMap a).linearPart = fun _ _ => a := by
  funext i j
  fin_cases i
  fin_cases j
  simp [scalarMap, PolyMap.linearPart, coeff_C_mul]

theorem finOne_exponent (m : Fin 1 →₀ ℕ) : m = Finsupp.single 0 (m 0) := by
  apply Finsupp.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp

theorem sum_single_degree (k : ℕ) :
    (Finsupp.single (0 : Fin 1) k).sum (fun _ e => e) = k := by
  exact Finsupp.sum_single_index rfl

theorem volumeJet_one_linear {d : ℕ} (J : PolyMap 1) (hJ : IsConstantVolumeJet J d) :
    J = scalarMap ((J 0).coeff (Finsupp.single 0 1)) := by
  have hdeg : (J 0).totalDegree ≤ d := by
    simpa [PolyMap.degree] using hJ.2.1
  have hjac : J.jacDet = pderiv 0 (J 0) := by
    exact Matrix.det_fin_one (fun i j : Fin 1 => pderiv j (J i))
  have hcoeff (k : ℕ) (hk : 2 ≤ k) : (J 0).coeff (Finsupp.single 0 k) = 0 := by
    by_cases hkd : k ≤ d
    · have hkm : k - 1 + 1 = k := by omega
      have h := hJ.2.2.2 (Finsupp.single 0 (k - 1))
        (by rw [sum_single_degree]; omega) (by rw [sum_single_degree]; omega)
      rw [hjac, coeff_pderiv] at h
      have he : (Finsupp.single (0 : Fin 1) (k - 1) + Finsupp.single 0 1) =
          Finsupp.single 0 k := by rw [← Finsupp.single_add, hkm]
      rw [he] at h
      have hcast : ((Finsupp.single (0 : Fin 1) (k - 1)) 0 + 1 : ℂ) ≠ 0 := by
        simp only [Finsupp.single_eq_same]
        exact_mod_cast (by omega : k - 1 + 1 ≠ 0)
      exact (mul_eq_zero.mp h).resolve_right hcast
    · apply coeff_eq_zero_of_totalDegree_lt
      change (J 0).totalDegree < (Finsupp.single (0 : Fin 1) k).sum (fun _ e => e)
      rw [sum_single_degree]
      exact lt_of_le_of_lt hdeg (show d < k by omega)
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  apply MvPolynomial.ext
  intro m
  change (J 0).coeff m =
    (C ((J 0).coeff (Finsupp.single 0 1)) * X (0 : Fin 1)).coeff m
  conv_lhs => rw [finOne_exponent m]
  conv_rhs => rw [finOne_exponent m]
  by_cases hm0 : m 0 = 0
  · simpa [hm0, coeff_C_mul, coeff_X] using hJ.1 0
  · by_cases hm1 : m 0 = 1
    · simp [hm1, coeff_C_mul]
    · rw [hcoeff _ (by omega)]
      simp [C_mul_X_eq_monomial, coeff_monomial, Ne.symm hm1]

set_option backward.isDefEq.respectTransparency false in
theorem scalarMap_linearPart_inv {a : ℂ} (ha : a ≠ 0) :
    (scalarMap a).linearPart⁻¹ = (scalarMap a⁻¹).linearPart := by
  apply Matrix.inv_eq_right_inv
  rw [scalarMap_linearPart, scalarMap_linearPart]
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hij : i = j := Subsingleton.elim _ _
  simp [ha, hij]

end Yau.Proofs.Y02Aux
