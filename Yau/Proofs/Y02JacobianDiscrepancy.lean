import Yau.Proofs.Y02DeterminantLinearization
import Yau.Proofs.Y02JetExtraction
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! The first error between constant-volume tangent jets is divergence free. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

open MvPolynomial

variable {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem jacobianMatrix_sub_one_order (P : PolyMap n) (hP : P.linearPart = 1) :
    ∀ i j, scalarOrderAtLeast 1
      (jacobianMatrix P i j - (1 : Matrix (Fin n) (Fin n) (ScalarPoly n)) i j) := by
  intro i j
  rw [scalarOrderAtLeast_one_iff]
  have hij := congrFun (congrFun hP i) j
  change (P i).coeff (Finsupp.single j 1) = (1 : Matrix (Fin n) (Fin n) ℂ) i j at hij
  change (pderiv j (P i)).coeff 0 - ((1 : Matrix (Fin n) (Fin n) (ScalarPoly n)) i j).coeff 0 = 0
  rw [coeff_pderiv]
  simp only [zero_add, Finsupp.zero_apply, Nat.cast_zero, zero_add, mul_one]
  rw [hij]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem order_of_jetEq_predecessor {m : ℕ} (hm : 1 ≤ m) {J G : PolyMap n}
    (hjet : PolyMap.JetEq J G (m - 1)) : mapOrderAtLeast m (J - G) := by
  have h := (jetEq_iff_order J G (m - 1)).mp hjet
  simpa only [Nat.sub_add_cancel hm] using h

theorem jacDet_discrepancy_order {m : ℕ} (hm : 2 ≤ m) (J G : PolyMap n)
    (hJ : J.linearPart = 1) (hG : G.linearPart = 1)
    (hjet : PolyMap.JetEq J G (m - 1)) :
    scalarOrderAtLeast m (J.jacDet - G.jacDet - divergence n (J - G)) := by
  have hm1 : 1 ≤ m := by omega
  have hD := order_of_jetEq_predecessor hm1 hjet
  have hAB : ∀ i j, scalarOrderAtLeast (m - 1)
      (jacobianMatrix J i j - jacobianMatrix G i j) := by
    intro i j
    have horder : scalarOrderAtLeast ((m - 1) + 1) (J i - G i) := by
      simpa only [Nat.sub_add_cancel hm1, Pi.sub_apply] using hD i
    simpa only [jacobianMatrix, map_sub] using scalarOrderAtLeast_pderiv horder j
  have hdet := determinant_first_difference_order (jacobianMatrix J) (jacobianMatrix G)
    (jacobianMatrix_sub_one_order J hJ) (jacobianMatrix_sub_one_order G hG) hAB
  have htrace : (∑ i, (jacobianMatrix J i i - jacobianMatrix G i i)) =
      divergence n (J - G) := by
    change (∑ i, (pderiv i (J i) - pderiv i (G i))) = ∑ i, pderiv i (J i - G i)
    simp only [map_sub]
  change scalarOrderAtLeast ((m - 1) + 1)
    (J.jacDet - G.jacDet - ∑ i, (jacobianMatrix J i i - jacobianMatrix G i i)) at hdet
  simpa only [Nat.sub_add_cancel hm1, htrace] using hdet

theorem jacDet_discrepancy_coeff {m : ℕ} (hm : 2 ≤ m) (J G : PolyMap n)
    (hJ : J.linearPart = 1) (hG : G.linearPart = 1)
    (hjet : PolyMap.JetEq J G (m - 1)) (a : Fin n →₀ ℕ) (ha : a.degree = m - 1) :
    (J.jacDet - G.jacDet).coeff a = (divergence n (J - G)).coeff a := by
  have h := jacDet_discrepancy_order hm J G hJ hG hjet a (by omega)
  exact sub_eq_zero.mp h

theorem divergence_order {r : ℕ} {P : PolyMap n} (hP : mapOrderAtLeast (r + 1) P) :
    scalarOrderAtLeast r (divergence n P) := by
  apply scalarOrderAtLeast_sum
  intro i hi
  exact scalarOrderAtLeast_pderiv (hP i) i

theorem divergence_homogeneous {m : ℕ} {P : PolyMap n}
    (hP : P ∈ homogeneousFields n m) : (divergence n P).IsHomogeneous (m - 1) := by
  apply IsHomogeneous.sum
  intro i hi
  exact (hP i).pderiv

theorem firstDiscrepancy_divergence_zero {m d : ℕ} (hm : 2 ≤ m) (hmd : m ≤ d)
    (J G : PolyMap n) (hJ : tangentId J) (hG : tangentId G)
    (hjet : PolyMap.JetEq J G (m - 1))
    (hflatJ : positiveJacFlat J d) (hflatG : positiveJacFlat G d) :
    divergence n (firstDiscrepancy m J G) = 0 := by
  have hm1 : 1 ≤ m := by omega
  let H := firstDiscrepancy m J G
  have hH : H ∈ homogeneousFields n m := homogeneousPart_mem m (J - G)
  have hD := order_of_jetEq_predecessor hm1 hjet
  have hrem := divergence_order (order_sub_homogeneousPart hD)
  change scalarOrderAtLeast m (divergence n ((J - G) - H)) at hrem
  rw [map_sub] at hrem
  apply MvPolynomial.ext
  intro a
  by_cases ha : a.degree = m - 1
  · have hcoeff := jacDet_discrepancy_coeff hm J G hJ.2 hG.2 hjet a ha
    have hequal : (divergence n (J - G)).coeff a = (divergence n H).coeff a :=
      sub_eq_zero.mp (hrem a (by omega))
    have hzero : (divergence n (J - G)).coeff a = 0 := by
      rw [← hcoeff]
      change J.jacDet.coeff a - G.jacDet.coeff a = 0
      rw [hflatJ a (by omega) (by omega), hflatG a (by omega) (by omega), sub_self]
    change (divergence n H).coeff a = 0
    rw [← hequal, hzero]
  · change (divergence n H).coeff a = 0
    exact (divergence_homogeneous hH).coeff_eq_zero ha

set_option backward.isDefEq.respectTransparency false in
theorem positiveJacFlat_of_jacDet_one (P : PolyMap n) (hP : P.jacDet = 1) (d : ℕ) :
    positiveJacFlat P d := by
  classical
  intro a ha had
  have hne : a ≠ 0 := by intro h; simp [h] at ha
  rw [hP, MvPolynomial.coeff_one, ite_eq_right (Ne.symm hne)]

end Yau.Proofs.Y02Aux
