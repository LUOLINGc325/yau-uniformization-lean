import Yau.Proofs.Y02Order
import Yau.Proofs.Y02CoefficientBounds

/-! Homogeneous extraction, coefficient norm contraction and first jet errors. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

open MvPolynomial

variable {n : ℕ}

theorem mapOrderAtLeast_zero (r : ℕ) : mapOrderAtLeast r (0 : PolyMap n) :=
  fun _ => scalarOrderAtLeast_zero r

theorem mapOrderAtLeast_mono {r s : ℕ} {P : PolyMap n}
    (hP : mapOrderAtLeast r P) (hsr : s ≤ r) : mapOrderAtLeast s P :=
  fun i => scalarOrderAtLeast_mono (hP i) hsr

theorem mapOrderAtLeast_add {r : ℕ} {P Q : PolyMap n}
    (hP : mapOrderAtLeast r P) (hQ : mapOrderAtLeast r Q) : mapOrderAtLeast r (P + Q) :=
  fun i => scalarOrderAtLeast_add (hP i) (hQ i)

theorem mapOrderAtLeast_neg {r : ℕ} {P : PolyMap n}
    (hP : mapOrderAtLeast r P) : mapOrderAtLeast r (-P) :=
  fun i => scalarOrderAtLeast_neg (hP i)

theorem mapOrderAtLeast_sub {r : ℕ} {P Q : PolyMap n}
    (hP : mapOrderAtLeast r P) (hQ : mapOrderAtLeast r Q) : mapOrderAtLeast r (P - Q) :=
  fun i => scalarOrderAtLeast_sub (hP i) (hQ i)

theorem jetEq_mono {P Q : PolyMap n} {d e : ℕ} (h : PolyMap.JetEq P Q d) (hed : e ≤ d) :
    PolyMap.JetEq P Q e := by
  intro i a ha
  exact h i a (ha.trans hed)

theorem jetEq_add {P Q R S : PolyMap n} {d : ℕ}
    (hPQ : PolyMap.JetEq P Q d) (hRS : PolyMap.JetEq R S d) :
    PolyMap.JetEq (P + R) (Q + S) d := by
  intro i a ha
  change (P i).coeff a + (R i).coeff a = (Q i).coeff a + (S i).coeff a
  rw [hPQ i a ha, hRS i a ha]

theorem jetEq_smul {P Q : PolyMap n} {d : ℕ}
    (hPQ : PolyMap.JetEq P Q d) (c : ℂ) : PolyMap.JetEq (c • P) (c • Q) d := by
  intro i a ha
  change (c • P i).coeff a = (c • Q i).coeff a
  simp only [coeff_smul]
  rw [hPQ i a ha]

theorem tangentId_id : tangentId (PolyMap.id : PolyMap n) :=
  (tangentId_iff_jetEq _).mpr (jetEq_refl _ _)

theorem positiveJacFlat_mono {P : PolyMap n} {d e : ℕ}
    (hP : positiveJacFlat P d) (hed : e ≤ d) : positiveJacFlat P e := by
  intro a ha hae
  exact hP a ha (hae.trans (Nat.sub_le_sub_right hed 1))

theorem homogeneousPart_mem (m : ℕ) (P : PolyMap n) :
    homogeneousPart m P ∈ homogeneousFields n m :=
  fun i => homogeneousComponent_isHomogeneous m (P i)

theorem polynomialCoeffNorm_homogeneousComponent_le (m : ℕ) (p : ScalarPoly n) :
    polynomialCoeffNorm (homogeneousComponent m p) ≤ polynomialCoeffNorm p := by
  classical
  have hs : (homogeneousComponent m p).support ⊆ p.support := by
    rw [support_homogeneousComponent]
    exact Finset.filter_subset _ _
  rw [← sum_norm_coeff_eq (homogeneousComponent m p) p.support hs]
  unfold polynomialCoeffNorm
  apply Finset.sum_le_sum
  intro a ha
  rw [coeff_homogeneousComponent]
  split_ifs
  · exact le_rfl
  · simp

theorem coeffNorm_homogeneousPart_le (m : ℕ) (P : PolyMap n) :
    (homogeneousPart m P).coeffNorm ≤ P.coeffNorm := by
  change (∑ i, polynomialCoeffNorm (homogeneousComponent m (P i))) ≤
    ∑ i, polynomialCoeffNorm (P i)
  exact Finset.sum_le_sum fun i hi => polynomialCoeffNorm_homogeneousComponent_le m (P i)

theorem coeffNorm_add_le (P Q : PolyMap n) : (P + Q).coeffNorm ≤ P.coeffNorm + Q.coeffNorm := by
  change (∑ i, polynomialCoeffNorm (P i + Q i)) ≤ _
  calc
    _ ≤ ∑ i, (polynomialCoeffNorm (P i) + polynomialCoeffNorm (Q i)) :=
      Finset.sum_le_sum fun i hi => polynomialCoeffNorm_add (P i) (Q i)
    _ = _ := by rw [Finset.sum_add_distrib]; rfl

theorem coeffNorm_smul (c : ℂ) (P : PolyMap n) : (c • P).coeffNorm = ‖c‖ * P.coeffNorm := by
  change (∑ i, polynomialCoeffNorm (c • P i)) = _
  simp only [smul_eq_C_mul, polynomialCoeffNorm_C_mul]
  rw [← Finset.mul_sum]
  rfl

theorem coeffNorm_neg (P : PolyMap n) : (-P).coeffNorm = P.coeffNorm := by
  rw [← neg_one_smul ℂ P, coeffNorm_smul]
  simp

theorem coeffNorm_sub_le (P Q : PolyMap n) : (P - Q).coeffNorm ≤ P.coeffNorm + Q.coeffNorm := by
  simpa only [sub_eq_add_neg, coeffNorm_neg] using coeffNorm_add_le P (-Q)

theorem coeffNorm_id : (PolyMap.id : PolyMap n).coeffNorm = (n : ℝ) := by
  change (∑ i : Fin n, polynomialCoeffNorm (X i : ScalarPoly n)) = _
  simp only [X, polynomialCoeffNorm_monomial, norm_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem firstDiscrepancy_norm_le (m : ℕ) (J G : PolyMap n) :
    (firstDiscrepancy m J G).coeffNorm ≤ J.coeffNorm + G.coeffNorm :=
  (coeffNorm_homogeneousPart_le m (J - G)).trans (coeffNorm_sub_le J G)

theorem order_sub_homogeneousPart {m : ℕ} {P : PolyMap n}
    (hP : mapOrderAtLeast m P) : mapOrderAtLeast (m + 1) (P - homogeneousPart m P) := by
  intro i a ha
  change (P i).coeff a - (homogeneousComponent m (P i)).coeff a = 0
  rw [coeff_homogeneousComponent]
  by_cases ham : a.degree = m
  · simp [ham]
  · rw [ite_eq_right ham, hP i a (by omega), sub_self]

theorem firstDiscrepancy_corrects {m : ℕ} (hm : 1 ≤ m)
    {J G : PolyMap n} (h : PolyMap.JetEq J G (m - 1)) :
    PolyMap.JetEq (G + firstDiscrepancy m J G) J m := by
  intro i a ha
  change a.degree ≤ m at ha
  change (G i + homogeneousComponent m (J i - G i)).coeff a = (J i).coeff a
  change (G i).coeff a + (homogeneousComponent m (J i - G i)).coeff a = (J i).coeff a
  rw [coeff_homogeneousComponent]
  by_cases ham : a.degree = m
  · simp only [ham]
    change (G i).coeff a + ((J i).coeff a - (G i).coeff a) = (J i).coeff a
    ring
  · rw [ite_eq_right ham, add_zero]
    exact (h i a (by change a.degree ≤ m - 1; omega)).symm

end Yau.Proofs.Y02Aux
