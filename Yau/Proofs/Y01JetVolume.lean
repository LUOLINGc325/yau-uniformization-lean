import Yau.Proofs.Y01JetAlgebra

/-! Jacobian coefficient order is preserved by finite-jet truncation. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open MvPolynomial Yau.Proofs.Y02Aux

variable {n : ℕ}

theorem scalar_order_product_difference {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → MvPolynomial (Fin n) ℂ) {r : ℕ}
    (h : ∀ i ∈ s, scalarOrderAtLeast r (a i - b i)) :
    scalarOrderAtLeast r ((∏ i ∈ s, a i) - ∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using scalarOrderAtLeast_zero r (n := n)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    have heq : a i * (∏ j ∈ s, a j) - b i * (∏ j ∈ s, b j) =
        (a i - b i) * (∏ j ∈ s, a j) + b i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j) := by ring
    rw [heq]
    exact scalarOrderAtLeast_add
      (scalarOrderAtLeast_mul_right (h i (Finset.mem_insert_self _ _)) _)
      (scalarOrderAtLeast_mul_left _ (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))))

theorem jacDet_order_of_jetEq {P Q : PolyMap n} {d : ℕ}
    (h : PolyMap.JetEq P Q d) : scalarOrderAtLeast d (P.jacDet - Q.jacDet) := by
  classical
  have hdiff : ∀ i j, scalarOrderAtLeast d (pderiv j (P i) - pderiv j (Q i)) := by
    intro i j
    have hbase := (jetEq_iff_order _ _ _).1 h i
    simpa only [Pi.sub_apply, map_sub] using scalarOrderAtLeast_pderiv hbase j
  have hsum : scalarOrderAtLeast d
      (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : MvPolynomial (Fin n) ℂ) *
        ((∏ i, pderiv i (P (σ i))) - ∏ i, pderiv i (Q (σ i)))) := by
    apply scalarOrderAtLeast_sum
    intro σ hσ
    apply scalarOrderAtLeast_mul_left
    exact scalar_order_product_difference Finset.univ _ _ (fun i hi => hdiff (σ i) i)
  change scalarOrderAtLeast d ((jacobianMatrix P).det - (jacobianMatrix Q).det)
  rw [Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
  simpa only [mul_sub, jacobianMatrix] using hsum

theorem positiveJacFlat_of_jetEq {P Q : PolyMap n} {d : ℕ}
    (h : PolyMap.JetEq P Q d) (hQ : positiveJacFlat Q d) : positiveJacFlat P d := by
  intro a ha had
  have hz := jacDet_order_of_jetEq h a (by omega)
  change P.jacDet.coeff a - Q.jacDet.coeff a = 0 at hz
  rw [hQ a ha had, sub_zero] at hz
  exact hz

set_option backward.isDefEq.respectTransparency false in
theorem jacDet_constantCoeff (P : PolyMap n) : P.jacDet.coeff 0 = P.linearPart.det := by
  have heq : (jacobianMatrix P).map constantCoeff = P.linearPart := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply, jacobianMatrix, constantCoeff_eq, coeff_pderiv,
      zero_add, Finsupp.zero_apply, Nat.cast_zero, zero_add, Nat.cast_one, one_mul, mul_one, PolyMap.linearPart]
  change constantCoeff (jacobianMatrix P).det = _
  exact ((constantCoeff : MvPolynomial (Fin n) ℂ →+* ℂ).map_det (jacobianMatrix P)).trans
    (congrArg Matrix.det heq)

theorem jacDet_order_constant {P : PolyMap n} {d : ℕ} (hP : positiveJacFlat P d) :
    scalarOrderAtLeast d (P.jacDet - C P.linearPart.det) := by
  intro a ha
  by_cases hz : a = 0
  · subst a
    simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_C, ite_true]
    exact sub_eq_zero.mpr (jacDet_constantCoeff P)
  · have hpos : 1 ≤ a.degree := by
      have hne : a.degree ≠ 0 := fun h => hz ((Finsupp.degree_eq_zero_iff a).1 h)
      omega
    change P.jacDet.coeff a - (C P.linearPart.det).coeff a = 0
    rw [hP a hpos (by omega), coeff_C, ite_eq_right (Ne.symm hz)]
    simp

theorem isConstantVolumeJet_truncate {P : PolyMap n} {d : ℕ} (hd : 1 ≤ d)
    (hzero : P.FixesZero) (hdet : P.linearPart.det ≠ 0) (hflat : positiveJacFlat P d) :
    IsConstantVolumeJet (truncate d P) d := by
  refine ⟨truncate_fixesZero hzero, truncate_degree_le _ _, ?_, ?_⟩
  · simpa only [truncate_linearPart hd] using hdet
  · exact positiveJacFlat_of_jetEq (truncate_jetEq d P) hflat

end Yau.Proofs.Y01Aux
