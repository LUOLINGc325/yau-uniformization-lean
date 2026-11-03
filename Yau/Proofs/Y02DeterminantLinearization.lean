import Yau.Proofs.Y02ProductLinearization

/-! Determinant linearization at the identity in the finite coefficient filtration. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

variable {n r : ℕ}

theorem permutation_erased_identity_product (σ : Equiv.Perm (Fin n)) (j : Fin n)
    (hσ : σ ≠ 1) :
    (∏ k ∈ Finset.univ.erase j, (1 : Matrix (Fin n) (Fin n) (ScalarPoly n)) (σ k) k) = 0 := by
  classical
  by_contra hprod
  have hfix : ∀ k : Fin n, k ≠ j → σ k = k := by
    intro k hkj
    have hfactor := (Finset.prod_ne_zero_iff.mp hprod) k (Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ _⟩)
    by_contra hbad
    simp [hbad] at hfactor
  have hfixj : σ j = j := by
    by_contra hbad
    exact hbad (σ.injective (hfix (σ j) hbad))
  apply hσ
  apply Equiv.ext
  intro k
  by_cases hkj : k = j
  · simpa [hkj] using hfixj
  · exact hfix k hkj

set_option backward.isDefEq.respectTransparency false in
theorem determinant_linear_term (A B : Matrix (Fin n) (Fin n) (ScalarPoly n)) :
    (∑ σ : Equiv.Perm (Fin n),
      (Equiv.Perm.sign σ : ScalarPoly n) *
        ∑ i, (A (σ i) i - B (σ i) i) *
          ∏ j ∈ Finset.univ.erase i, (1 : Matrix (Fin n) (Fin n) (ScalarPoly n)) (σ j) j) =
      ∑ i, (A i i - B i i) := by
  classical
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · simp [Matrix.one_apply]
  · intro σ hmem hσ
    have hsum : (∑ i, (A (σ i) i - B (σ i) i) *
        ∏ j ∈ Finset.univ.erase i, (1 : Matrix (Fin n) (Fin n) (ScalarPoly n)) (σ j) j) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [permutation_erased_identity_product σ i hσ, mul_zero]
    rw [hsum, mul_zero]
  · simp

theorem determinant_first_difference_order
    (A B : Matrix (Fin n) (Fin n) (ScalarPoly n))
    (hA : ∀ i j, scalarOrderAtLeast 1
      (A i j - (1 : Matrix (Fin n) (Fin n) (ScalarPoly n)) i j))
    (hB : ∀ i j, scalarOrderAtLeast 1
      (B i j - (1 : Matrix (Fin n) (Fin n) (ScalarPoly n)) i j))
    (hAB : ∀ i j, scalarOrderAtLeast r (A i j - B i j)) :
    scalarOrderAtLeast (r + 1) (A.det - B.det - ∑ i, (A i i - B i i)) := by
  classical
  have hsum : scalarOrderAtLeast (r + 1)
      (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ScalarPoly n) *
        ((∏ i, A (σ i) i) - (∏ i, B (σ i) i) -
          ∑ i, (A (σ i) i - B (σ i) i) *
            ∏ j ∈ Finset.univ.erase i, (1 : Matrix (Fin n) (Fin n) (ScalarPoly n)) (σ j) j)) := by
    apply scalarOrderAtLeast_sum
    intro σ hσ
    apply scalarOrderAtLeast_mul_left
    exact product_first_difference_order Finset.univ
      (fun i => A (σ i) i) (fun i => B (σ i) i)
      (fun i => (1 : Matrix (Fin n) (Fin n) (ScalarPoly n)) (σ i) i)
      (fun i hi => hA (σ i) i) (fun i hi => hB (σ i) i) (fun i hi => hAB (σ i) i)
  have heq : (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ScalarPoly n) *
        ((∏ i, A (σ i) i) - (∏ i, B (σ i) i) -
          ∑ i, (A (σ i) i - B (σ i) i) *
            ∏ j ∈ Finset.univ.erase i, (1 : Matrix (Fin n) (Fin n) (ScalarPoly n)) (σ j) j)) =
      A.det - B.det - ∑ i, (A i i - B i i) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [determinant_linear_term, Matrix.det_apply', Matrix.det_apply']
    rw [Finset.sum_sub_distrib]
  rwa [heq] at hsum

end Yau.Proofs.Y02Aux
