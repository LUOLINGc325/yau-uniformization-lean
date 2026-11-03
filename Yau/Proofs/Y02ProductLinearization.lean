import Yau.Proofs.Y02Order

/-! The first difference of a finite product modulo the coefficient-order filtration. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

variable {n r : ℕ} {ι : Type*} [DecidableEq ι]

theorem product_difference_order (s : Finset ι) (a b : ι → ScalarPoly n)
    (hab : ∀ i ∈ s, scalarOrderAtLeast r (a i - b i)) :
    scalarOrderAtLeast r ((∏ i ∈ s, a i) - ∏ i ∈ s, b i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (scalarOrderAtLeast_zero r : scalarOrderAtLeast r (0 : ScalarPoly n))
  | @insert i s hi ih =>
    have heq : (∏ j ∈ insert i s, a j) - (∏ j ∈ insert i s, b j) =
        (a i - b i) * (∏ j ∈ s, a j) + b i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j) := by
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      ring
    rw [heq]
    exact scalarOrderAtLeast_add
      (scalarOrderAtLeast_mul_right (hab i (Finset.mem_insert_self i s)) _)
      (scalarOrderAtLeast_mul_left _ (ih fun j hj => hab j (Finset.mem_insert_of_mem hj)))

theorem product_linear_term_insert (s : Finset ι) (a b c : ι → ScalarPoly n)
    (i : ι) (hi : i ∉ s) :
    (∑ j ∈ insert i s, (a j - b j) * ∏ k ∈ (insert i s).erase j, c k) =
      (a i - b i) * (∏ k ∈ s, c k) +
        c i * (∑ j ∈ s, (a j - b j) * ∏ k ∈ s.erase j, c k) := by
  rw [Finset.sum_insert hi, Finset.erase_insert hi, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := ne_of_mem_of_not_mem hj hi
  have hie : i ∉ s.erase j := fun h => hi (Finset.mem_of_mem_erase h)
  rw [Finset.erase_insert_of_ne hji.symm, Finset.prod_insert hie]
  ring

theorem product_first_difference_order (s : Finset ι) (a b c : ι → ScalarPoly n)
    (ha : ∀ i ∈ s, scalarOrderAtLeast 1 (a i - c i))
    (hb : ∀ i ∈ s, scalarOrderAtLeast 1 (b i - c i))
    (hab : ∀ i ∈ s, scalarOrderAtLeast r (a i - b i)) :
    scalarOrderAtLeast (r + 1)
      ((∏ i ∈ s, a i) - (∏ i ∈ s, b i) -
        ∑ i ∈ s, (a i - b i) * ∏ j ∈ s.erase i, c j) := by
  induction s using Finset.induction_on with
  | empty => simpa using
      (scalarOrderAtLeast_zero (r + 1) : scalarOrderAtLeast (r + 1) (0 : ScalarPoly n))
  | @insert i s hi ih =>
    have haS := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hbS := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have habS := fun j hj => hab j (Finset.mem_insert_of_mem hj)
    have heq :
        ((∏ j ∈ insert i s, a j) - (∏ j ∈ insert i s, b j) -
          ∑ j ∈ insert i s, (a j - b j) * ∏ k ∈ (insert i s).erase j, c k) =
        (a i - b i) * ((∏ j ∈ s, a j) - ∏ j ∈ s, c j) +
          (b i - c i) * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j) +
          c i * (((∏ j ∈ s, a j) - (∏ j ∈ s, b j)) -
            ∑ j ∈ s, (a j - b j) * ∏ k ∈ s.erase j, c k) := by
      rw [Finset.prod_insert hi, Finset.prod_insert hi, product_linear_term_insert s a b c i hi]
      ring
    rw [heq]
    apply scalarOrderAtLeast_add
    · apply scalarOrderAtLeast_add
      · exact scalarOrderAtLeast_mul (hab i (Finset.mem_insert_self i s))
          (product_difference_order s a c haS)
      · simpa only [Nat.add_comm 1 r] using
          scalarOrderAtLeast_mul (hb i (Finset.mem_insert_self i s))
            (product_difference_order s a b habS)
    · exact scalarOrderAtLeast_mul_left _ (ih haS hbS habS)

end Yau.Proofs.Y02Aux
