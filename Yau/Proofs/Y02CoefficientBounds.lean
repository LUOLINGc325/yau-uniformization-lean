import Yau.Proofs.Y02Algebra

/-! Elementary coefficient bounds for the polynomial operations in jet realization. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

open MvPolynomial

variable {n : ℕ}

/-- The scalar polynomial version of the contract's coefficient norm. -/
def polynomialCoeffNorm (p : MvPolynomial (Fin n) ℂ) : ℝ :=
  ∑ a ∈ p.support, ‖p.coeff a‖

theorem polynomialCoeffNorm_nonneg (p : MvPolynomial (Fin n) ℂ) :
    0 ≤ polynomialCoeffNorm p := by unfold polynomialCoeffNorm; positivity

theorem sum_norm_coeff_eq (p : MvPolynomial (Fin n) ℂ) (S : Finset (Fin n →₀ ℕ))
    (hS : p.support ⊆ S) : (∑ a ∈ S, ‖p.coeff a‖) = polynomialCoeffNorm p := by
  classical
  unfold polynomialCoeffNorm
  symm
  apply Finset.sum_subset hS
  intro a ha hnot
  simp [notMem_support_iff.mp hnot]

theorem polynomialCoeffNorm_zero : polynomialCoeffNorm (0 : MvPolynomial (Fin n) ℂ) = 0 := by
  simp [polynomialCoeffNorm]

theorem polynomialCoeffNorm_monomial (a : Fin n →₀ ℕ) (c : ℂ) :
    polynomialCoeffNorm (monomial a c) = ‖c‖ := by
  classical
  by_cases hc : c = 0 <;> simp [polynomialCoeffNorm, support_monomial, hc]

theorem polynomialCoeffNorm_add (p q : MvPolynomial (Fin n) ℂ) :
    polynomialCoeffNorm (p + q) ≤ polynomialCoeffNorm p + polynomialCoeffNorm q := by
  classical
  let S := p.support ∪ q.support
  calc
    _ = ∑ a ∈ S, ‖(p + q).coeff a‖ := (sum_norm_coeff_eq _ S support_add).symm
    _ ≤ ∑ a ∈ S, (‖p.coeff a‖ + ‖q.coeff a‖) := by
      apply Finset.sum_le_sum
      intro a ha
      exact norm_add_le _ _
    _ = _ := by
      rw [Finset.sum_add_distrib, sum_norm_coeff_eq p S Finset.subset_union_left,
        sum_norm_coeff_eq q S Finset.subset_union_right]

theorem polynomialCoeffNorm_C_mul (c : ℂ) (p : MvPolynomial (Fin n) ℂ) :
    polynomialCoeffNorm (C c * p) = ‖c‖ * polynomialCoeffNorm p := by
  classical
  have hs : (C c * p).support ⊆ p.support := by
    intro a ha
    rw [mem_support_iff, coeff_C_mul] at ha
    exact mem_support_iff.mpr (right_ne_zero_of_mul ha)
  rw [← sum_norm_coeff_eq (C c * p) p.support hs]
  simp only [coeff_C_mul, norm_mul]
  rw [← Finset.mul_sum]
  rfl

theorem polynomialCoeffNorm_sum {ι : Type*} (S : Finset ι)
    (p : ι → MvPolynomial (Fin n) ℂ) :
    polynomialCoeffNorm (∑ i ∈ S, p i) ≤ ∑ i ∈ S, polynomialCoeffNorm (p i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [polynomialCoeffNorm_zero]
  | @insert i S hi hS =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (polynomialCoeffNorm_add _ _).trans (add_le_add le_rfl hS)

theorem polynomialCoeffNorm_mul (p q : MvPolynomial (Fin n) ℂ) :
    polynomialCoeffNorm (p * q) ≤ polynomialCoeffNorm p * polynomialCoeffNorm q := by
  classical
  have hexp : p * q = ∑ a ∈ p.support, ∑ b ∈ q.support,
      monomial (a + b) (p.coeff a * q.coeff b) := by
    conv_lhs => rw [← support_sum_monomial_coeff p, ← support_sum_monomial_coeff q]
    simp only [Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial]
    rw [Finset.sum_comm]
  rw [hexp]
  apply (polynomialCoeffNorm_sum _ _).trans
  calc
    _ ≤ ∑ a ∈ p.support, ∑ b ∈ q.support,
        polynomialCoeffNorm (monomial (a + b) (p.coeff a * q.coeff b)) :=
      Finset.sum_le_sum fun a ha => polynomialCoeffNorm_sum _ _
    _ = polynomialCoeffNorm p * polynomialCoeffNorm q := by
      simp only [polynomialCoeffNorm_monomial, norm_mul]
      simp only [polynomialCoeffNorm, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

theorem polynomialCoeffNorm_pow (p : MvPolynomial (Fin n) ℂ) (r : ℕ) :
    polynomialCoeffNorm (p ^ r) ≤ polynomialCoeffNorm p ^ r := by
  induction r with
  | zero => simp [polynomialCoeffNorm]
  | succ r hr =>
    rw [pow_succ, pow_succ]
    exact (polynomialCoeffNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_right hr (polynomialCoeffNorm_nonneg p))

end Yau.Proofs.Y02Aux
