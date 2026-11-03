import Yau.Proofs.Y02Homogeneous
import Yau.Proofs.Y02Polarization

/-! Fixed labeled slots express each monomial as powers of fixed linear forms. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

open MvPolynomial

variable {n : ℕ}

abbrev MonomialSlots (a : Fin n →₀ ℕ) := Σ i : Fin n, Fin (a i)

theorem card_monomialSlots (a : Fin n →₀ ℕ) : Fintype.card (MonomialSlots a) = a.degree := by
  simp [Fintype.card_sigma, Finsupp.degree_eq_sum]

def monomialSlotEquiv (a : Fin n →₀ ℕ) : MonomialSlots a ≃ Fin a.degree :=
  Fintype.equivFinOfCardEq (card_monomialSlots a)

def monomialWord (a : Fin n →₀ ℕ) (t : Fin a.degree) : Fin n :=
  ((monomialSlotEquiv a).symm t).1

theorem monomialWord_product (a : Fin n →₀ ℕ) :
    (∏ t, X (monomialWord a t) : MvPolynomial (Fin n) ℂ) = monomial a 1 := by
  change (∏ t, X (((monomialSlotEquiv a).symm t).1)) = _
  rw [(monomialSlotEquiv a).symm.prod_comp
    (fun s : MonomialSlots a => (X s.1 : MvPolynomial (Fin n) ℂ))]
  change (∏ s : (Σ i : Fin n, Fin (a i)), X s.1) = _
  rw [Fintype.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype]
  intro i
  exact pow_zero _

def slotForm (a : Fin n →₀ ℕ) (S : Finset (Fin a.degree)) : Fin n → ℂ :=
  ∑ t ∈ S, Pi.single (monomialWord a t) 1

theorem linearForm_slotForm (a : Fin n →₀ ℕ) (S : Finset (Fin a.degree)) :
    linearForm (slotForm a S) = ∑ t ∈ S, X (monomialWord a t) := by
  classical
  unfold linearForm slotForm
  simp only [Finset.sum_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  simp [Pi.single_apply]

theorem monomial_polarization (a : Fin n →₀ ℕ) :
    (a.degree.factorial : MvPolynomial (Fin n) ℂ) * monomial a 1 =
      ∑ S : Finset (Fin a.degree),
        (-1 : MvPolynomial (Fin n) ℂ) ^ (a.degree - S.card) * linearForm (slotForm a S) ^ a.degree := by
  have h := polarization_fin a.degree (fun t => (X (monomialWord a t) : MvPolynomial (Fin n) ℂ))
  rw [monomialWord_product] at h
  simpa only [linearForm_slotForm] using h.symm

end Yau.Proofs.Y02Aux
