import Yau.Proofs.Y01PolynomialJets

/-! Repeated coordinate derivatives recover each actual polynomial coefficient. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open MvPolynomial

variable {n : ℕ}

def wordCounts (w : List (Fin n)) : Fin n →₀ ℕ :=
  Multiset.toFinsupp (w : Multiset (Fin n))

def wordPartial : List (Fin n) → MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ
  | [], p => p
  | i :: w, p => wordPartial w (pderiv i p)

@[simp] theorem wordCounts_nil : wordCounts ([] : List (Fin n)) = 0 := by
  simp [wordCounts, Multiset.toFinsupp_zero]

@[simp] theorem wordCounts_cons (i : Fin n) (w : List (Fin n)) :
    wordCounts (i :: w) = Finsupp.single i 1 + wordCounts w := by
  change Multiset.toFinsupp ({i} + (w : Multiset (Fin n))) = _
  rw [Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]
  rfl

theorem wordCounts_degree (w : List (Fin n)) : (wordCounts w).degree = w.length := by
  change (Multiset.toFinsupp (w : Multiset (Fin n))).sum (fun _ e => e) = w.length
  exact Multiset.toFinsupp_sum_eq (w : Multiset (Fin n))

theorem exists_coefficient_word (a : Fin n →₀ ℕ) :
    ∃ w : List (Fin n), wordCounts w = a ∧ w.length = a.degree := by
  let w := a.toMultiset.toList
  have hc : wordCounts w = a := by
    simp only [wordCounts, w, Multiset.coe_toList, Finsupp.toMultiset_toFinsupp]
  exact ⟨w, hc, (wordCounts_degree w).symm.trans (congrArg Finsupp.degree hc)⟩

theorem wordPartial_coeff_zero (w : List (Fin n)) (p : MvPolynomial (Fin n) ℂ) :
    ∃ c : ℕ, 1 ≤ c ∧ (wordPartial w p).coeff 0 = (c : ℂ) * p.coeff (wordCounts w) := by
  induction w generalizing p with
  | nil => exact ⟨1, le_rfl, by simp [wordPartial]⟩
  | cons i w ih =>
    obtain ⟨c, hc, hcoeff⟩ := ih (pderiv i p)
    refine ⟨c * (wordCounts w i + 1), by nlinarith, ?_⟩
    change (wordPartial w (pderiv i p)).coeff 0 = _
    rw [hcoeff, coeff_pderiv, wordCounts_cons]
    rw [add_comm (Finsupp.single i 1)]
    push_cast
    ring

end Yau.Proofs.Y01Aux
