import Yau.Proofs.F05BootstrapGoodPolynomial
import Yau.Proofs.F05BootstrapGoodDirections

/-! Finite word-order bookkeeping for the recursive product-rule
polynomials. Every new atom is an existing word or its one-letter successor. -/

noncomputable section
namespace Yau.Proofs.F05Aux.F05GoodPolynomial
open Yau.Parabolic
variable {n : ℕ}

def order : F05GoodPolynomial n → ℕ
  | .constant _ => 0
  | .atom β => β.length
  | .add P Q => max P.order Q.order
  | .mul P Q => max P.order Q.order

theorem atom_length_le (P : F05GoodPolynomial n) :
    ∀ β ∈ P.atoms, β.length ≤ P.order := by
  induction P with
  | constant c => intro β hβ; simp only [atoms,List.not_mem_nil] at hβ
  | atom γ =>
    intro β hβ
    have hEq : β = γ := List.mem_singleton.mp hβ
    subst β
    exact le_rfl
  | add P Q ihP ihQ =>
    intro β hβ
    rcases List.mem_append.mp hβ with hP | hQ
    · exact (ihP β hP).trans (le_max_left _ _)
    · exact (ihQ β hQ).trans (le_max_right _ _)
  | mul P Q ihP ihQ =>
    intro β hβ
    rcases List.mem_append.mp hβ with hP | hQ
    · exact (ihP β hP).trans (le_max_left _ _)
    · exact (ihQ β hQ).trans (le_max_right _ _)

theorem derivative_order (P : F05GoodPolynomial n) (d : Option (RIdx n)) :
    (P.derivative d).order ≤ P.order+1 := by
  induction P with
  | constant c => simp only [derivative,order]; omega
  | atom β => simp only [derivative,order,List.length_cons]; exact le_rfl
  | add P Q ihP ihQ => simp only [derivative,order]; omega
  | mul P Q ihP ihQ => simp only [derivative,order]; omega

theorem derivative_atoms (P : F05GoodPolynomial n) (d : Option (RIdx n)) :
    ∀ β ∈ (P.derivative d).atoms, ∃ γ ∈ P.atoms, β = γ ∨ β = d::γ := by
  induction P with
  | constant c => intro β hβ; simp only [derivative,atoms,List.not_mem_nil] at hβ
  | atom γ =>
    intro β hβ
    refine ⟨γ,by simp only [atoms,List.mem_singleton],Or.inr ?_⟩
    exact List.mem_singleton.mp hβ
  | add P Q ihP ihQ =>
    intro β hβ
    rcases List.mem_append.mp hβ with hP | hQ
    · obtain ⟨γ,hγ,hEq⟩ := ihP β hP
      exact ⟨γ,List.mem_append_left _ hγ,hEq⟩
    · obtain ⟨γ,hγ,hEq⟩ := ihQ β hQ
      exact ⟨γ,List.mem_append_right _ hγ,hEq⟩
  | mul P Q ihP ihQ =>
    intro β hβ
    change β ∈ ((P.derivative d).atoms++Q.atoms)++(P.atoms++(Q.derivative d).atoms) at hβ
    rcases List.mem_append.mp hβ with hLeft | hRight
    · rcases List.mem_append.mp hLeft with hP | hQ
      · obtain ⟨γ,hγ,hEq⟩ := ihP β hP
        exact ⟨γ,List.mem_append_left _ hγ,hEq⟩
      · exact ⟨β,List.mem_append_right _ hQ,Or.inl rfl⟩
    · rcases List.mem_append.mp hRight with hP | hQ
      · exact ⟨β,List.mem_append_left _ hP,Or.inl rfl⟩
      · obtain ⟨γ,hγ,hEq⟩ := ihQ β hQ
        exact ⟨γ,List.mem_append_right _ hγ,hEq⟩

theorem derivative_good_atoms (P : F05GoodPolynomial n) {ν d : Option (RIdx n)}
    (hd : F05GoodLetter ν d) (hP : ∀ γ ∈ P.atoms, F05GoodList ν γ) :
    ∀ β ∈ (P.derivative d).atoms, F05GoodList ν β := by
  intro β hβ
  obtain ⟨γ,hγ,hEq⟩ := P.derivative_atoms d β hβ
  rcases hEq with hEq | hEq
  · rw [hEq]
    exact hP γ hγ
  · rw [hEq]
    exact (F05GoodList_cons ν d γ).mpr ⟨hd,hP γ hγ⟩

theorem budget_nonneg (P : F05GoodPolynomial n) {B : ℝ} (hB : 0 ≤ B) : 0 ≤ P.budget B := by
  induction P with
  | constant c => exact abs_nonneg c
  | atom β => exact hB
  | add P Q ihP ihQ => exact add_nonneg ihP ihQ
  | mul P Q ihP ihQ => exact mul_nonneg (mul_nonneg (by norm_num) ihP) ihQ

end Yau.Proofs.F05Aux.F05GoodPolynomial
