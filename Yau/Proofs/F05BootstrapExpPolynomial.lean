import Yau.Proofs.F05BootstrapGoodPolynomialOrder
import Yau.Proofs.F05BootstrapGoodCongruence

/-! The finite exponential derivative polynomials use only solution words
of the displayed finite order. No smoothness of the exponential coefficient
is assumed in the identity below. -/

open Set
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

def F05ExpPolynomial : List (Option (RIdx n)) → F05GoodPolynomial n
  | [] => .constant 1
  | d::β => .add (.mul (.mul (.constant (-1)) (.atom [d])) (F05ExpPolynomial β))
      ((F05ExpPolynomial β).derivative d)

theorem F05_exp_polynomial_order (β : List (Option (RIdx n))) :
    (F05ExpPolynomial β).order ≤ β.length := by
  induction β with
  | nil => exact le_rfl
  | cons d β ih =>
    have hD := (F05ExpPolynomial β).derivative_order d
    simp only [F05ExpPolynomial,F05GoodPolynomial.order,List.length_cons,List.length_nil] at *
    omega

theorem F05_exp_polynomial_good_atoms {ν : Option (RIdx n)}
    {β : List (Option (RIdx n))} (hβ : F05GoodList ν β) :
    ∀ γ ∈ (F05ExpPolynomial β).atoms, F05GoodList ν γ := by
  induction β with
  | nil => intro γ hγ; simp only [F05ExpPolynomial,F05GoodPolynomial.atoms,List.not_mem_nil] at hγ
  | cons d β ih =>
    have hdβ := (F05GoodList_cons ν d β).mp hβ
    have hOld := ih hdβ.2
    intro γ hγ
    change γ ∈ ([]++[[d]])++(F05ExpPolynomial β).atoms++
      ((F05ExpPolynomial β).derivative d).atoms at hγ
    rcases List.mem_append.mp hγ with hLeft | hD
    · rcases List.mem_append.mp hLeft with hOne | hOldγ
      · have hEq : γ = [d] := by simpa only [List.nil_append,List.mem_singleton] using hOne
        rw [hEq]
        exact (F05GoodList_cons ν d []).mpr ⟨hdβ.1,by simp [F05GoodList]⟩
      · exact hOld γ hOldγ
    · exact (F05ExpPolynomial β).derivative_good_atoms hdβ.1 hOld γ hD

theorem F05_exp_good_word_polynomial {ν : Option (RIdx n)} {T : ℝ}
    (β : List (Option (RIdx n))) (u : Point n → ℝ) (hβ : F05GoodList ν β)
    (hFinite : ∀ γ : List (Option (RIdx n)), γ.length < β.length → F05GoodList ν γ →
      ∀ d, F05GoodLetter ν d → F05GoodDiffOn T d (F05GoodWord T γ u) (F05PosPatch ν T)) :
    EqOn (F05GoodWord T β (fun z => Real.exp (-u z)))
      (fun z => Real.exp (-u z)*(F05ExpPolynomial β).eval T u z) (F05PosPatch ν T) := by
  induction β with
  | nil => intro z hz; simp only [F05GoodWord,F05ExpPolynomial,F05GoodPolynomial.eval,mul_one]
  | cons d β ih =>
    have hdβ := (F05GoodList_cons ν d β).mp hβ
    have hPrev := ih hdβ.2 (fun γ hγ hG e hE => hFinite γ
      (by simp only [List.length_cons]; omega) hG e hE)
    have hDu : F05GoodDiffOn T d u (F05PosPatch ν T) :=
      hFinite [] (by simp only [List.length_nil,List.length_cons]; omega)
        (by simp [F05GoodList]) d hdβ.1
    have hAtoms : ∀ γ ∈ (F05ExpPolynomial β).atoms,
        F05GoodDiffOn T d (F05GoodWord T γ u) (F05PosPatch ν T) := by
      intro γ hγ
      have hLen := ((F05ExpPolynomial β).atom_length_le γ hγ).trans (F05_exp_polynomial_order β)
      exact hFinite γ (by simp only [List.length_cons]; omega)
        (F05_exp_polynomial_good_atoms hdβ.2 γ hγ) d hdβ.1
    intro z hz
    change F05GoodPartial T d (F05GoodWord T β (fun p => Real.exp (-u p))) z = _
    rw [F05_good_partial_congr hdβ.1 hPrev hz,
      F05_good_partial_mul (F05_good_diff_exp_neg hDu) ((F05ExpPolynomial β).good_diff hAtoms) hz,
      F05_good_partial_exp_neg hDu hz hz.2,(F05ExpPolynomial β).partial_eval hAtoms hz]
    simp only [F05ExpPolynomial,F05GoodPolynomial.eval,F05GoodWord]
    ring

end Yau.Proofs.F05Aux
