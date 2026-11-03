import Yau.Proofs.F05BootstrapExpPolynomial
import Yau.Proofs.F05BootstrapPolynomialHolder

/-! Actual finite-order exponential coefficient words have Holder bounds
from the finite solution words at that order. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_exp_good_word_holder {ν : Option (RIdx n)} {T α B : ℝ}
    (β : List (Option (RIdx n))) (u : Point n → ℝ) (hβ : F05GoodList ν β)
    (hFinite : ∀ γ : List (Option (RIdx n)), γ.length < β.length → F05GoodList ν γ →
      ∀ d, F05GoodLetter ν d → F05GoodDiffOn T d (F05GoodWord T γ u) (F05PosPatch ν T))
    {Q : Set (Point n)} (hQ : Q ⊆ F05PosPatch ν T)
    (hu : HolderBound α Q u B)
    (hAtoms : ∀ γ ∈ (F05ExpPolynomial β).atoms, HolderBound α Q (F05GoodWord T γ u) B) :
    HolderBound α Q (F05GoodWord T β (fun z => Real.exp (-u z)))
      (2*(Real.exp B*(1+B))*(F05ExpPolynomial β).budget B) := by
  have hExp := F05_holder_exp (holderBound_neg hu) (fun z hz =>
    (neg_le_abs (u z)).trans (hu.2.1 z hz))
  have hProduct := holderBound_mul hExp ((F05ExpPolynomial β).holder_eval hAtoms)
  exact holderBound_congr_on hProduct (fun z hz =>
    (F05_exp_good_word_polynomial β u hβ hFinite (hQ hz)).symm)

theorem F05_exp_good_word_local_holder {ν : Option (RIdx n)} {T α : ℝ}
    (β : List (Option (RIdx n))) (u : Point n → ℝ) (hβ : F05GoodList ν β)
    (hFinite : ∀ γ : List (Option (RIdx n)), γ.length < β.length → F05GoodList ν γ →
      ∀ d, F05GoodLetter ν d → F05GoodDiffOn T d (F05GoodWord T γ u) (F05PosPatch ν T))
    (hu : F05LocalHolder α ν T u)
    (hWords : ∀ γ, γ.length ≤ β.length → F05GoodList ν γ →
      F05LocalHolder α ν T (F05GoodWord T γ u)) :
    F05LocalHolder α ν T (F05GoodWord T β (fun z => Real.exp (-u z))) := by
  have hP : F05LocalHolder α ν T ((F05ExpPolynomial β).eval T u) :=
    (F05ExpPolynomial β).local_holder (fun γ hγ => hWords γ
      (((F05ExpPolynomial β).atom_length_le γ hγ).trans (F05_exp_polynomial_order β))
      (F05_exp_polynomial_good_atoms hβ γ hγ))
  have hProduct := F05_local_holder_mul (F05_local_holder_exp_neg hu) hP
  intro r hr hr2 s hs hsT
  obtain ⟨C,hC,hBound⟩ := hProduct r hr hr2 s hs hsT
  refine ⟨C,hC,holderBound_congr_on hBound ?_⟩
  intro z hz
  exact (F05_exp_good_word_polynomial β u hβ hFinite
    (F05_receiving_subset_posPatch ν hr2 hs hz)).symm

end Yau.Proofs.F05Aux
