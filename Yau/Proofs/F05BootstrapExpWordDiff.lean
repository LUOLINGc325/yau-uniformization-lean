import Yau.Proofs.F05BootstrapExpWordHolder
import Yau.Proofs.F05BootstrapGoodValue

/-! A finite Schauder induction supplies the next coefficient value words
and all current coefficient differentiability. The next coefficient word
needs no spatial Hessian of the corresponding next solution word. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_exp_good_word_diff {ν d : Option (RIdx n)} {T : ℝ}
    (β : List (Option (RIdx n))) (u : Point n → ℝ) (hβ : F05GoodList ν β)
    (hd : F05GoodLetter ν d)
    (hFinite : ∀ γ : List (Option (RIdx n)), γ.length ≤ β.length → F05GoodList ν γ →
      ∀ e, F05GoodLetter ν e → F05GoodDiffOn T e (F05GoodWord T γ u) (F05PosPatch ν T)) :
    F05GoodDiffOn T d (F05GoodWord T β (fun z => Real.exp (-u z))) (F05PosPatch ν T) := by
  have hEq := F05_exp_good_word_polynomial β u hβ
    (fun γ hγ hG e hE => hFinite γ hγ.le hG e hE)
  apply F05_good_diff_congr hd hEq
  exact F05_good_diff_mul (F05_good_diff_exp_neg (hFinite [] (by simp)
    (by simp [F05GoodList]) d hd))
    ((F05ExpPolynomial β).good_diff (fun γ hγ => hFinite γ
      (((F05ExpPolynomial β).atom_length_le γ hγ).trans (F05_exp_polynomial_order β))
      (F05_exp_polynomial_good_atoms hβ γ hγ) d hd))

theorem F05_local_schauder_value_holder {ν : Option (RIdx n)} {T α : ℝ}
    {v : Point n → ℝ} (hv : F05LocalSchauder α ν T v) : F05LocalHolder α ν T v := by
  intro r hr hr2 s hs hsT
  obtain ⟨C,hC,hSch⟩ := hv r hr hr2 s hs hsT
  exact ⟨C,hC,holderBound_fst hSch.2.1⟩

theorem F05_good_word_next_value_holder {ν : Option (RIdx n)} {T α : ℝ} {m : ℕ}
    {u : Point n → ℝ}
    (hCurrent : ∀ β : List (Option (RIdx n)), β.length ≤ m → F05GoodList ν β →
      F05LocalSchauder α ν T (F05GoodWord T β u))
    (β : List (Option (RIdx n))) (hLen : β.length ≤ m+1) (hβ : F05GoodList ν β) :
    F05LocalHolder α ν T (F05GoodWord T β u) := by
  cases β with
  | nil => exact F05_local_schauder_value_holder (hCurrent [] (by simp) hβ)
  | cons d γ =>
    have hdγ := (F05GoodList_cons ν d γ).mp hβ
    exact F05_local_schauder_good_holder hdγ.1
      (hCurrent γ (by simp only [List.length_cons] at hLen; omega) hdγ.2)

theorem F05_exp_coefficient_words_finite {ν : Option (RIdx n)} {T α : ℝ} (m : ℕ)
    (u : Point n → ℝ)
    (hCurrent : ∀ β : List (Option (RIdx n)), β.length ≤ m → F05GoodList ν β →
      F05LocalSchauder α ν T (F05GoodWord T β u)) :
    (∀ β : List (Option (RIdx n)), β.length ≤ m+1 → F05GoodList ν β →
      F05LocalHolder α ν T (F05GoodWord T β (fun z => Real.exp (-u z)))) ∧
    (∀ β : List (Option (RIdx n)), β.length ≤ m → F05GoodList ν β →
      ∀ d, F05GoodLetter ν d →
      F05GoodDiffOn T d (F05GoodWord T β (fun z => Real.exp (-u z))) (F05PosPatch ν T)) := by
  have hDiff (γ : List (Option (RIdx n))) (hγ : γ.length ≤ m) (hGood : F05GoodList ν γ)
      (d : Option (RIdx n)) (hd : F05GoodLetter ν d) :=
    F05_local_schauder_good_diff hd (hCurrent γ hγ hGood)
  constructor
  · intro β hLen hβ
    apply F05_exp_good_word_local_holder β u hβ
    · intro γ hγ hG d hd
      exact hDiff γ (by omega) hG d hd
    · exact F05_local_schauder_value_holder (hCurrent [] (by simp) (by simp [F05GoodList]))
    · intro γ hγ hG
      exact F05_good_word_next_value_holder hCurrent γ (hγ.trans hLen) hG
  · intro β hLen hβ d hd
    exact F05_exp_good_word_diff β u hβ hd (fun γ hγ hG e hE =>
      hDiff γ (hγ.trans hLen) hG e hE)

end Yau.Proofs.F05Aux
