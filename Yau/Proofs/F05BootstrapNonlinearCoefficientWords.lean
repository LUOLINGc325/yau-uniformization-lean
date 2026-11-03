import Yau.Proofs.F05BootstrapGoodProduct
import Yau.Proofs.F05BootstrapGoodAffineScalar
import Yau.Proofs.F05BootstrapExpWordDiff

/-! The finite nonlinear coefficient budgets are consequences of current
solution Schauder words and the fixed background words. Higher coefficient
regularity is constructed rather than inserted into the solution hypotheses. -/

noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_exp_background_coefficient_finite {ν : Option (RIdx n)} {T α : ℝ}
    (m : ℕ) (u : Point n → ℝ) (A : Point n → V)
    (hCurrent : ∀ β : List (Option (RIdx n)), β.length ≤ m → F05GoodList ν β →
      F05LocalSchauder α ν T (F05GoodWord T β u))
    (hBackgroundH : ∀ β : List (Option (RIdx n)), β.length ≤ m+1 → F05GoodList ν β →
      F05LocalHolder α ν T (F05GoodWord T β A))
    (hBackgroundD : ∀ β : List (Option (RIdx n)), β.length ≤ m → F05GoodList ν β →
      ∀ d, F05GoodLetter ν d → F05GoodDiffOn T d (F05GoodWord T β A) (F05PosPatch ν T)) :
    (∀ β : List (Option (RIdx n)), β.length ≤ m+1 → F05GoodList ν β →
      F05LocalHolder α ν T (F05GoodWord T β (fun z => Real.exp (-u z) • A z))) ∧
    (∀ β : List (Option (RIdx n)), β.length ≤ m → F05GoodList ν β →
      ∀ d, F05GoodLetter ν d →
      F05GoodDiffOn T d (F05GoodWord T β (fun z => Real.exp (-u z) • A z)) (F05PosPatch ν T)) := by
  have hExp := F05_exp_coefficient_words_finite m u hCurrent
  constructor
  · intro β hLen hβ
    apply F05_good_word_smul_local_holder β _ A hβ
    · intro γ hγ hGood d hd
      exact hExp.2 γ (by omega) hGood d hd
    · intro γ hγ hGood d hd
      exact hBackgroundD γ (by omega) hGood d hd
    · intro γ hγ hGood
      exact hExp.1 γ (hγ.trans hLen) hGood
    · intro γ hγ hGood
      exact hBackgroundH γ (hγ.trans hLen) hGood
  · intro β hLen hβ d hd
    exact F05_good_word_smul_diff β _ A hβ hd
      (fun γ hγ hGood e he => hExp.2 γ (hγ.trans hLen) hGood e he)
      (fun γ hγ hGood e he => hBackgroundD γ (hγ.trans hLen) hGood e he)

theorem F05_exp_source_coefficient_finite {ν : Option (RIdx n)} {T α : ℝ}
    (m : ℕ) (u R : Point n → ℝ)
    (hCurrent : ∀ β : List (Option (RIdx n)), β.length ≤ m → F05GoodList ν β →
      F05LocalSchauder α ν T (F05GoodWord T β u))
    (hBackgroundH : ∀ β : List (Option (RIdx n)), β.length ≤ m+1 → F05GoodList ν β →
      F05LocalHolder α ν T (F05GoodWord T β R))
    (hBackgroundD : ∀ β : List (Option (RIdx n)), β.length ≤ m → F05GoodList ν β →
      ∀ d, F05GoodLetter ν d → F05GoodDiffOn T d (F05GoodWord T β R) (F05PosPatch ν T)) :
    (∀ β : List (Option (RIdx n)), β.length ≤ m+1 → F05GoodList ν β →
      F05LocalHolder α ν T (F05GoodWord T β (fun z => (1-Real.exp (-u z))*R z))) ∧
    (∀ β : List (Option (RIdx n)), β.length ≤ m → F05GoodList ν β →
      ∀ d, F05GoodLetter ν d →
      F05GoodDiffOn T d (F05GoodWord T β (fun z => (1-Real.exp (-u z))*R z)) (F05PosPatch ν T)) := by
  have hExp := F05_exp_coefficient_words_finite m u hCurrent
  have hH (β : List (Option (RIdx n))) (hLen : β.length ≤ m+1) (hβ : F05GoodList ν β) :=
    F05_good_const_sub_word_local_holder (c := 1) β (fun z => Real.exp (-u z)) (hExp.1 β hLen hβ)
  have hD (β : List (Option (RIdx n))) (hLen : β.length ≤ m) (hβ : F05GoodList ν β)
      (d : Option (RIdx n)) (hd : F05GoodLetter ν d) :=
    F05_good_diff_const_sub_word (c := 1) β (fun z => Real.exp (-u z)) (hExp.2 β hLen hβ d hd)
  constructor
  · intro β hLen hβ
    exact F05_good_word_smul_local_holder β _ R hβ
      (fun γ hγ hGood d hd => hD γ (by omega) hGood d hd)
      (fun γ hγ hGood d hd => hBackgroundD γ (by omega) hGood d hd)
      (fun γ hγ hGood => hH γ (hγ.trans hLen) hGood)
      (fun γ hγ hGood => hBackgroundH γ (hγ.trans hLen) hGood)
  · intro β hLen hβ d hd
    exact F05_good_word_smul_diff β _ R hβ hd
      (fun γ hγ hGood e he => hD γ (hγ.trans hLen) hGood e he)
      (fun γ hγ hGood e he => hBackgroundD γ (hγ.trans hLen) hGood e he)

end Yau.Proofs.F05Aux
