import Yau.Proofs.F05BootstrapNonlinearCoefficientWords
import Yau.Proofs.F05BootstrapBackgroundData
import Yau.Proofs.F05BootstrapGoodWordAdd

/-! Smooth fixed backgrounds discharge the finite coefficient inputs.
Only current finite solution Schauder words are required for every next
coefficient value and source word. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_actual_exp_background_finite {ν : Option (RIdx n)} {T α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (m : ℕ) (u : Point n → ℝ) (A : Point n → V)
    (hCurrent : ∀ β : List (Option (RIdx n)), β.length ≤ m → F05GoodList ν β →
      F05LocalSchauder α ν T (F05GoodWord T β u))
    (hA : ContDiffOn ℝ ∞ A (Metric.ball 0 3 ×ˢ Ioc 0 T)) :
    (∀ β : List (Option (RIdx n)), β.length ≤ m+1 → F05GoodList ν β →
      F05LocalHolder α ν T (F05GoodWord T β (fun z => Real.exp (-u z) • A z))) ∧
    (∀ β : List (Option (RIdx n)), β.length ≤ m → F05GoodList ν β →
      ∀ d, F05GoodLetter ν d →
      F05GoodDiffOn T d (F05GoodWord T β (fun z => Real.exp (-u z) • A z)) (F05PosPatch ν T)) :=
  F05_exp_background_coefficient_finite m u A hCurrent
    (fun β hLen hGood => (F05_smooth_background_word_data hα hα1 hA β).1)
    (fun β hLen hGood d hd => (F05_smooth_background_word_data hα hα1 hA β).2 d)

theorem F05_actual_exp_forcing_finite {ν : Option (RIdx n)} {T α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (m : ℕ) (u H J : Point n → ℝ)
    (hCurrent : ∀ β : List (Option (RIdx n)), β.length ≤ m → F05GoodList ν β →
      F05LocalSchauder α ν T (F05GoodWord T β u))
    (hH : ContDiffOn ℝ ∞ H (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hJ : ContDiffOn ℝ ∞ J (Metric.ball 0 3 ×ˢ Ioc 0 T)) :
    (∀ β : List (Option (RIdx n)), β.length ≤ m+1 → F05GoodList ν β →
      F05LocalHolder α ν T (F05GoodWord T β (fun z => Real.exp (-u z)*H z+J z))) ∧
    (∀ β : List (Option (RIdx n)), β.length ≤ m → F05GoodList ν β →
      ∀ d, F05GoodLetter ν d →
      F05GoodDiffOn T d (F05GoodWord T β (fun z => Real.exp (-u z)*H z+J z)) (F05PosPatch ν T)) := by
  have hProduct := F05_actual_exp_background_finite hα hα1 m u H hCurrent hH
  have hJData := fun β => F05_smooth_background_word_data (ν := ν) hα hα1 hJ β
  constructor
  · intro β hLen hβ
    exact F05_good_word_add_local_holder β _ J hβ
      (fun γ hγ hGood d hd => hProduct.2 γ (by omega) hGood d hd)
      (fun γ hγ hGood d hd => (hJData γ).2 d)
      (hProduct.1 β hLen hβ) (hJData β).1
  · intro β hLen hβ d hd
    exact F05_good_word_add_diff β _ J hβ hd
      (fun γ hγ hGood e he => hProduct.2 γ (hγ.trans hLen) hGood e he)
      (fun γ hγ hGood e he => (hJData γ).2 e)

end Yau.Proofs.F05Aux
