import Yau.Proofs.F05BootstrapGoodVectorLeibniz
import Yau.Proofs.F05BootstrapLocalVectorHolder

/-! Finite actual scalar-vector coefficient words inherit local Holder
bounds and current good differentiability from their two finite factors. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_good_word_smul_local_holder {ν : Option (RIdx n)} {T α : ℝ}
    (β : List (Option (RIdx n))) (f : Point n → ℝ) (g : Point n → V)
    (hβ : F05GoodList ν β)
    (hFD : ∀ γ : List (Option (RIdx n)), γ.length < β.length → F05GoodList ν γ →
      ∀ d, F05GoodLetter ν d → F05GoodDiffOn T d (F05GoodWord T γ f) (F05PosPatch ν T))
    (hGD : ∀ γ : List (Option (RIdx n)), γ.length < β.length → F05GoodList ν γ →
      ∀ d, F05GoodLetter ν d → F05GoodDiffOn T d (F05GoodWord T γ g) (F05PosPatch ν T))
    (hFH : ∀ γ : List (Option (RIdx n)), γ.length ≤ β.length → F05GoodList ν γ →
      F05LocalHolder α ν T (F05GoodWord T γ f))
    (hGH : ∀ γ : List (Option (RIdx n)), γ.length ≤ β.length → F05GoodList ν γ →
      F05LocalHolder α ν T (F05GoodWord T γ g)) :
    F05LocalHolder α ν T (F05GoodWord T β (fun z => f z • g z)) := by
  have hSum : F05LocalHolder α ν T (fun z => ((F05LeibnizSplits β).map
      (fun st => F05GoodWord T st.1 f z • F05GoodWord T st.2 g z)).sum) := by
    apply F05_local_vector_holder_list_sum (F05LeibnizSplits β)
    intro st hst
    have hProp := F05_leibniz_splits_properties hβ hst
    exact F05_local_vector_holder_smul (hFH st.1 (by omega) hProp.1)
      (hGH st.2 (by omega) hProp.2.1)
  exact F05_local_vector_holder_congr hSum
    (fun z hz => (F05_good_word_leibniz_smul β f g hβ hFD hGD hz).symm)

theorem F05_good_word_smul_diff {ν d : Option (RIdx n)} {T : ℝ}
    (β : List (Option (RIdx n))) (f : Point n → ℝ) (g : Point n → V)
    (hβ : F05GoodList ν β) (hd : F05GoodLetter ν d)
    (hFD : ∀ γ : List (Option (RIdx n)), γ.length ≤ β.length → F05GoodList ν γ →
      ∀ e, F05GoodLetter ν e → F05GoodDiffOn T e (F05GoodWord T γ f) (F05PosPatch ν T))
    (hGD : ∀ γ : List (Option (RIdx n)), γ.length ≤ β.length → F05GoodList ν γ →
      ∀ e, F05GoodLetter ν e → F05GoodDiffOn T e (F05GoodWord T γ g) (F05PosPatch ν T)) :
    F05GoodDiffOn T d (F05GoodWord T β (fun z => f z • g z)) (F05PosPatch ν T) := by
  have hEq := F05_good_word_leibniz_smul β f g hβ
    (fun γ hγ hGood e he => hFD γ hγ.le hGood e he)
    (fun γ hγ hGood e he => hGD γ hγ.le hGood e he)
  apply F05_good_diff_congr hd hEq
  apply F05_good_vector_diff_list_sum (F05LeibnizSplits β)
  intro st hst
  have hProp := F05_leibniz_splits_properties hβ hst
  exact F05_good_diff_smul (hFD st.1 (by omega) hProp.1 d hd)
    (hGD st.2 (by omega) hProp.2.1 d hd)

end Yau.Proofs.F05Aux
