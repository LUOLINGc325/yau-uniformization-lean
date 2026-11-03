import Yau.Proofs.F05BootstrapGoodVectorCalculus
import Yau.Proofs.F05BootstrapGoodCongruence
import Yau.Proofs.F05BootstrapLocalVectorHolder

/-! Actual finite good words distribute over sums on the original physical
patch, using only the strictly shorter factor derivatives. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_good_word_add {ν : Option (RIdx n)} {T : ℝ}
    (β : List (Option (RIdx n))) (f g : Point n → V) (hβ : F05GoodList ν β)
    (hF : ∀ γ : List (Option (RIdx n)), γ.length < β.length → F05GoodList ν γ →
      ∀ d, F05GoodLetter ν d → F05GoodDiffOn T d (F05GoodWord T γ f) (F05PosPatch ν T))
    (hG : ∀ γ : List (Option (RIdx n)), γ.length < β.length → F05GoodList ν γ →
      ∀ d, F05GoodLetter ν d → F05GoodDiffOn T d (F05GoodWord T γ g) (F05PosPatch ν T)) :
    EqOn (F05GoodWord T β (fun z => f z+g z))
      (fun z => F05GoodWord T β f z+F05GoodWord T β g z) (F05PosPatch ν T) := by
  induction β with
  | nil => intro z hz; rfl
  | cons d β ih =>
    have hdβ := (F05GoodList_cons ν d β).mp hβ
    have hPrev := ih hdβ.2
      (fun γ hγ hGood e he => hF γ (by simp only [List.length_cons]; omega) hGood e he)
      (fun γ hγ hGood e he => hG γ (by simp only [List.length_cons]; omega) hGood e he)
    have hDF := hF β (by simp only [List.length_cons]; omega) hdβ.2 d hdβ.1
    have hDG := hG β (by simp only [List.length_cons]; omega) hdβ.2 d hdβ.1
    intro z hz
    change F05GoodPartial T d (F05GoodWord T β (fun p => f p+g p)) z = _
    rw [F05_good_partial_congr hdβ.1 hPrev hz,F05_good_vector_partial_add hDF hDG hz]
    rfl

theorem F05_good_word_add_local_holder {ν : Option (RIdx n)} {T α : ℝ}
    (β : List (Option (RIdx n))) (f g : Point n → V) (hβ : F05GoodList ν β)
    (hF : ∀ γ : List (Option (RIdx n)), γ.length < β.length → F05GoodList ν γ →
      ∀ d, F05GoodLetter ν d → F05GoodDiffOn T d (F05GoodWord T γ f) (F05PosPatch ν T))
    (hG : ∀ γ : List (Option (RIdx n)), γ.length < β.length → F05GoodList ν γ →
      ∀ d, F05GoodLetter ν d → F05GoodDiffOn T d (F05GoodWord T γ g) (F05PosPatch ν T))
    (hFH : F05LocalHolder α ν T (F05GoodWord T β f))
    (hGH : F05LocalHolder α ν T (F05GoodWord T β g)) :
    F05LocalHolder α ν T (F05GoodWord T β (fun z => f z+g z)) :=
  F05_local_vector_holder_congr (F05_local_vector_holder_add hFH hGH)
    (fun z hz => (F05_good_word_add β f g hβ hF hG hz).symm)

theorem F05_good_word_add_diff {ν d : Option (RIdx n)} {T : ℝ}
    (β : List (Option (RIdx n))) (f g : Point n → V) (hβ : F05GoodList ν β)
    (hd : F05GoodLetter ν d)
    (hF : ∀ γ : List (Option (RIdx n)), γ.length ≤ β.length → F05GoodList ν γ →
      ∀ e, F05GoodLetter ν e → F05GoodDiffOn T e (F05GoodWord T γ f) (F05PosPatch ν T))
    (hG : ∀ γ : List (Option (RIdx n)), γ.length ≤ β.length → F05GoodList ν γ →
      ∀ e, F05GoodLetter ν e → F05GoodDiffOn T e (F05GoodWord T γ g) (F05PosPatch ν T)) :
    F05GoodDiffOn T d (F05GoodWord T β (fun z => f z+g z)) (F05PosPatch ν T) := by
  apply F05_good_diff_congr hd (F05_good_word_add β f g hβ
    (fun γ hγ hGood e he => hF γ hγ.le hGood e he)
    (fun γ hγ hGood e he => hG γ hγ.le hGood e he))
  exact F05_good_vector_diff_add (hF β le_rfl hβ d hd) (hG β le_rfl hβ d hd)

end Yau.Proofs.F05Aux
