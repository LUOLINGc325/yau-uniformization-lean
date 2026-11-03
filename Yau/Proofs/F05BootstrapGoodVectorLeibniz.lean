import Yau.Proofs.F05BootstrapLeibnizSplits
import Yau.Proofs.F05BootstrapGoodVectorCalculus
import Yau.Proofs.F05BootstrapGoodCongruence

/-! The actual finite scalar-vector Leibniz identity controls nonlinear
principal coefficient words in their genuine matrix norm. -/

open Set
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_good_word_leibniz_smul {ν : Option (RIdx n)} {T : ℝ}
    (β : List (Option (RIdx n))) (f : Point n → ℝ) (g : Point n → V) (hβ : F05GoodList ν β)
    (hF : ∀ γ : List (Option (RIdx n)), γ.length < β.length → F05GoodList ν γ →
      ∀ d, F05GoodLetter ν d → F05GoodDiffOn T d (F05GoodWord T γ f) (F05PosPatch ν T))
    (hG : ∀ γ : List (Option (RIdx n)), γ.length < β.length → F05GoodList ν γ →
      ∀ d, F05GoodLetter ν d → F05GoodDiffOn T d (F05GoodWord T γ g) (F05PosPatch ν T)) :
    EqOn (F05GoodWord T β (fun z => f z • g z))
      (fun z => ((F05LeibnizSplits β).map (fun st =>
        F05GoodWord T st.1 f z • F05GoodWord T st.2 g z)).sum) (F05PosPatch ν T) := by
  induction β with
  | nil => intro z hz; simp only [F05LeibnizSplits,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,F05GoodWord,add_zero]
  | cons d β ih =>
    have hdβ := (F05GoodList_cons ν d β).mp hβ
    have hPrev := ih hdβ.2
      (fun γ hγ hGood e he => hF γ (by simp only [List.length_cons]; omega) hGood e he)
      (fun γ hγ hGood e he => hG γ (by simp only [List.length_cons]; omega) hGood e he)
    let Term (st : List (Option (RIdx n)) × List (Option (RIdx n))) (z : Point n) :=
      F05GoodWord T st.1 f z • F05GoodWord T st.2 g z
    have hFactors (st : List (Option (RIdx n)) × List (Option (RIdx n)))
        (hst : st ∈ F05LeibnizSplits β) :
        F05GoodDiffOn T d (F05GoodWord T st.1 f) (F05PosPatch ν T) ∧
        F05GoodDiffOn T d (F05GoodWord T st.2 g) (F05PosPatch ν T) := by
      have hProp := F05_leibniz_splits_properties hdβ.2 hst
      exact ⟨hF st.1 (by simp only [List.length_cons]; omega) hProp.1 d hdβ.1,
        hG st.2 (by simp only [List.length_cons]; omega) hProp.2.1 d hdβ.1⟩
    have hTerms := fun st hst => F05_good_diff_smul (hFactors st hst).1 (hFactors st hst).2
    intro z hz
    change F05GoodPartial T d (F05GoodWord T β (fun p => f p • g p)) z = _
    rw [F05_good_partial_congr hdβ.1 hPrev hz,
      F05_good_vector_partial_list_sum (F05LeibnizSplits β) hTerms hz]
    calc
      ((F05LeibnizSplits β).map (fun st => F05GoodPartial T d (Term st) z)).sum =
          ((F05LeibnizSplits β).map (fun st =>
            F05GoodWord T (d::st.1) f z • F05GoodWord T st.2 g z+
            F05GoodWord T st.1 f z • F05GoodWord T (d::st.2) g z)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro st hst
        exact F05_good_partial_smul (hFactors st hst).1 (hFactors st hst).2 hz
      _ = ((F05LeibnizSplits (d::β)).map (fun st =>
          F05GoodWord T st.1 f z • F05GoodWord T st.2 g z)).sum := by
        simp only [F05LeibnizSplits,List.map_flatMap,List.map_cons,List.map_nil]
        rw [F05_vector_list_sum_flatMap_pairs]

end Yau.Proofs.F05Aux
