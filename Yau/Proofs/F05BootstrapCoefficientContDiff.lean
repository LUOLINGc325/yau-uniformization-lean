import Yau.Proofs.F05BootstrapPolynomialContDiff
import Yau.Proofs.F05BootstrapActualCoefficientWords

/-! Current finite joint regularity of the actual solution words gives
the same joint order for every nonlinear coefficient word. The finite
polynomial and product identities are proved from actual good derivatives. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ}

theorem F05_exp_word_contDiff {ν : Option (RIdx n)} {T α : ℝ} {k : ℕ}
    {Q : Set (Point n)} (hQ : Q ⊆ F05PosPatch ν T) (u : Point n → ℝ)
    (hWords : ∀ γ : List (Option (RIdx n)), F05GoodList ν γ →
      F05LocalSchauder α ν T (F05GoodWord T γ u))
    (hJoint : ∀ γ : List (Option (RIdx n)), F05GoodList ν γ →
      ContDiffOn ℝ k (F05GoodWord T γ u) Q)
    (β : List (Option (RIdx n))) (hβ : F05GoodList ν β) :
    ContDiffOn ℝ k (F05GoodWord T β (fun z => Real.exp (-u z))) Q := by
  have hPoly := (F05ExpPolynomial β).contDiff_eval (fun γ hγ =>
    hJoint γ (F05_exp_polynomial_good_atoms hβ γ hγ))
  have hExp := (hJoint [] (by simp [F05GoodList])).neg.exp
  apply (hExp.mul hPoly).congr
  intro z hz
  exact F05_exp_good_word_polynomial β u hβ
    (fun γ hLen hGood d hd => F05_local_schauder_good_diff hd (hWords γ hGood)) (hQ hz)

theorem F05_exp_background_word_contDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ν : Option (RIdx n)} {T α : ℝ} {k : ℕ} {Q : Set (Point n)}
    (hQ : Q ⊆ F05PosPatch ν T) (u : Point n → ℝ) (A : Point n → V)
    (hWords : ∀ γ : List (Option (RIdx n)), F05GoodList ν γ →
      F05LocalSchauder α ν T (F05GoodWord T γ u))
    (hJoint : ∀ γ : List (Option (RIdx n)), F05GoodList ν γ →
      ContDiffOn ℝ k (F05GoodWord T γ u) Q)
    (hA : ContDiffOn ℝ ∞ A (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (β : List (Option (RIdx n))) (hβ : F05GoodList ν β) :
    ContDiffOn ℝ k (F05GoodWord T β (fun z => Real.exp (-u z) • A z)) Q := by
  have hQB : Q ⊆ Metric.ball 0 3 ×ˢ Ioc 0 T := fun z hz =>
    ⟨Metric.ball_subset_ball (by norm_num : (2 : ℝ) ≤ 3) (hQ hz).1.2,(hQ hz).2⟩
  have hExpD (γ : List (Option (RIdx n))) (hGood : F05GoodList ν γ)
      (d : Option (RIdx n)) (hd : F05GoodLetter ν d) :=
    F05_exp_good_word_diff γ u hGood hd (fun δ hLen hG e he =>
      F05_local_schauder_good_diff he (hWords δ hG))
  have hASmooth := fun γ => F05_smooth_background_good_words Metric.isOpen_ball hA γ
  have hEq := F05_good_word_leibniz_smul β (fun z => Real.exp (-u z)) A hβ
    (fun γ hLen hGood d hd => hExpD γ hGood d hd)
    (fun γ hLen hGood d hd => F05_smooth_background_good_diff (hASmooth γ) d)
  have hSum : ContDiffOn ℝ k (fun z => ((F05LeibnizSplits β).map (fun st =>
      F05GoodWord T st.1 (fun p => Real.exp (-u p)) z • F05GoodWord T st.2 A z)).sum) Q := by
    apply F05_contDiffOn_list_sum (F05LeibnizSplits β)
    intro st hst
    have hGood := F05_leibniz_splits_properties hβ hst
    exact (F05_exp_word_contDiff hQ u hWords hJoint st.1 hGood.1).smul
      (((hASmooth st.2).mono hQB).of_le (by simp))
  exact hSum.congr (fun z hz => hEq (hQ hz))

end Yau.Proofs.F05Aux
