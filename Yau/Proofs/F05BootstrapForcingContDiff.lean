import Yau.Proofs.F05BootstrapCoefficientContDiff

/-! The actual forcing words inherit each current finite joint order
from the solution words and the fixed smooth source backgrounds. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ}

theorem F05_exp_forcing_word_contDiff {ν : Option (RIdx n)} {T α : ℝ} {k : ℕ}
    {Q : Set (Point n)} (hQ : Q ⊆ F05PosPatch ν T) (u H J : Point n → ℝ)
    (hWords : ∀ γ : List (Option (RIdx n)), F05GoodList ν γ →
      F05LocalSchauder α ν T (F05GoodWord T γ u))
    (hJoint : ∀ γ : List (Option (RIdx n)), F05GoodList ν γ →
      ContDiffOn ℝ k (F05GoodWord T γ u) Q)
    (hH : ContDiffOn ℝ ∞ H (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hJ : ContDiffOn ℝ ∞ J (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (β : List (Option (RIdx n))) (hβ : F05GoodList ν β) :
    ContDiffOn ℝ k (F05GoodWord T β (fun z => Real.exp (-u z)*H z+J z)) Q := by
  have hQB : Q ⊆ Metric.ball 0 3 ×ˢ Ioc 0 T := fun z hz =>
    ⟨Metric.ball_subset_ball (by norm_num : (2 : ℝ) ≤ 3) (hQ hz).1.2,(hQ hz).2⟩
  have hExpD (γ : List (Option (RIdx n))) (hGood : F05GoodList ν γ)
      (d : Option (RIdx n)) (hd : F05GoodLetter ν d) :=
    F05_exp_good_word_diff γ u hGood hd (fun δ hLen hG e he =>
      F05_local_schauder_good_diff he (hWords δ hG))
  have hProductD (γ : List (Option (RIdx n))) (hGood : F05GoodList ν γ)
      (d : Option (RIdx n)) (hd : F05GoodLetter ν d) :=
    F05_good_word_smul_diff γ (fun z => Real.exp (-u z)) H hGood hd
      (fun δ hLen hG e he => hExpD δ hG e he)
      (fun δ hLen hG e he => F05_smooth_background_good_diff
        (F05_smooth_background_good_words Metric.isOpen_ball hH δ) e)
  have hEq := F05_good_word_add β (fun z => Real.exp (-u z)*H z) J hβ
    (fun γ hLen hGood d hd => hProductD γ hGood d hd)
    (fun γ hLen hGood d hd => F05_smooth_background_good_diff
      (F05_smooth_background_good_words Metric.isOpen_ball hJ γ) d)
  have hProduct := F05_exp_background_word_contDiff hQ u H hWords hJoint hH β hβ
  have hJWord : ContDiffOn ℝ k (F05GoodWord T β J) Q :=
    ((F05_smooth_background_good_words Metric.isOpen_ball hJ β).mono hQB).of_le (by simp)
  exact (hProduct.add hJWord).congr (fun z hz => hEq (hQ hz))

end Yau.Proofs.F05Aux
