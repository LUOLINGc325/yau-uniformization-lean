import Yau.Proofs.F05BootstrapFiniteWordStep
import Yau.Proofs.F05BootstrapActualCoefficientWords

/-! The finite nonlinear good-word induction. Every coefficient word is
constructed from the current solution words and the fixed smooth
background; no smoothness of exp(-u) is assumed. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2400000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_zero_trace_nonlinear_good_words {ν : Option (RIdx n)} {T α lam upper : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1)
    (A : Point n → Mat n) (B : Point n → RIdx n → ℝ) (H J u : Point n → ℝ)
    (hA : ContDiffOn ℝ ∞ A (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hB : ∀ j, ContDiffOn ℝ ∞ (fun z => B z j) (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hH : ContDiffOn ℝ ∞ H (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hJ : ContDiffOn ℝ ∞ J (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hu : F05LocalSchauder α ν T u) (hFace : F05ZeroFace ν T u)
    (hEll : Elliptic (F05PosPatch ν T) (fun z => Real.exp (-u z) • A z) lam upper)
    (hPDE : ∀ z ∈ F05PosPatch ν T,
      F05RelOp (F05PosSpace ν) (Ioc 0 T) (fun z => Real.exp (-u z) • A z)
        (fun z j => Real.exp (-u z)*B z j) u z = Real.exp (-u z)*H z+J z) :
    ∀ β : List (Option (RIdx n)), F05GoodList ν β →
      F05LocalSchauder α ν T (F05GoodWord T β u) ∧
      ∀ z ∈ F05PosPatch ν T,
        F05RelOp (F05PosSpace ν) (Ioc 0 T) (fun z => Real.exp (-u z) • A z)
          (fun z j => Real.exp (-u z)*B z j) (F05GoodWord T β u) z =
        F05GoodSource T (F05PosSpace ν) (fun z => Real.exp (-u z) • A z)
          (fun z j => Real.exp (-u z)*B z j) (fun z => Real.exp (-u z)*H z+J z) u β z := by
  let a := fun z => Real.exp (-u z) • A z
  let b := fun z j => Real.exp (-u z)*B z j
  let f := fun z => Real.exp (-u z)*H z+J z
  have hBase : F05LocalSchauder α ν T (F05GoodWord T [] u) ∧
      ∀ z ∈ F05PosPatch ν T,
        F05RelOp (F05PosSpace ν) (Ioc 0 T) a b (F05GoodWord T [] u) z =
          F05GoodSource T (F05PosSpace ν) a b f u [] z := by
    exact ⟨hu,by simpa only [F05GoodWord,F05_good_source_nil] using hPDE⟩
  have hInd (m : ℕ) : ∀ β : List (Option (RIdx n)), β.length ≤ m → F05GoodList ν β →
      F05LocalSchauder α ν T (F05GoodWord T β u) ∧
      ∀ z ∈ F05PosPatch ν T,
        F05RelOp (F05PosSpace ν) (Ioc 0 T) a b (F05GoodWord T β u) z =
          F05GoodSource T (F05PosSpace ν) a b f u β z := by
    induction m with
    | zero =>
      intro β hLen hβ
      cases β with
      | nil => exact hBase
      | cons d γ => simp only [List.length_cons] at hLen; omega
    | succ m ih =>
      intro β hLen hβ
      cases β with
      | nil => exact hBase
      | cons d γ =>
        have hγLen : γ.length ≤ m := by simp only [List.length_cons] at hLen; omega
        have hdγ := (F05GoodList_cons ν d γ).mp hβ
        have hCurrent (δ : List (Option (RIdx n))) (hδ : δ.length ≤ m) (hGood : F05GoodList ν δ) :=
          (ih δ hδ hGood).1
        have hDataA := F05_actual_exp_background_finite hα hα1 m u A hCurrent hA
        have hDataB := fun j => F05_actual_exp_background_finite hα hα1 m u (fun z => B z j) hCurrent (hB j)
        have hDataF := F05_actual_exp_forcing_finite hα hα1 m u H J hCurrent hH hJ
        have hStep := F05_good_word_zero_trace_upgrade hT hα hα1 hdγ.1 γ hdγ.2 a b f u hEll hFace
          (fun δ hδ hGood => hDataA.1 δ (by omega) hGood)
          (fun δ hδ hGood j => (hDataB j).1 δ (by omega) hGood)
          (fun δ hδ hGood => hDataF.1 δ (by omega) hGood)
          (fun δ hδ hGood => hDataA.2 δ (hδ.trans hγLen) hGood d hdγ.1)
          (fun δ hδ hGood j => (hDataB j).2 δ (hδ.trans hγLen) hGood d hdγ.1)
          (hDataF.2 γ hγLen hdγ.2 d hdγ.1)
          (fun δ hδ hGood => hCurrent δ (hδ.trans hγLen) hGood)
          (ih γ hγLen hdγ.2).2
        exact ⟨hStep.1,hStep.2.2⟩
  intro β hβ
  exact hInd β.length β le_rfl hβ

end Yau.Proofs.F05Aux
