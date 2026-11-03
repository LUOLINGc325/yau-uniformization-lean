import Yau.Proofs.F05BootstrapDefinitions
import Yau.Proofs.F05BootstrapPolynomialHolder

/-! Constant subtraction has an exact finite good-word formula. The
nonempty words use no differentiability assumption beyond their actual
computed derivatives. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_good_partial_neg (T : ℝ) (d : Option (RIdx n)) (f : Point n → ℝ) :
    F05GoodPartial T d (fun z => -f z) = fun z => -F05GoodPartial T d f z := by
  funext z
  cases d with
  | none => exact derivWithin.fun_neg
  | some k => exact deriv.fun_neg

theorem F05_good_partial_const_sub (T c : ℝ) (d : Option (RIdx n)) (f : Point n → ℝ) :
    F05GoodPartial T d (fun z => c-f z) = fun z => -F05GoodPartial T d f z := by
  funext z
  cases d with
  | none => exact derivWithin_const_sub c
  | some k => exact deriv_const_sub c

theorem F05_good_word_const_sub {T c : ℝ} (β : List (Option (RIdx n))) (f : Point n → ℝ)
    (hβ : β ≠ []) : F05GoodWord T β (fun z => c-f z) = fun z => -F05GoodWord T β f z := by
  induction β with
  | nil => exact False.elim (hβ rfl)
  | cons d β ih =>
    cases β with
    | nil => exact F05_good_partial_const_sub T c d f
    | cons e γ =>
      rw [F05GoodWord,ih (by simp)]
      exact F05_good_partial_neg T d (F05GoodWord T (e::γ) f)

theorem F05_good_diff_const_sub_word {ν d : Option (RIdx n)} {T c : ℝ}
    (β : List (Option (RIdx n))) (f : Point n → ℝ)
    (hf : F05GoodDiffOn T d (F05GoodWord T β f) (F05PosPatch ν T)) :
    F05GoodDiffOn T d (F05GoodWord T β (fun z => c-f z)) (F05PosPatch ν T) := by
  cases β with
  | nil =>
    intro z hz
    cases d with
    | none => exact (differentiableWithinAt_const c).sub (hf z hz)
    | some k => exact (differentiableAt_const c).sub (hf z hz)
  | cons e γ =>
    rw [F05_good_word_const_sub (e::γ) f (by simp)]
    intro z hz
    cases d with
    | none => exact (hf z hz).neg
    | some k => exact (hf z hz).neg

theorem F05_good_const_sub_word_local_holder {ν : Option (RIdx n)} {T α c : ℝ}
    (β : List (Option (RIdx n))) (f : Point n → ℝ)
    (hf : F05LocalHolder α ν T (F05GoodWord T β f)) :
    F05LocalHolder α ν T (F05GoodWord T β (fun z => c-f z)) := by
  cases β with
  | nil =>
    intro r hr hr2 s hs hsT
    obtain ⟨C,hC,hBound⟩ := hf r hr hr2 s hs hsT
    exact ⟨|c|+C,by positivity,holderBound_sub (holderBound_const α _ c) hBound⟩
  | cons e γ =>
    rw [F05_good_word_const_sub (e::γ) f (by simp)]
    intro r hr hr2 s hs hsT
    obtain ⟨C,hC,hBound⟩ := hf r hr hr2 s hs hsT
    exact ⟨C,hC,holderBound_neg hBound⟩

end Yau.Proofs.F05Aux
