import Yau.LeafProofs.L21WordWeakDerivative

/-! Every next coordinate word satisfies the actual differentiated graph
equation, with a finite lower-order correction expression. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem evalWordTerms_principalCorrectionTerms
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (a : Yau.RIdx n)
    (w : List (Yau.RIdx n)) (U : List (Yau.RIdx n) → X n → ℂ) (x : X n) :
    evalWordTerms U (principalCorrectionTerms A i a w) x =
      -(∑ b, fderiv ℝ (dbarRealCoefficient A i b) x (Yau.realVec a) * U (b :: w) x) := by
  simp only [evalWordTerms, principalCorrectionTerms, List.map_map, Function.comp_apply,
    Finset.sum_map_toList, neg_mul, Finset.sum_neg_distrib]

theorem graphWordSource_cons
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (f : X n → Fin n → ℂ)
    (U : List (Yau.RIdx n) → X n → ℂ) (a : Yau.RIdx n) (w : List (Yau.RIdx n))
    (x : X n) (i : Fin n) :
    graphWordSource A f U (a :: w) x i =
      (wordDerivative (fun y => f y i) (a :: w) x +
        evalWordTerms U (differentiateWordTerms a (correctionTerms A i w)) x) -
          ∑ b, fderiv ℝ (dbarRealCoefficient A i b) x (Yau.realVec a) * U (b :: w) x := by
  simp only [graphWordSource, correctionTerms, evalWordTerms_append,
    evalWordTerms_principalCorrectionTerms]
  ring

theorem graphWordEquation_directional {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (f : X n → Fin n → ℂ) (hf : ∀ i, ContDiffOn ℝ ∞ (fun x => f x i) O)
    (U : List (Yau.RIdx n) → X n → ℂ) (q : ℕ)
    (hU : ∀ w, w.length ≤ q + 1 → LocallyL2On (U w) O)
    (hWeak : ∀ w, w.length ≤ q → ∀ a,
      ComplexWeakDerivativeOn O (U w) (U (a :: w)) (Yau.realVec a))
    (w : List (Yau.RIdx n)) (hw : w.length ≤ q)
    (heq : DbarWeakOn A (U w) (graphWordSource A f U w) O) (a : Yau.RIdx n) :
    DbarWeakOn A (U (a :: w)) (graphWordSource A f U (a :: w)) O := by
  let G := fun x b => U (b :: w) x
  let F := fun x i => wordDerivative (fun y => f y i) (a :: w) x +
    evalWordTerms U (differentiateWordTerms a (correctionTerms A i w)) x
  have hG (b : Yau.RIdx n) : LocallyL2On (fun x => G x b) O := hU (b :: w) (by
    simpa only [List.length_cons] using Nat.add_le_add_right hw 1)
  have hF (i : Fin n) : LocallyL2On (fun x => F x i) O :=
    locallyL2On_add
      (locallyL2On_of_continuousOn (contDiffOn_wordDerivative hO (hf i) (a :: w)).continuousOn)
      (evalWordTerms_locallyL2 U _
        (differentiateWordTerms_smooth hO a _ (correctionTerms_smooth hO hA i w))
        (fun t ht => hU t.2 ((differentiateWordTerms_order a _ w.length
          (correctionTerms_order A i w) t ht).trans (Nat.add_le_add_right hw 1))))
  have hnew := dbar_weak_equation_directional hO hA (U w) (U (a :: w))
    (graphWordSource A f U w) F G (Yau.realVec a)
    (hU w (hw.trans (Nat.le_succ q))) (hG a) hG hF (hWeak w hw) (hWeak w hw a)
    (fun i => graphWordSource_weak_derivative hO hA f hf U q hU hWeak w hw a i) heq
  have hR (x : X n) (i : Fin n) :
      differentiatedDbarSource A (Yau.realVec a) G F x i =
        graphWordSource A f U (a :: w) x i := by
    rw [graphWordSource_cons]
    rfl
  intro i ψ hψ hcψ hsψ
  simpa only [hR] using hnew i ψ hψ hcψ hsψ

end Yau.LeafProofs.L21Aux
