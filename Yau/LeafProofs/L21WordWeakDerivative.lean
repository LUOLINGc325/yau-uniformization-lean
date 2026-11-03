import Yau.LeafProofs.L21WordCorrections

/-! The finite correction expressions have precisely the weak derivatives
obtained by differentiating their smooth coefficient and rough word factors. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem evalWordTerms_locallyL2 {O : Set (X n)} (U : List (Yau.RIdx n) → X n → ℂ)
    (L : List (WordTerm n)) (hc : ∀ t ∈ L, ContDiffOn ℝ ∞ t.1 O)
    (hU : ∀ t ∈ L, LocallyL2On (U t.2) O) : LocallyL2On (evalWordTerms U L) O := by
  induction L with
  | nil => exact fun _ _ _ => MemLp.zero'
  | cons t L ih =>
    have ht := locallyL2On_mul_smooth (hc t (List.mem_cons_self)) (hU t (List.mem_cons_self))
    have hL := ih (fun s hs => hc s (List.mem_cons_of_mem t hs))
      (fun s hs => hU s (List.mem_cons_of_mem t hs))
    change LocallyL2On (fun x => t.1 x * U t.2 x + evalWordTerms U L x) O
    exact locallyL2On_add ht hL

theorem evalWordTerms_weak_derivative {O : Set (X n)} (hO : IsOpen O)
    (U : List (Yau.RIdx n) → X n → ℂ) (L : List (WordTerm n)) (a : Yau.RIdx n)
    (hc : ∀ t ∈ L, ContDiffOn ℝ ∞ t.1 O)
    (hU : ∀ t ∈ L, LocallyL2On (U t.2) O)
    (hDU : ∀ t ∈ L, LocallyL2On (U (a :: t.2)) O)
    (hWeak : ∀ t ∈ L, ComplexWeakDerivativeOn O (U t.2) (U (a :: t.2)) (Yau.realVec a)) :
    LocallyL2On (evalWordTerms U L) O ∧
      LocallyL2On (evalWordTerms U (differentiateWordTerms a L)) O ∧
      ComplexWeakDerivativeOn O (evalWordTerms U L)
        (evalWordTerms U (differentiateWordTerms a L)) (Yau.realVec a) := by
  induction L with
  | nil => exact ⟨fun _ _ _ => MemLp.zero', fun _ _ _ => MemLp.zero', complexWeakDerivativeOn_zero O _⟩
  | cons t L ih =>
    have ht := complexWeakDerivativeOn_smooth_mul hO
      (hc t (List.mem_cons_self)) (hU t (List.mem_cons_self)) (hDU t (List.mem_cons_self))
      (hWeak t (List.mem_cons_self))
    have hL := ih (fun s hs => hc s (List.mem_cons_of_mem t hs))
      (fun s hs => hU s (List.mem_cons_of_mem t hs))
      (fun s hs => hDU s (List.mem_cons_of_mem t hs))
      (fun s hs => hWeak s (List.mem_cons_of_mem t hs))
    have hV : LocallyL2On (evalWordTerms U (t :: L)) O := by
      change LocallyL2On (fun x => t.1 x * U t.2 x + evalWordTerms U L x) O
      exact locallyL2On_add ht.1 hL.1
    have he : evalWordTerms U (differentiateWordTerms a (t :: L)) =
        fun x => (t.1 x * U (a :: t.2) x + fderiv ℝ t.1 x (Yau.realVec a) * U t.2 x) +
          evalWordTerms U (differentiateWordTerms a L) x := by
      funext x
      rw [eval_differentiateWordTerms_cons]
      ring
    have hD : LocallyL2On (evalWordTerms U (differentiateWordTerms a (t :: L))) O := by
      rw [he]
      exact locallyL2On_add ht.2.1 hL.2.1
    refine ⟨hV, hD, ?_⟩
    apply complexWeakDerivativeOn_congr
      (complexWeakDerivativeOn_add hO ht.1 ht.2.1 hL.1 hL.2.1 ht.2.2 hL.2.2)
    · intro x _
      rfl
    · intro x _
      rw [he]

theorem graphWordSource_locallyL2 {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (f : X n → Fin n → ℂ) (hf : ∀ i, ContDiffOn ℝ ∞ (fun x => f x i) O)
    (U : List (Yau.RIdx n) → X n → ℂ) (q : ℕ)
    (hU : ∀ w, w.length ≤ q → LocallyL2On (U w) O)
    (w : List (Yau.RIdx n)) (hw : w.length ≤ q) (i : Fin n) :
    LocallyL2On (fun x => graphWordSource A f U w x i) O :=
  locallyL2On_add (locallyL2On_of_continuousOn (contDiffOn_wordDerivative hO (hf i) w).continuousOn)
    (evalWordTerms_locallyL2 U (correctionTerms A i w) (correctionTerms_smooth hO hA i w)
      (fun t ht => hU t.2 ((correctionTerms_order A i w t ht).trans hw)))

theorem graphWordSource_weak_derivative {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (f : X n → Fin n → ℂ) (hf : ∀ i, ContDiffOn ℝ ∞ (fun x => f x i) O)
    (U : List (Yau.RIdx n) → X n → ℂ) (q : ℕ)
    (hU : ∀ w, w.length ≤ q + 1 → LocallyL2On (U w) O)
    (hWeak : ∀ w, w.length ≤ q → ∀ a,
      ComplexWeakDerivativeOn O (U w) (U (a :: w)) (Yau.realVec a))
    (w : List (Yau.RIdx n)) (hw : w.length ≤ q) (a : Yau.RIdx n) (i : Fin n) :
    ComplexWeakDerivativeOn O (fun x => graphWordSource A f U w x i)
      (fun x => wordDerivative (fun y => f y i) (a :: w) x +
        evalWordTerms U (differentiateWordTerms a (correctionTerms A i w)) x) (Yau.realVec a) := by
  have hCorrection := evalWordTerms_weak_derivative hO U (correctionTerms A i w) a
    (correctionTerms_smooth hO hA i w)
    (fun t ht => hU t.2 ((correctionTerms_order A i w t ht).trans (hw.trans (Nat.le_succ q))))
    (fun t ht => hU (a :: t.2) (by
      simpa only [List.length_cons] using Nat.add_le_add_right ((correctionTerms_order A i w t ht).trans hw) 1))
    (fun t ht => hWeak t.2 ((correctionTerms_order A i w t ht).trans hw) a)
  have hW := contDiffOn_wordDerivative hO (hf i) w
  have hWa := contDiffOn_wordDerivative hO (hf i) (a :: w)
  exact complexWeakDerivativeOn_add hO
    (locallyL2On_of_continuousOn hW.continuousOn) (locallyL2On_of_continuousOn hWa.continuousOn)
    hCorrection.1 hCorrection.2.1 (complexWeakDerivativeOn_smooth hO hW _) hCorrection.2.2

end Yau.LeafProofs.L21Aux
