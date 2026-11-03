import Yau.LeafProofs.L21WeakLinear

/-! Finite coordinate words and the actual correction terms in repeated
weak differentiation. Their rough factors never exceed the current order. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def wordDerivative (f : X n → ℂ) : List (Yau.RIdx n) → X n → ℂ
  | [] => f
  | a :: w => fun x => fderiv ℝ (wordDerivative f w) x (Yau.realVec a)

theorem contDiffOn_wordDerivative {O : Set (X n)} (hO : IsOpen O)
    {f : X n → ℂ} (hf : ContDiffOn ℝ ∞ f O) (w : List (Yau.RIdx n)) :
    ContDiffOn ℝ ∞ (wordDerivative f w) O := by
  induction w with
  | nil => exact hf
  | cons a w ih => exact (ih.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const

abbrev WordTerm (n : ℕ) := (X n → ℂ) × List (Yau.RIdx n)

def evalWordTerms (U : List (Yau.RIdx n) → X n → ℂ) (L : List (WordTerm n)) (x : X n) : ℂ :=
  (L.map (fun t => t.1 x * U t.2 x)).sum

def differentiateWordTerms (a : Yau.RIdx n) (L : List (WordTerm n)) : List (WordTerm n) :=
  L.flatMap fun t =>
    [(fun x => fderiv ℝ t.1 x (Yau.realVec a), t.2), (t.1, a :: t.2)]

@[simp] theorem evalWordTerms_nil (U : List (Yau.RIdx n) → X n → ℂ) (x : X n) :
    evalWordTerms U [] x = 0 := rfl

@[simp] theorem evalWordTerms_cons (U : List (Yau.RIdx n) → X n → ℂ)
    (t : WordTerm n) (L : List (WordTerm n)) (x : X n) :
    evalWordTerms U (t :: L) x = t.1 x * U t.2 x + evalWordTerms U L x := rfl

theorem evalWordTerms_append (U : List (Yau.RIdx n) → X n → ℂ)
    (L K : List (WordTerm n)) (x : X n) :
    evalWordTerms U (L ++ K) x = evalWordTerms U L x + evalWordTerms U K x := by
  simp only [evalWordTerms, List.map_append, List.sum_append]

@[simp] theorem differentiateWordTerms_nil (a : Yau.RIdx n) :
    differentiateWordTerms a [] = [] := rfl

theorem eval_differentiateWordTerms_cons (U : List (Yau.RIdx n) → X n → ℂ)
    (a : Yau.RIdx n) (t : WordTerm n) (L : List (WordTerm n)) (x : X n) :
    evalWordTerms U (differentiateWordTerms a (t :: L)) x =
      (fderiv ℝ t.1 x (Yau.realVec a) * U t.2 x + t.1 x * U (a :: t.2) x) +
        evalWordTerms U (differentiateWordTerms a L) x := by
  simp only [differentiateWordTerms, List.flatMap_cons, evalWordTerms_append,
    evalWordTerms_cons, evalWordTerms_nil, add_zero, add_assoc]

def principalCorrectionTerms (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) (a : Yau.RIdx n) (w : List (Yau.RIdx n)) : List (WordTerm n) :=
  (Finset.univ : Finset (Yau.RIdx n)).toList.map fun b =>
    (fun x => -fderiv ℝ (dbarRealCoefficient A i b) x (Yau.realVec a), b :: w)

def correctionTerms (A : X n → Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    List (Yau.RIdx n) → List (WordTerm n)
  | [] => []
  | a :: w => differentiateWordTerms a (correctionTerms A i w) ++ principalCorrectionTerms A i a w

def graphWordSource (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (f : X n → Fin n → ℂ) (U : List (Yau.RIdx n) → X n → ℂ)
    (w : List (Yau.RIdx n)) (x : X n) (i : Fin n) : ℂ :=
  wordDerivative (fun y => f y i) w x + evalWordTerms U (correctionTerms A i w) x

theorem differentiateWordTerms_order (a : Yau.RIdx n) (L : List (WordTerm n)) (q : ℕ)
    (hL : ∀ t ∈ L, t.2.length ≤ q) :
    ∀ t ∈ differentiateWordTerms a L, t.2.length ≤ q + 1 := by
  intro t ht
  obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact (hL s hs).trans (Nat.le_succ q)
  · simpa only [List.length_cons] using Nat.add_le_add_right (hL s hs) 1

theorem correctionTerms_order (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) (w : List (Yau.RIdx n)) :
    ∀ t ∈ correctionTerms A i w, t.2.length ≤ w.length := by
  induction w with
  | nil => simp [correctionTerms]
  | cons a w ih =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact differentiateWordTerms_order a _ w.length ih t ht
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp ht
      simp only [List.length_cons, le_refl]

theorem differentiateWordTerms_smooth {O : Set (X n)} (hO : IsOpen O)
    (a : Yau.RIdx n) (L : List (WordTerm n))
    (hL : ∀ t ∈ L, ContDiffOn ℝ ∞ t.1 O) :
    ∀ t ∈ differentiateWordTerms a L, ContDiffOn ℝ ∞ t.1 O := by
  intro t ht
  obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact ((hL s hs).fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  · exact hL s hs

theorem correctionTerms_smooth {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (i : Fin n) (w : List (Yau.RIdx n)) :
    ∀ t ∈ correctionTerms A i w, ContDiffOn ℝ ∞ t.1 O := by
  induction w with
  | nil => simp [correctionTerms]
  | cons a w ih =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact differentiateWordTerms_smooth hO a _ ih t ht
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp ht
      exact (((dbarRealCoefficient_smoothOn hA i b).fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const).neg

end Yau.LeafProofs.L21Aux
