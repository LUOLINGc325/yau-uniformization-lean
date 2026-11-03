import Yau.LeafProofs.L21WeakJets

/-! A finite weak graph jet gains exactly one order on an inner domain.
The new highest order comes from the proved first-order graph gain. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem extend_weak_graph_jet {W V : Set (X n)} (hW : IsOpen W) (hV : IsOpen V)
    (hcV : IsCompact (closure V)) (hVW : closure V ⊆ W)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A W)
    (hsmall : ∀ x ∈ W, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2)
    (f : X n → Fin n → ℂ) (hf : ∀ i, ContDiffOn ℝ ∞ (fun x => f x i) W)
    (q : ℕ) (u : X n → ℂ) (U : List (Yau.RIdx n) → X n → ℂ)
    (hJet : WeakGraphJet A f u U q W) :
    ∃ U' : List (Yau.RIdx n) → X n → ℂ, WeakGraphJet A f u U' (q + 1) V := by
  rcases hJet with ⟨hU0, hU, hD, hEq⟩
  have hVW0 : V ⊆ W := subset_closure.trans hVW
  have hAV : MatrixSmoothOn A V := fun i j => (hA i j).mono hVW0
  have hfV (i : Fin n) := (hf i).mono hVW0
  have hExist (w : List (Yau.RIdx n)) (hw : w.length = q) :
      ∃ G : X n → Yau.RIdx n → ℂ,
        (∀ a, MemLp (fun x => G x a) 2 (Yau.lebesgueC n)) ∧
        ∀ a, ComplexWeakDerivativeOn V (U w) (fun x => G x a) (Yau.realVec a) :=
    exists_inner_weak_gradient hW hcV hVW hA hsmall (U w) (graphWordSource A f U w)
      (hU w hw.le) (fun i => graphWordSource_locallyL2 hW hA f hf U q hU w hw.le i)
      (hEq w hw.le)
  let G : ∀ w : List (Yau.RIdx n), w.length = q → X n → Yau.RIdx n → ℂ :=
    fun w hw => (hExist w hw).choose
  have hG2 (w : List (Yau.RIdx n)) (hw : w.length = q) (a : Yau.RIdx n) :
      MemLp (fun x => G w hw x a) 2 (Yau.lebesgueC n) := (hExist w hw).choose_spec.1 a
  have hGD (w : List (Yau.RIdx n)) (hw : w.length = q) (a : Yau.RIdx n) :
      ComplexWeakDerivativeOn V (U w) (fun x => G w hw x a) (Yau.realVec a) :=
    (hExist w hw).choose_spec.2 a
  let U' := extendWordJet q U G
  have hOld (w : List (Yau.RIdx n)) (hw : w.length ≤ q) : U' w = U w :=
    extendWordJet_old q U G w hw
  have hNew (w : List (Yau.RIdx n)) (hw : w.length = q) (a : Yau.RIdx n) :
      U' (a :: w) = fun x => G w hw x a := extendWordJet_new q U G w hw a
  have hUNew (w : List (Yau.RIdx n)) (hw : w.length ≤ q + 1) : LocallyL2On (U' w) V := by
    by_cases hlow : w.length ≤ q
    · rw [hOld w hlow]
      exact locallyL2On_mono (hU w hlow) hVW0
    · cases w with
      | nil => exact False.elim (hlow (Nat.zero_le q))
      | cons a w =>
        have he : w.length = q := by simp only [List.length_cons] at hw hlow; omega
        rw [hNew w he a]
        exact fun _ _ _ => (hG2 w he a).mono_measure Measure.restrict_le_self
  have hDNew (w : List (Yau.RIdx n)) (hw : w.length ≤ q) (a : Yau.RIdx n) :
      ComplexWeakDerivativeOn V (U' w) (U' (a :: w)) (Yau.realVec a) := by
    by_cases he : w.length = q
    · rw [hOld w hw, hNew w he a]
      exact hGD w he a
    · have hshort : w.length < q := by omega
      have hcons : (a :: w).length ≤ q := by simp only [List.length_cons]; omega
      rw [hOld w hw, hOld (a :: w) hcons]
      exact complexWeakDerivativeOn_mono (hD w hshort a) hVW0
  have hSource (w : List (Yau.RIdx n)) (hw : w.length ≤ q) :
      graphWordSource A f U' w = graphWordSource A f U w :=
    graphWordSource_congr A f U' U q hOld w hw
  have hEqOld (w : List (Yau.RIdx n)) (hw : w.length ≤ q) :
      DbarWeakOn A (U' w) (graphWordSource A f U' w) V := by
    rw [hOld w hw, hSource w hw]
    exact dbarWeakOn_mono (hEq w hw) hVW0
  have hEqNew (w : List (Yau.RIdx n)) (hw : w.length ≤ q + 1) :
      DbarWeakOn A (U' w) (graphWordSource A f U' w) V := by
    by_cases hlow : w.length ≤ q
    · exact hEqOld w hlow
    · cases w with
      | nil => exact False.elim (hlow (Nat.zero_le q))
      | cons a w =>
        have he : w.length = q := by simp only [List.length_cons] at hw hlow; omega
        exact graphWordEquation_directional hV hAV f hfV U' q hUNew hDNew w he.le (hEqOld w he.le) a
  refine ⟨U', ?_, hUNew, fun w hw => hDNew w (by omega), hEqNew⟩
  change U [] = u
  exact hU0

end Yau.LeafProofs.L21Aux
