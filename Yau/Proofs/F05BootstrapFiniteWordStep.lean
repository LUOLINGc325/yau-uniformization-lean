import Yau.Proofs.F05BootstrapGoodSourceCalc
import Yau.Proofs.F05BootstrapGoodSourceHolder

/-! A genuine finite Schauder induction step for zero physical trace.
The new word's spatial jets are constructed by the good quotient estimate;
only the current finite solution words enter the source hypotheses. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2400000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_good_word_zero_trace_upgrade {ν d : Option (RIdx n)} {T α lam upper : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1) (hd : F05GoodLetter ν d)
    (β : List (Option (RIdx n))) (hβ : F05GoodList ν β)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (f u : Point n → ℝ)
    (hEll : Elliptic (F05PosPatch ν T) a lam upper) (hFace : F05ZeroFace ν T u)
    (hAH : ∀ γ : List (Option (RIdx n)), γ.length ≤ β.length+1 → F05GoodList ν γ →
      F05LocalHolder α ν T (F05GoodWord T γ a))
    (hBH : ∀ γ : List (Option (RIdx n)), γ.length ≤ β.length+1 → F05GoodList ν γ → ∀ j,
      F05LocalHolder α ν T (F05GoodWord T γ (fun z => b z j)))
    (hFH : ∀ γ : List (Option (RIdx n)), γ.length ≤ β.length+1 → F05GoodList ν γ →
      F05LocalHolder α ν T (F05GoodWord T γ f))
    (hAD : ∀ γ : List (Option (RIdx n)), γ.length ≤ β.length → F05GoodList ν γ →
      F05GoodDiffOn T d (F05GoodWord T γ a) (F05PosPatch ν T))
    (hBD : ∀ γ : List (Option (RIdx n)), γ.length ≤ β.length → F05GoodList ν γ → ∀ j,
      F05GoodDiffOn T d (F05GoodWord T γ (fun z => b z j)) (F05PosPatch ν T))
    (hFD : F05GoodDiffOn T d (F05GoodWord T β f) (F05PosPatch ν T))
    (hCurrent : ∀ γ : List (Option (RIdx n)), γ.length ≤ β.length → F05GoodList ν γ →
      F05LocalSchauder α ν T (F05GoodWord T γ u))
    (hPDE : ∀ z ∈ F05PosPatch ν T,
      F05RelOp (F05PosSpace ν) (Ioc 0 T) a b (F05GoodWord T β u) z =
        F05GoodSource T (F05PosSpace ν) a b f u β z) :
    F05LocalSchauder α ν T (F05GoodWord T (d::β) u) ∧
      F05ZeroFace ν T (F05GoodWord T (d::β) u) ∧
      ∀ z ∈ F05PosPatch ν T,
        F05RelOp (F05PosSpace ν) (Ioc 0 T) a b (F05GoodWord T (d::β) u) z =
          F05GoodSource T (F05PosSpace ν) a b f u (d::β) z := by
  have hNil : F05GoodList ν ([] : List (Option (RIdx n))) := by simp [F05GoodList]
  have hOne : F05GoodList ν [d] := (F05GoodList_cons ν d []).mpr ⟨hd,hNil⟩
  have hCalc := F05_good_source_calculus_finite hd β hβ a b f u hAD hBD hFD hCurrent
  have hSourceH : F05LocalHolder α ν T (F05GoodSource T (F05PosSpace ν) a b f u β) := by
    apply F05_good_source_local_holder β a b f u (hFH β (by omega) hβ)
    · intro st hst
      have hLength := (commutatorSplits_properties β st hst).2
      exact hAH st.1 (by omega) (F05_commutator_splits_good hβ hst).1
    · intro st hst j
      have hLength := (commutatorSplits_properties β st hst).2
      exact hBH st.1 (by omega) (F05_commutator_splits_good hβ hst).1 j
    · intro st hst
      have hLength := commutatorSplits_lower_length β st hst
      exact hCurrent st.2 (by omega) (F05_commutator_splits_good hβ hst).2
  have hDerivativeH := F05_good_source_derivative_local_holder hd β hβ a b f u hAH hBH
    (hFH (d::β) (by simp only [List.length_cons]; exact le_rfl) ((F05GoodList_cons ν d β).mpr ⟨hd,hβ⟩)) hCurrent
  have hActualDerivativeH : F05LocalHolder α ν T
      (F05GoodPartial T d (F05GoodSource T (F05PosSpace ν) a b f u β)) := by
    intro r hr hr2 s hs hsT
    obtain ⟨C,hC,hBound⟩ := hDerivativeH r hr hr2 s hs hsT
    exact ⟨C,hC,holderBound_congr_on hBound (fun z hz =>
      (hCalc.2 (F05_receiving_subset_posPatch ν hr2 hs hz)).symm)⟩
  have hStep := F05_good_partial_local_schauder hT hα hα1 hd a b
    (F05GoodSource T (F05PosSpace ν) a b f u β) (F05GoodWord T β u)
    (hCurrent β le_rfl hβ) (F05_good_word_zero_face hFace β hβ) hEll
    (hAH [] (by simp) hNil) (hBH [] (by simp) hNil) hSourceH
    (hAD [] (by simp) hNil) (hBD [] (by simp) hNil) hCalc.1
    (hAH [d] (by simp) hOne) (hBH [d] (by simp) hOne) hActualDerivativeH hPDE
  refine ⟨hStep.1,hStep.2.1,?_⟩
  intro z hz
  change F05RelOp (F05PosSpace ν) (Ioc 0 T) a b (F05GoodPartial T d (F05GoodWord T β u)) z = _
  rw [hStep.2.2 z hz]
  rw [F05_good_source_cons]
  unfold F05FirstGoodSource
  rw [hCalc.2 hz]
  simp only [F05GoodCorrection,F05GoodWord]
  ring

end Yau.Proofs.F05Aux
