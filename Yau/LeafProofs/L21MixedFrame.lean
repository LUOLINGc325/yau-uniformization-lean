import Yau.LeafProofs.L21MixedFrameEstimates

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

/-- Uniform actual mixed-frame reconstruction, with linear first-jet values and
uniform first derivatives. All constants precede the open set and coefficients. -/
theorem exists_mixed_frame_coefficients (n : ℕ) :
    ∃ eps C : ℝ, 0 < eps ∧ 0 < C ∧
    ∀ (O : Set (X n)) (A : X n → Matrix (Fin n) (Fin n) ℂ),
      IsOpen O → MatrixSmoothOn A O → JetBound 0 eps A O → JetBound 2 1 A O →
      ∃ c d : Fin n → Fin n → Fin n → X n → ℂ,
        (∀ i j k, ContDiffOn ℝ ∞ (c i j k) O ∧ ContDiffOn ℝ ∞ (d i j k) O) ∧
        (∀ x ∈ O, ∀ i j k, ‖c i j k x‖ ≤ C*mixedFrameDerivativeSize A x ∧
          ‖d i j k x‖ ≤ C*mixedFrameDerivativeSize A x) ∧
        (∀ x ∈ O, ∀ i j k, ‖fderiv ℝ (c i j k) x‖ ≤ C ∧ ‖fderiv ℝ (d i j k) x‖ ≤ C) ∧
        (∀ x ∈ O, ∀ i j k, star (d j i k x) = -c i j k x) ∧
        (∀ (f : X n → ℂ), ContDiffOn ℝ ∞ f O → ∀ x ∈ O, ∀ i j,
          dbarA A i (conjugateD A j f) x-conjugateD A j (dbarA A i f) x =
            ∑ k, (c i j k x*dbarA A k f x+d i j k x*conjugateD A k f x)) := by
  let C : ℝ := 2*mixedFrameBracketConstant n+mixedFrameC1Constant n+1
  have hB0 : 0 ≤ mixedFrameBracketConstant n := by unfold mixedFrameBracketConstant; positivity
  have hD0 : 0 ≤ mixedFrameC1Constant n := by unfold mixedFrameC1Constant; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCV : 2*mixedFrameBracketConstant n ≤ C := by dsimp only [C]; linarith
  have hCD : mixedFrameC1Constant n ≤ C := by dsimp only [C]; linarith
  refine ⟨mixedFrameEpsilon n,C,mixedFrameEpsilon_pos n,hC,?_⟩
  intro O A hO hA hSmall hJet
  refine ⟨mixedFrameC A,mixedFrameD A,?_,?_,?_,?_,?_⟩
  · exact mixedFrame_coefficients_smooth hO hA hSmall
  · intro x hx i j k
    have h := mixedFrame_coefficients_norm hO hA hSmall hJet hx i j k
    exact ⟨h.1.trans (mul_le_mul_of_nonneg_right hCV (mixedFrameDerivativeSize_nonneg A x)),
      h.2.trans (mul_le_mul_of_nonneg_right hCV (mixedFrameDerivativeSize_nonneg A x))⟩
  · intro x hx i j k
    have h := mixedFrame_coefficients_fderiv_norm hO hA hSmall hJet hx i j k
    exact ⟨h.1.trans hCD,h.2.trans hCD⟩
  · intro x hx i j k
    apply mixedFrame_coefficients_conjugate
    intro r s
    simpa only [norm_iteratedFDeriv_zero] using hSmall 0 (by omega) x hx r s
  · intro f hf x hx i j
    apply mixedFrame_commutator hO hA hx _ hf i j
    intro r s
    simpa only [norm_iteratedFDeriv_zero] using hSmall 0 (by omega) x hx r s

end Yau.LeafProofs.L21Aux
