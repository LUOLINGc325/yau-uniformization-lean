import Yau.LeafProofs.L21QuantitativeWords

/-! The proved finite-product mixed Sobolev estimate evaluates the literal
complex coordinate derivatives in the original Euclidean Lebesgue measure. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem contDiff_wordDerivative {f : X n → ℂ} (hf : ContDiff ℝ ∞ f)
    (w : List (Yau.RIdx n)) : ContDiff ℝ ∞ (wordDerivative f w) := by
  induction w with
  | nil => exact hf
  | cons a w ih => exact contDiff_directional ih _

theorem hasCompactSupport_wordDerivative {f : X n → ℂ} (hcf : HasCompactSupport f)
    (w : List (Yau.RIdx n)) : HasCompactSupport (wordDerivative f w) := by
  induction w with
  | nil => exact hcf
  | cons a w ih => exact ih.fderiv_apply ℝ _

theorem coordinateWordDerivative_realCoordinates (ℓ : ℂ →L[ℝ] ℝ) {f : X n → ℂ}
    (hf : ContDiff ℝ ∞ f) (w : List (Fin (realDimension n))) :
    Yau.LeafProofs.L16Aux.coordinateWordDerivative (fun y => ℓ (f ((realCoordinates n).symm y))) w =
      fun y => ℓ (wordDerivative f (w.map (realIndex n).symm) ((realCoordinates n).symm y)) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    simp only [Yau.LeafProofs.L16Aux.coordinateWordDerivative, List.map_cons, wordDerivative]
    rw [ih]
    funext y
    let g := wordDerivative f (w.map (realIndex n).symm)
    have hg := contDiff_wordDerivative hf (w.map (realIndex n).symm)
    have hgcomp := (hg.comp (realCoordinates n).symm.contDiff).differentiable (by simp) y
    have hd : fderiv ℝ (fun z => ℓ (g ((realCoordinates n).symm z))) y (Pi.single j 1) =
        ℓ (fderiv ℝ (g ∘ (realCoordinates n).symm) y (Pi.single j 1)) :=
      congrArg (fun L : (Fin (realDimension n) → ℝ) →L[ℝ] ℝ => L (Pi.single j 1))
        (ℓ.hasFDerivAt.comp y hgcomp.hasFDerivAt).fderiv
    change fderiv ℝ (fun z => ℓ (g ((realCoordinates n).symm z))) y (Pi.single j 1) = _
    rw [hd, realCoordinates_symm_directional (hg.differentiable (by simp))]

theorem integral_sq_mixedDerivative_realCoordinates (ℓ : ℂ →L[ℝ] ℝ) {f : X n → ℂ}
    (hf : ContDiff ℝ ∞ f) (s : Finset (Fin (realDimension n))) :
    (∫ y, (Yau.LeafProofs.L16Aux.mixedDerivative (fun z => ℓ (f ((realCoordinates n).symm z))) s y) ^ 2) =
      ∫ x, (ℓ (wordDerivative f ((s.sort (· ≤ ·)).map (realIndex n).symm) x)) ^ 2 ∂Yau.lebesgueC n := by
  simp only [Yau.LeafProofs.L16Aux.mixedDerivative, coordinateWordDerivative_realCoordinates ℓ hf]
  exact (realCoordinates_symm_measurePreserving n).integral_comp
    (realCoordinates n).symm.toHomeomorph.measurableEmbedding
    (fun x => (ℓ (wordDerivative f ((s.sort (· ≤ ·)).map (realIndex n).symm) x)) ^ 2)

theorem integrable_realCLM_word_sq (ℓ : ℂ →L[ℝ] ℝ) {f : X n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (w : List (Yau.RIdx n)) :
    Integrable (fun x => (ℓ (wordDerivative f w x)) ^ 2) (Yau.lebesgueC n) := by
  letI : IsLocallyFiniteMeasure (Yau.lebesgueC n) := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  have hm : MemLp (fun x => ℓ (wordDerivative f w x)) 2 (Yau.lebesgueC n) :=
    (ℓ.continuous.comp (contDiff_wordDerivative hf w).continuous).memLp_of_hasCompactSupport
    ((hasCompactSupport_wordDerivative hcf w).comp_left (map_zero ℓ)) (p := 2)
  simpa only [Real.norm_eq_abs, sq_abs] using hm.integrable_norm_pow (p := 2) (by decide)

theorem complex_compact_pointwise_norm_sq_le {f : X n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (x : X n) :
    ‖f x‖ ^ 2 ≤ ∑ s : Finset (Fin (realDimension n)),
      ∫ y, ‖wordDerivative f ((s.sort (· ≤ ·)).map (realIndex n).symm) y‖ ^ 2 ∂Yau.lebesgueC n := by
  have hrcont := Complex.reCLM.contDiff.comp (hf.comp (realCoordinates n).symm.contDiff)
  have hicont := Complex.imCLM.contDiff.comp (hf.comp (realCoordinates n).symm.contDiff)
  have hrcomp := (hcf.comp_homeomorph (realCoordinates n).symm.toHomeomorph).comp_left (map_zero Complex.reCLM)
  have hicomp := (hcf.comp_homeomorph (realCoordinates n).symm.toHomeomorph).comp_left (map_zero Complex.imCLM)
  have hr := Yau.LeafProofs.L16Aux.sq_le_sum_integral_sq_mixedDerivative
    (f := fun y => Complex.reCLM (f ((realCoordinates n).symm y))) hrcont hrcomp (realCoordinates n x)
  have hi := Yau.LeafProofs.L16Aux.sq_le_sum_integral_sq_mixedDerivative
    (f := fun y => Complex.imCLM (f ((realCoordinates n).symm y))) hicont hicomp (realCoordinates n x)
  simp only [integral_sq_mixedDerivative_realCoordinates Complex.reCLM hf,
    ContinuousLinearEquiv.symm_apply_apply] at hr
  simp only [integral_sq_mixedDerivative_realCoordinates Complex.imCLM hf,
    ContinuousLinearEquiv.symm_apply_apply] at hi
  calc
    _ = (Complex.reCLM (f x)) ^ 2 + (Complex.imCLM (f x)) ^ 2 := by
      change ‖f x‖ ^ 2 = (f x).re ^ 2 + (f x).im ^ 2
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    _ ≤ (∑ s : Finset (Fin (realDimension n)), ∫ y,
        (Complex.reCLM (wordDerivative f ((s.sort (· ≤ ·)).map (realIndex n).symm) y)) ^ 2 ∂Yau.lebesgueC n) +
      ∑ s : Finset (Fin (realDimension n)), ∫ y,
        (Complex.imCLM (wordDerivative f ((s.sort (· ≤ ·)).map (realIndex n).symm) y)) ^ 2 ∂Yau.lebesgueC n :=
      add_le_add hr hi
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      rw [← integral_add (integrable_realCLM_word_sq Complex.reCLM hf hcf _)
        (integrable_realCLM_word_sq Complex.imCLM hf hcf _)]
      apply integral_congr_ae
      filter_upwards [] with y
      change (wordDerivative f ((s.sort (· ≤ ·)).map (realIndex n).symm) y).re ^ 2 +
        (wordDerivative f ((s.sort (· ≤ ·)).map (realIndex n).symm) y).im ^ 2 = _
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring

theorem complex_compact_directional_pointwise_norm_sq_le {f : X n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (x : X n) (a : Yau.RIdx n) :
    ‖fderiv ℝ f x (Yau.realVec a)‖ ^ 2 ≤ ∑ s : Finset (Fin (realDimension n)),
      ∫ y, ‖wordDerivative f (((s.sort (· ≤ ·)).map (realIndex n).symm) ++ [a]) y‖ ^ 2 ∂Yau.lebesgueC n := by
  have hh := complex_compact_pointwise_norm_sq_le (contDiff_directional hf (Yau.realVec a))
    (hcf.fderiv_apply ℝ (Yau.realVec a)) x
  simpa only [wordDerivative_append_singleton] using hh

end Yau.LeafProofs.L21Aux
