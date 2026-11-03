import Yau.LeafProofs.L21LocalWeakGain

/-! Complex compact tests and product calculus for genuine local weak
directional derivatives. All pairings use the original Lebesgue measure. -/

open MeasureTheory
open scoped ContDiff Topology
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def ComplexWeakDerivativeOn (O : Set (X n)) (u g : X n → ℂ) (v : X n) : Prop :=
  ∀ (ψ : X n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ O →
    (∫ x, u x * (fderiv ℝ ψ x v : ℂ) ∂Yau.lebesgueC n) =
      -(∫ x, g x * (ψ x : ℂ) ∂Yau.lebesgueC n)

theorem complexWeakDerivativeOn_of_global {O : Set (X n)}
    {u g : X n → ℂ} {v : X n} (h : ComplexWeakDerivative u g v) :
    ComplexWeakDerivativeOn O u g v := fun ψ hψ hcψ _ => h ψ hψ hcψ

theorem fderiv_re_apply {f : X n → ℂ} {x : X n}
    (hf : DifferentiableAt ℝ f x) (v : X n) :
    fderiv ℝ (fun y => (f y).re) x v = (fderiv ℝ f x v).re := by
  exact congrArg (fun L : X n →L[ℝ] ℝ => L v)
    (Complex.reCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv

theorem fderiv_im_apply {f : X n → ℂ} {x : X n}
    (hf : DifferentiableAt ℝ f x) (v : X n) :
    fderiv ℝ (fun y => (f y).im) x v = (fderiv ℝ f x v).im := by
  exact congrArg (fun L : X n →L[ℝ] ℝ => L v)
    (Complex.imCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv

theorem complex_weak_derivative_complex_test {O : Set (X n)} (hO : IsOpen O)
    {u g : X n → ℂ} {v : X n}
    (hu : LocallyL2On u O) (hg : LocallyL2On g O)
    (hWeak : ComplexWeakDerivativeOn O u g v)
    (ψ : CompactTest O) :
    (∫ x, u x * fderiv ℝ ψ x v ∂Yau.lebesgueC n) =
      -(∫ x, g x * ψ x ∂Yau.lebesgueC n) := by
  have hRe : ContDiff ℝ ∞ (fun x => (ψ x).re) := Complex.reCLM.contDiff.comp ψ.property.1
  have hIm : ContDiff ℝ ∞ (fun x => (ψ x).im) := Complex.imCLM.contDiff.comp ψ.property.1
  have hcRe : HasCompactSupport (fun x => (ψ x).re) :=
    ψ.property.2.1.comp_left (map_zero Complex.reCLM)
  have hcIm : HasCompactSupport (fun x => (ψ x).im) :=
    ψ.property.2.1.comp_left (map_zero Complex.imCLM)
  have hsRe : tsupport (fun x => (ψ x).re) ⊆ O :=
    (tsupport_comp_subset (map_zero Complex.reCLM) ψ).trans ψ.property.2.2
  have hsIm : tsupport (fun x => (ψ x).im) ⊆ O :=
    (tsupport_comp_subset (map_zero Complex.imCLM) ψ).trans ψ.property.2.2
  have hR := hWeak _ hRe hcRe hsRe
  have hI := hWeak _ hIm hcIm hsIm
  have intVal (f : X n → ℂ) (hf : LocallyL2On f O)
      (χ : X n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ O) :
      Integrable (fun x => f x * (χ x : ℂ)) (Yau.lebesgueC n) :=
    Yau.LeafProofs.L14Aux.locallyIntegrableOn_mul_compactTest f _
      (locallyIntegrableOn_of_locallyL2On hO hf)
      (Complex.ofRealCLM.continuous.comp hχ.continuous)
      (hcχ.comp_left Complex.ofReal_zero)
      ((tsupport_comp_subset Complex.ofReal_zero χ).trans hsχ)
  have intDeriv (χ : X n → ℝ) (hχ : ContDiff ℝ ∞ χ)
      (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ O) :
      Integrable (fun x => u x * (fderiv ℝ χ x v : ℂ)) (Yau.lebesgueC n) :=
    intVal u hu _ ((hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
      (hcχ.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hsχ)
  have hL : (fun x => u x * fderiv ℝ ψ x v) =
      fun x => u x * (fderiv ℝ (fun y => (ψ y).re) x v : ℂ) +
        Complex.I * (u x * (fderiv ℝ (fun y => (ψ y).im) x v : ℂ)) := by
    funext x
    rw [fderiv_re_apply (ψ.property.1.differentiable (by simp) x),
      fderiv_im_apply (ψ.property.1.differentiable (by simp) x)]
    have he := Complex.re_add_im (fderiv ℝ ψ x v)
    conv_lhs => rw [← he]
    ring
  have hRight : (fun x => g x * ψ x) =
      fun x => g x * ((ψ x).re : ℂ) + Complex.I * (g x * ((ψ x).im : ℂ)) := by
    funext x
    have he := Complex.re_add_im (ψ x)
    conv_lhs => rw [← he]
    ring
  rw [hL, hRight, integral_add (intDeriv _ hRe hcRe hsRe)
    ((intDeriv _ hIm hcIm hsIm).const_mul Complex.I),
    integral_add (intVal g hg _ hRe hcRe hsRe)
    ((intVal g hg _ hIm hcIm hsIm).const_mul Complex.I),
    integral_const_mul, integral_const_mul, hR, hI]
  ring

end Yau.LeafProofs.L21Aux
