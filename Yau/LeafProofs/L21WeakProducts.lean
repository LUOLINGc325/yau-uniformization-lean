import Yau.LeafProofs.L21WeakCalculus

/-! Multiplication by smooth complex coefficients preserves actual local
L² weak derivatives, including coefficients smooth only on the chart. -/

open MeasureTheory Filter
open scoped ContDiff Topology
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem locallyL2On_mul_smooth {O : Set (X n)} {a u : X n → ℂ}
    (ha : ContDiffOn ℝ ∞ a O) (hu : LocallyL2On u O) :
    LocallyL2On (fun x => a x * u x) O := by
  intro K hK hKO
  exact Yau.LeafProofs.L14Aux.memLp_continuousOn_mul_compact K hK a u
    (ha.continuousOn.mono hKO) (hu K hK hKO)

theorem locallyL2On_add {O : Set (X n)} {u g : X n → ℂ}
    (hu : LocallyL2On u O) (hg : LocallyL2On g O) :
    LocallyL2On (fun x => u x + g x) O := fun K hK hKO => (hu K hK hKO).add (hg K hK hKO)

def multiplyLocalTest {O : Set (X n)} (hO : IsOpen O) {a : X n → ℂ}
    (ha : ContDiffOn ℝ ∞ a O) (ψ : CompactTest O) : CompactTest O :=
  ⟨fun x => a x * ψ x,
    contDiff_of_contDiffOn_tsupport_subset hO (ha.mul ψ.property.1.contDiffOn)
      tsupport_mul_subset_right ψ.property.2.2,
    ψ.property.2.1.mul_left, tsupport_mul_subset_right.trans ψ.property.2.2⟩

theorem locallyL2On_test_integrable {O : Set (X n)} (hO : IsOpen O)
    {u : X n → ℂ} (hu : LocallyL2On u O) (ψ : CompactTest O) :
    Integrable (fun x => u x * ψ x) (Yau.lebesgueC n) :=
  Yau.LeafProofs.L14Aux.locallyIntegrableOn_mul_compactTest u ψ
    (locallyIntegrableOn_of_locallyL2On hO hu) ψ.property.1.continuous
    ψ.property.2.1 ψ.property.2.2

theorem complexWeakDerivativeOn_smooth_mul {O : Set (X n)} (hO : IsOpen O)
    {a u g : X n → ℂ} {v : X n}
    (ha : ContDiffOn ℝ ∞ a O) (hu : LocallyL2On u O) (hg : LocallyL2On g O)
    (hWeak : ComplexWeakDerivativeOn O u g v) :
    LocallyL2On (fun x => a x * u x) O ∧
      LocallyL2On (fun x => a x * g x + fderiv ℝ a x v * u x) O ∧
      ComplexWeakDerivativeOn O (fun x => a x * u x)
        (fun x => a x * g x + fderiv ℝ a x v * u x) v := by
  have hDa : ContDiffOn ℝ ∞ (fun x => fderiv ℝ a x v) O :=
    (ha.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have hau := locallyL2On_mul_smooth ha hu
  have hag := locallyL2On_mul_smooth ha hg
  have hDau := locallyL2On_mul_smooth hDa hu
  refine ⟨hau, locallyL2On_add hag hDau, ?_⟩
  intro ψ hψ hcψ hsψ
  let ψC : CompactTest O :=
    ⟨fun x => (ψ x : ℂ), Complex.ofRealCLM.contDiff.comp hψ,
      hcψ.comp_left Complex.ofReal_zero, (tsupport_comp_subset Complex.ofReal_zero ψ).trans hsψ⟩
  let ψD : CompactTest O :=
    ⟨fun x => (fderiv ℝ ψ x v : ℂ),
      Complex.ofRealCLM.contDiff.comp ((hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const),
      (hcψ.fderiv_apply ℝ v).comp_left Complex.ofReal_zero,
      (tsupport_comp_subset Complex.ofReal_zero _).trans ((tsupport_fderiv_apply_subset ℝ v).trans hsψ)⟩
  let θ := multiplyLocalTest hO ha ψC
  have hX : Integrable (fun x => (a x * u x) * (fderiv ℝ ψ x v : ℂ)) (Yau.lebesgueC n) :=
    locallyL2On_test_integrable hO hau ψD
  have hY : Integrable (fun x => (fderiv ℝ a x v * u x) * (ψ x : ℂ)) (Yau.lebesgueC n) :=
    locallyL2On_test_integrable hO hDau ψC
  have hZ : Integrable (fun x => (a x * g x) * (ψ x : ℂ)) (Yau.lebesgueC n) :=
    locallyL2On_test_integrable hO hag ψC
  have hD (x : X n) : fderiv ℝ θ x v =
      a x * (fderiv ℝ ψ x v : ℂ) + (ψ x : ℂ) * fderiv ℝ a x v := by
    by_cases hx : x ∈ O
    · change fderiv ℝ (fun y => a y * (ψ y : ℂ)) x v = _
      rw [fderiv_fun_mul (c := a) (d := fun y => (ψ y : ℂ))
        ((ha.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
        (ψC.property.1.differentiable (by simp) x)]
      simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
        fderiv_ofReal_apply (hψ.differentiable (by simp) x)]
    · have hnp : x ∉ tsupport ψ := fun hh => hx (hsψ hh)
      have hnθ : x ∉ tsupport θ := fun hh => hx (θ.property.2.2 hh)
      simp only [fderiv_of_notMem_tsupport ℝ hnθ, _root_.zero_apply,
        fderiv_of_notMem_tsupport ℝ hnp, image_eq_zero_of_notMem_tsupport hnp,
        Complex.ofReal_zero, mul_zero, zero_mul, add_zero]
  have h := complex_weak_derivative_complex_test hO hu hg hWeak θ
  have hL : (fun x => u x * fderiv ℝ θ x v) =
      fun x => (a x * u x) * (fderiv ℝ ψ x v : ℂ) +
        (fderiv ℝ a x v * u x) * (ψ x : ℂ) := by
    funext x
    rw [hD]
    ring
  have hR : (fun x => g x * θ x) = fun x => (a x * g x) * (ψ x : ℂ) := by
    funext x
    change g x * (a x * (ψ x : ℂ)) = _
    ring
  rw [hL, hR, integral_add hX hY] at h
  have hGoal : (fun x => (a x * g x + fderiv ℝ a x v * u x) * (ψ x : ℂ)) =
      fun x => (a x * g x) * (ψ x : ℂ) + (fderiv ℝ a x v * u x) * (ψ x : ℂ) := by
    funext x
    ring
  rw [hGoal, integral_add hZ hY]
  linear_combination h

end Yau.LeafProofs.L21Aux
