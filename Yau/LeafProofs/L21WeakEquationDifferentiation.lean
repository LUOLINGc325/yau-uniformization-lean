import Yau.LeafProofs.L21WeakRowPairing

/-! The actual weak graph equation differentiates with exactly one
coefficient derivative and the already available first weak gradient. -/

open MeasureTheory Filter
open scoped ContDiff Topology
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem transposeRow_eq_rowTranspose
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (i : Fin n) {ψ : X n → ℝ}
    (hψ : Differentiable ℝ ψ) (x : X n) :
    transposeRow A i ψ x = rowTranspose Yau.realVec (dbarRealCoefficient A i)
      (fun y => (ψ y : ℂ)) x := by
  simp only [transposeRow, rowTranspose, rowApply, rowDivergence,
    fderiv_ofReal_apply (hψ _), Finset.sum_add_distrib, Finset.sum_mul]
  ring

def differentiatedDbarSource (A : X n → Matrix (Fin n) (Fin n) ℂ) (v : X n)
    (G : X n → Yau.RIdx n → ℂ) (F : X n → Fin n → ℂ) (x : X n) (i : Fin n) : ℂ :=
  F x i - ∑ a, fderiv ℝ (dbarRealCoefficient A i a) x v * G x a

theorem locallyL2On_differentiatedDbarSource {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O) (v : X n)
    (G : X n → Yau.RIdx n → ℂ) (F : X n → Fin n → ℂ)
    (hG : ∀ a, LocallyL2On (fun x => G x a) O)
    (hF : ∀ i, LocallyL2On (fun x => F x i) O) (i : Fin n) :
    LocallyL2On (fun x => differentiatedDbarSource A v G F x i) O := by
  have hterm (a : Yau.RIdx n) := locallyL2On_mul_smooth
    (contDiffOn_rowDirectional hO (dbarRealCoefficient A i)
      (fun a => dbarRealCoefficient_smoothOn hA i a) v a) (hG a)
  intro K hK hKO
  exact (hF i K hK hKO).sub
    (memLp_finsetSum Finset.univ (fun a _ => hterm a K hK hKO))

theorem dbar_weak_equation_directional {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (u g : X n → ℂ) (w F : X n → Fin n → ℂ) (G : X n → Yau.RIdx n → ℂ) (v : X n)
    (hu : LocallyL2On u O) (hg : LocallyL2On g O)
    (hG : ∀ a, LocallyL2On (fun x => G x a) O)
    (hF : ∀ i, LocallyL2On (fun x => F x i) O)
    (hWeak : ∀ a, ComplexWeakDerivativeOn O u (fun x => G x a) (Yau.realVec a))
    (hgv : ComplexWeakDerivativeOn O u g v)
    (hFv : ∀ i, ComplexWeakDerivativeOn O (fun x => w x i) (fun x => F x i) v)
    (heq : DbarWeakOn A u w O) :
    DbarWeakOn A g (differentiatedDbarSource A v G F) O := by
  intro i ψ hψ hcψ hsψ
  let p := dbarRealCoefficient A i
  have hp (a : Yau.RIdx n) : ContDiffOn ℝ ∞ (p a) O := dbarRealCoefficient_smoothOn hA i a
  have hp' (a : Yau.RIdx n) := contDiffOn_rowDirectional hO p hp v a
  let ψC : CompactTest O :=
    ⟨fun x => (ψ x : ℂ), Complex.ofRealCLM.contDiff.comp hψ,
      hcψ.comp_left Complex.ofReal_zero, (tsupport_comp_subset Complex.ofReal_zero ψ).trans hsψ⟩
  let ψD : CompactTest O :=
    ⟨fun x => (fderiv ℝ ψ x v : ℂ),
      Complex.ofRealCLM.contDiff.comp ((hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const),
      (hcψ.fderiv_apply ℝ v).comp_left Complex.ofReal_zero,
      (tsupport_comp_subset Complex.ofReal_zero _).trans ((tsupport_fderiv_apply_subset ℝ v).trans hsψ)⟩
  let θ := rowTransposeTest hO Yau.realVec p hp ψC
  let θ1 := rowTransposeTest hO Yau.realVec p hp ψD
  let θ2 := rowTransposeTest hO Yau.realVec (rowDirectional p v) hp' ψC
  have hdir : (fun y => fderiv ℝ ψC y v) = (ψD : X n → ℂ) := by
    funext y
    exact fderiv_ofReal_apply (hψ.differentiable (by simp) y) v
  have hdθ (x : X n) : fderiv ℝ θ x v = θ1 x + θ2 x := by
    by_cases hx : x ∈ O
    · change fderiv ℝ (rowTranspose Yau.realVec p ψC) x v = _
      rw [rowTranspose_directional hO Yau.realVec p hp ψC.property.1.contDiffOn hx v, hdir]
      rfl
    · have hnθ : x ∉ tsupport θ := fun hh => hx (θ.property.2.2 hh)
      have hn1 : x ∉ tsupport θ1 := fun hh => hx (θ1.property.2.2 hh)
      have hn2 : x ∉ tsupport θ2 := fun hh => hx (θ2.property.2.2 hh)
      simp only [fderiv_of_notMem_tsupport ℝ hnθ, _root_.zero_apply,
        image_eq_zero_of_notMem_tsupport hn1, image_eq_zero_of_notMem_tsupport hn2, add_zero]
  have hpair := complex_weak_derivative_complex_test hO hu hg hgv θ
  have hsplit : (fun x => u x * fderiv ℝ θ x v) = fun x => u x * θ1 x + u x * θ2 x := by
    funext x
    rw [hdθ, mul_add]
  rw [hsplit, integral_add (locallyL2On_test_integrable hO hu θ1)
    (locallyL2On_test_integrable hO hu θ2)] at hpair
  have hθ (x : X n) : θ x = transposeRow A i ψ x :=
    (transposeRow_eq_rowTranspose A i (hψ.differentiable (by simp)) x).symm
  have hθ1 (x : X n) : θ1 x = transposeRow A i (fun y => fderiv ℝ ψ y v) x :=
    (transposeRow_eq_rowTranspose A i
      (((hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)) x).symm
  have hfirst : (∫ x, u x * θ1 x ∂Yau.lebesgueC n) =
      -(∫ x, (ψ x : ℂ) * F x i ∂Yau.lebesgueC n) := by
    simp only [hθ1]
    rw [← heq i _ ((hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
      (hcψ.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hsψ)]
    simpa only [mul_comm] using hFv i ψ hψ hcψ hsψ
  have hsecond : (∫ x, u x * θ2 x ∂Yau.lebesgueC n) =
      ∫ x, (ψ x : ℂ) * (∑ a, fderiv ℝ (p a) x v * G x a) ∂Yau.lebesgueC n :=
    weak_gradient_row_transpose_pairing hO Yau.realVec (rowDirectional p v) hp'
      u G hu hG hWeak ψC
  rw [hfirst, hsecond] at hpair
  simp only [hθ] at hpair
  have hIntF : Integrable (fun x => (ψ x : ℂ) * F x i) (Yau.lebesgueC n) := by
    simpa only [mul_comm] using locallyL2On_test_integrable hO (hF i) ψC
  have hS : LocallyL2On (fun x => ∑ a, fderiv ℝ (p a) x v * G x a) O := by
    intro K hK hKO
    exact memLp_finsetSum Finset.univ (fun a _ =>
      locallyL2On_mul_smooth (hp' a) (hG a) K hK hKO)
  have hIntS : Integrable (fun x => (ψ x : ℂ) * (∑ a, fderiv ℝ (p a) x v * G x a))
      (Yau.lebesgueC n) := by
    simpa only [mul_comm] using locallyL2On_test_integrable hO hS ψC
  change (∫ x, (ψ x : ℂ) * (F x i - ∑ a, fderiv ℝ (p a) x v * G x a)
    ∂Yau.lebesgueC n) = _
  simp only [mul_sub]
  rw [integral_sub hIntF hIntS]
  linear_combination -hpair

end Yau.LeafProofs.L21Aux
