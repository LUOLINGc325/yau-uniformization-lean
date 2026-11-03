import Yau.LeafProofs.L21TransposeDifferentiation

/-! A row applied to a weak gradient is identified by actual compact
transpose pairings. No derivative of the rough input is evaluated. -/

open MeasureTheory Filter
open scoped ContDiff Topology
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ} {ι : Type*} [Fintype ι]

def directionalTest {O : Set (X n)} (ψ : CompactTest O) (v : X n) : CompactTest O :=
  ⟨fun x => fderiv ℝ ψ x v, contDiff_directional ψ.property.1 v,
    ψ.property.2.1.fderiv_apply ℝ v, (tsupport_fderiv_apply_subset ℝ v).trans ψ.property.2.2⟩

theorem fderiv_multiplyLocalTest {O : Set (X n)} (hO : IsOpen O)
    {a : X n → ℂ} (ha : ContDiffOn ℝ ∞ a O) (ψ : CompactTest O) (x v : X n) :
    fderiv ℝ (multiplyLocalTest hO ha ψ) x v =
      a x * fderiv ℝ ψ x v + ψ x * fderiv ℝ a x v := by
  by_cases hx : x ∈ O
  · change fderiv ℝ (fun y => a y * ψ y) x v = _
    rw [fderiv_fun_mul (c := a) (d := ψ)
      ((ha.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
      (ψ.property.1.differentiable (by simp) x)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  · have hn : x ∉ tsupport ψ := fun hh => hx (ψ.property.2.2 hh)
    have hnp : x ∉ tsupport (multiplyLocalTest hO ha ψ) := fun hh =>
      hx ((multiplyLocalTest hO ha ψ).property.2.2 hh)
    simp only [fderiv_of_notMem_tsupport ℝ hnp, fderiv_of_notMem_tsupport ℝ hn,
      _root_.zero_apply, image_eq_zero_of_notMem_tsupport hn, mul_zero, zero_mul, add_zero]

theorem rowTranspose_eq_neg_sum_derivative {O : Set (X n)} (hO : IsOpen O)
    (v : ι → X n) (p : ι → X n → ℂ) (hp : ∀ a, ContDiffOn ℝ ∞ (p a) O)
    (ψ : CompactTest O) (x : X n) :
    rowTranspose v p ψ x =
      -(∑ a, fderiv ℝ (multiplyLocalTest hO (hp a) ψ) x (v a)) := by
  simp only [rowTranspose, rowApply, rowDivergence, fderiv_multiplyLocalTest,
    Finset.sum_add_distrib, Finset.sum_mul]
  have he : (∑ a, ψ x * fderiv ℝ (p a) x (v a)) =
      ∑ a, fderiv ℝ (p a) x (v a) * ψ x := by
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he]
  ring

theorem weak_gradient_row_transpose_pairing {O : Set (X n)} (hO : IsOpen O)
    (v : ι → X n) (p : ι → X n → ℂ) (hp : ∀ a, ContDiffOn ℝ ∞ (p a) O)
    (u : X n → ℂ) (G : X n → ι → ℂ)
    (hu : LocallyL2On u O) (hG : ∀ a, LocallyL2On (fun x => G x a) O)
    (hWeak : ∀ a, ComplexWeakDerivativeOn O u (fun x => G x a) (v a)) (ψ : CompactTest O) :
    (∫ x, u x * rowTranspose v p ψ x ∂Yau.lebesgueC n) =
      ∫ x, ψ x * (∑ a, p a x * G x a) ∂Yau.lebesgueC n := by
  have hInt (a : ι) : Integrable
      (fun x => u x * fderiv ℝ (multiplyLocalTest hO (hp a) ψ) x (v a)) (Yau.lebesgueC n) :=
    locallyL2On_test_integrable hO hu (directionalTest (multiplyLocalTest hO (hp a) ψ) (v a))
  have hIntG (a : ι) : Integrable (fun x => G x a * multiplyLocalTest hO (hp a) ψ x)
      (Yau.lebesgueC n) :=
    locallyL2On_test_integrable hO (hG a) (multiplyLocalTest hO (hp a) ψ)
  calc
    _ = -(∑ a, ∫ x, u x * fderiv ℝ (multiplyLocalTest hO (hp a) ψ) x (v a)
        ∂Yau.lebesgueC n) := by
      simp only [rowTranspose_eq_neg_sum_derivative hO v p hp ψ, mul_neg, Finset.mul_sum]
      rw [integral_neg, integral_finsetSum _ (fun a _ => hInt a)]
    _ = ∑ a, ∫ x, G x a * multiplyLocalTest hO (hp a) ψ x ∂Yau.lebesgueC n := by
      simp only [complex_weak_derivative_complex_test hO hu (hG _) (hWeak _),
        Finset.sum_neg_distrib, neg_neg]
    _ = ∫ x, ∑ a, G x a * multiplyLocalTest hO (hp a) ψ x ∂Yau.lebesgueC n :=
      (integral_finsetSum _ (fun a _ => hIntG a)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      change G x a * (p a x * ψ x) = _
      ring

end Yau.LeafProofs.L21Aux
