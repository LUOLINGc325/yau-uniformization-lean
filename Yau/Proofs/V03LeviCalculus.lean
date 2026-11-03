import Yau.Proofs.V03Wirtinger
import Yau.Proofs.V03HolomorphicSmooth

/-! First-order rules for the original real Fréchet Wirtinger operators.
These rules keep the complex and real differentiability hypotheses explicit. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem wirt_holomorphic {f : E → ℂ} {z : E} (hf : DifferentiableAt ℂ f z) (v : E) :
    wirt f z v = fderiv ℂ f z v := by
  unfold wirt
  rw [hf.fderiv_restrictScalars (𝕜 := ℝ)]
  change (1 / 2 : ℂ) * (fderiv ℂ f z v - Complex.I * fderiv ℂ f z (Complex.I • v)) = _
  rw [map_smul, smul_eq_mul, ← mul_assoc, Complex.I_mul_I]
  ring

theorem wirtBar_holomorphic {f : E → ℂ} {z : E} (hf : DifferentiableAt ℂ f z) (v : E) :
    wirtBar f z v = 0 := by
  unfold wirtBar
  rw [hf.fderiv_restrictScalars (𝕜 := ℝ)]
  change (1 / 2 : ℂ) * (fderiv ℂ f z v + Complex.I * fderiv ℂ f z (Complex.I • v)) = 0
  rw [map_smul, smul_eq_mul, ← mul_assoc, Complex.I_mul_I]
  ring

theorem wirt_conj (f : E → ℂ) (z v : E) :
    wirt (fun y => star (f y)) z v = star (wirtBar f z v) := by
  unfold wirt wirtBar
  rw [fderiv_star]
  simp [star_mul, star_add, Complex.star_def]
  ring

theorem wirtBar_conj (f : E → ℂ) (z v : E) :
    wirtBar (fun y => star (f y)) z v = star (wirt f z v) := by
  unfold wirtBar wirt
  rw [fderiv_star]
  simp [star_mul, star_sub, Complex.star_def]
  ring

theorem wirt_mul {f g : E → ℂ} {z : E}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (v : E) :
    wirt (fun y => f y * g y) z v = wirt f z v * g z + f z * wirt g z v := by
  simp only [wirt, fderiv_fun_mul hf hg, ContinuousLinearMap.add_apply,
    smul_apply, smul_eq_mul]
  ring

theorem wirtBar_mul {f g : E → ℂ} {z : E}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (v : E) :
    wirtBar (fun y => f y * g y) z v = wirtBar f z v * g z + f z * wirtBar g z v := by
  simp only [wirtBar, fderiv_fun_mul hf hg, ContinuousLinearMap.add_apply,
    smul_apply, smul_eq_mul]
  ring

theorem wirt_sum {ι : Type*} (s : Finset ι) (f : ι → E → ℂ) (z v : E)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    wirt (fun y => ∑ i ∈ s, f i y) z v = ∑ i ∈ s, wirt (f i) z v := by
  simp only [wirt, fderiv_fun_sum hf, ContinuousLinearMap.sum_apply]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem wirtBar_sum {ι : Type*} (s : Finset ι) (f : ι → E → ℂ) (z v : E)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    wirtBar (fun y => ∑ i ∈ s, f i y) z v = ∑ i ∈ s, wirtBar (f i) z v := by
  simp only [wirtBar, fderiv_fun_sum hf, ContinuousLinearMap.sum_apply]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]

theorem fderiv_ofReal_apply {f : E → ℝ} {z : E}
    (hf : DifferentiableAt ℝ f z) (v : E) :
    fderiv ℝ (fun y => (f y : ℂ)) z v = (fderiv ℝ f z v : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt.comp z hf.hasFDerivAt).fderiv
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at h
  rw [h]
  rfl

theorem wirtBar_log_real {f : E → ℝ} {z : E}
    (hf : DifferentiableAt ℝ f z) (hne : f z ≠ 0) (v : E) :
    wirtBar (fun y => (Real.log (f y) : ℂ)) z v =
      (f z : ℂ)⁻¹ * wirtBar (fun y => (f y : ℂ)) z v := by
  simp only [wirtBar, fderiv_ofReal_apply (hf.log hne), fderiv_ofReal_apply hf,
    fderiv.log hf hne, smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem fderiv_inv_complex_apply {f : E → ℂ} {z : E}
    (hf : DifferentiableAt ℝ f z) (hne : f z ≠ 0) (v : E) :
    fderiv ℝ (fun y => (f y)⁻¹) z v = -(f z)⁻¹ * fderiv ℝ f z v * (f z)⁻¹ := by
  have h := ((hasFDerivAt_inv' (𝕜 := ℝ) hne).comp z hf.hasFDerivAt).fderiv
  simp only [Function.comp_def] at h
  rw [h]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, neg_mul]

theorem wirt_inv {f : E → ℂ} {z : E}
    (hf : DifferentiableAt ℝ f z) (hne : f z ≠ 0) (v : E) :
    wirt (fun y => (f y)⁻¹) z v = -(f z)⁻¹ ^ 2 * wirt f z v := by
  simp only [wirt, fderiv_inv_complex_apply hf hne]
  ring

end Yau.Blueprint.V03Proof
