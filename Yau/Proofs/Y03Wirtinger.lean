import Yau.Blueprint.Alignment

/-! Native first-order chain rules for the exact Wirtinger operators in the contracts. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem wirt_comp_holomorphic {f : W → ℂ} {γ : V → W} {z v : V}
    (hf : DifferentiableAt ℝ f (γ z)) (hγ : DifferentiableAt ℂ γ z) :
    wirt (f ∘ γ) z v = wirt f (γ z) (fderiv ℂ γ z v) := by
  unfold wirt
  rw [fderiv_comp z hf (hγ.restrictScalars ℝ), hγ.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    map_smul]

theorem wirtBar_comp_holomorphic {f : W → ℂ} {γ : V → W} {z v : V}
    (hf : DifferentiableAt ℝ f (γ z)) (hγ : DifferentiableAt ℂ γ z) :
    wirtBar (f ∘ γ) z v = wirtBar f (γ z) (fderiv ℂ γ z v) := by
  unfold wirtBar
  rw [fderiv_comp z hf (hγ.restrictScalars ℝ), hγ.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    map_smul]

theorem wirt_add_dir (f : V → ℂ) (z v w : V) :
    wirt f z (v + w) = wirt f z v + wirt f z w := by
  simp only [wirt, smul_add, map_add]
  ring

theorem wirtBar_add_dir (f : V → ℂ) (z v w : V) :
    wirtBar f z (v + w) = wirtBar f z v + wirtBar f z w := by
  simp only [wirtBar, smul_add, map_add]
  ring

theorem wirt_I_dir (f : V → ℂ) (z v : V) :
    wirt f z (Complex.I • v) = Complex.I * wirt f z v := by
  simp only [wirt, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
  ring_nf
  simp
  ring

theorem wirtBar_I_dir (f : V → ℂ) (z v : V) :
    wirtBar f z (Complex.I • v) = -Complex.I * wirtBar f z v := by
  simp only [wirtBar, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
  ring_nf
  simp
  ring

theorem wirt_real_smul_dir (f : V → ℂ) (z v : V) (r : ℝ) :
    wirt f z (r • v) = (r : ℂ) * wirt f z v := by
  simp only [wirt, smul_comm Complex.I r, map_smul, Complex.real_smul]
  ring

theorem wirtBar_real_smul_dir (f : V → ℂ) (z v : V) (r : ℝ) :
    wirtBar f z (r • v) = (r : ℂ) * wirtBar f z v := by
  simp only [wirtBar, smul_comm Complex.I r, map_smul, Complex.real_smul]
  ring

theorem wirt_of_differentiableAt_complex {f : V → ℂ} {z : V}
    (hf : DifferentiableAt ℂ f z) (v : V) : wirt f z v = fderiv ℂ f z v := by
  unfold wirt
  rw [hf.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  ring_nf
  simp
  ring

theorem wirtBar_of_differentiableAt_complex {f : V → ℂ} {z : V}
    (hf : DifferentiableAt ℂ f z) (v : V) : wirtBar f z v = 0 := by
  unfold wirtBar
  rw [hf.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  ring_nf
  simp

end Yau.Blueprint.Alignment.Y03Proof
