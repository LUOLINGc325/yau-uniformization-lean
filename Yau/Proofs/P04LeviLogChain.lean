import Yau.Proofs.P04LogHessian

noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs

/-- The actual holomorphic differential of a real function. -/
theorem wirt_ofReal_formula {n : ℕ} {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : DifferentiableAt ℝ f z) (v : ComplexVector n) :
    wirt (fun y => (f y : ℂ)) z v =
      ((1/2 : ℝ)*fderiv ℝ f z v : ℂ) -
        Complex.I*((1/2 : ℝ)*fderiv ℝ f z (Complex.I • v) : ℂ) := by
  rw [wirt,fderiv_ofReal_apply hf,fderiv_ofReal_apply hf]
  push_cast
  ring

def gradientGram {n : ℕ} (f : ComplexVector n → ℝ) (z : ComplexVector n) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => star (wirt (fun y => (f y : ℂ)) z (stdVec i)) *
    wirt (fun y => (f y : ℂ)) z (stdVec j)

theorem gradientGram_posSemidef {n : ℕ} (f : ComplexVector n → ℝ) (z : ComplexVector n) :
    (gradientGram f z).PosSemidef := by
  let B : Matrix (Fin 1) (Fin n) ℂ := fun _ j => wirt (fun y => (f y : ℂ)) z (stdVec j)
  have H := Matrix.posSemidef_conjTranspose_mul_self B
  convert H using 1
  ext i j
  change star (wirt (fun y => (f y : ℂ)) z (stdVec i)) *
    wirt (fun y => (f y : ℂ)) z (stdVec j) = ∑ k : Fin 1, star (B k i)*B k j
  simp [B]

/-- The exact matrix logarithm chain rule for the original nested Wirtinger
calculator, with no positivity assertion about finite zero partial sums. -/
theorem leviC_log {n : ℕ} {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hpos : 0 < f z) :
    leviC (fun y => Real.log (f y)) z =
      (((f z)⁻¹ : ℝ) : ℂ) • leviC f z -
        ((((f z)^2)⁻¹ : ℝ) : ℂ) • gradientGram f z := by
  have hlog : ContDiffAt ℝ 2 (fun y => Real.log (f y)) z :=
    (Real.contDiffAt_log.mpr hpos.ne').comp z hf
  have hd := hf.differentiableAt (by norm_num)
  ext i j
  have hL := L18Aux.leviMatrix_entry_re_im hlog stdVec i j
  have hF := L18Aux.leviMatrix_entry_re_im hf stdVec i j
  apply Complex.ext
  · simp only [leviC,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Complex.sub_re,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hL.1,hF.1]
    simp only [gradientGram,wirt_ofReal_formula hd,Complex.star_def,Complex.conj_re,
      Complex.conj_im,Complex.mul_re,Complex.mul_im,
      Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
      Complex.I_im,Complex.neg_re,Complex.neg_im]
    simp only [secondFDeriv_log hf hpos]
    ring
  · simp only [leviC,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Complex.sub_im,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,hL.2,hF.2]
    simp only [gradientGram,wirt_ofReal_formula hd,Complex.star_def,Complex.conj_re,
      Complex.conj_im,Complex.mul_re,Complex.mul_im,
      Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
      Complex.I_im,Complex.neg_re,Complex.neg_im]
    simp only [secondFDeriv_log hf hpos]
    ring

end Yau.Proofs.P04Aux
