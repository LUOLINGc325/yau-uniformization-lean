import Yau.Proofs.P04LeviLogChain
import Yau.LeafProofs.L19LocalizationMaximum
import Yau.LeafProofs.L17RicciNaturality

/-! Local scalar composition and the Levi sign at an actual local minimum. -/
noncomputable section
open Filter
open scoped Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.P08Aux
open Yau Yau.LeafProofs Yau.Proofs.P04Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

/-- The exact real scalar chain rule for the actual Wirtinger Levi matrix. -/
theorem leviC_scalar_comp {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) {F : ℝ → ℝ} (hF : ContDiffAt ℝ 2 F (f z)) :
    leviC (fun y => F (f y)) z = ((deriv F (f z) : ℝ) : ℂ) • leviC f z +
      ((deriv (deriv F) (f z) : ℝ) : ℂ) • gradientGram f z := by
  have hcomp : ContDiffAt ℝ 2 (fun y => F (f y)) z := hF.comp z hf
  have hd := hf.differentiableAt (by norm_num)
  have hess (v w : ComplexVector n) :
      fderiv ℝ (fderiv ℝ (fun y => F (f y))) z v w =
        deriv (deriv F) (f z) * fderiv ℝ f z v * fderiv ℝ f z w +
          deriv F (f z) * fderiv ℝ (fderiv ℝ f) z v w := by
    change fderiv ℝ (fderiv ℝ (F ∘ f)) z v w = _
    rw [L18Aux.secondFDeriv_comp hf hF,L18Aux.secondFDeriv_scalar_apply hF,
      fderiv_eq_deriv_mul]
    ring
  ext i j
  have hL := L18Aux.leviMatrix_entry_re_im hcomp stdVec i j
  have hq := L18Aux.leviMatrix_entry_re_im hf stdVec i j
  apply Complex.ext
  · simp only [leviC, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hL.1, hq.1]
    simp only [gradientGram, wirt_ofReal_formula hd, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      hess]
    ring
  · simp only [leviC, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, hL.2, hq.2]
    simp only [gradientGram, wirt_ofReal_formula hd, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      hess]
    ring

/-- A local minimum has nonnegative real second directional derivatives. -/
theorem secondFDeriv_nonneg_at_local_min {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hm : IsLocalMin f z) (v : ComplexVector n) :
    0 ≤ fderiv ℝ (fderiv ℝ f) z v v := by
  have hmax : IsLocalMax (fun y => (-1 : ℝ) * f y) z := by
    simpa only [neg_one_mul] using hm.neg
  have h := L19Aux.secondFDeriv_nonpos_at_local_max (contDiffAt_const.mul hf) hmax v
  rw [L22Aux.secondFDeriv_const_mul hf (-1)] at h
  linarith

/-- At a zero of a nonnegative smooth function, its regularized logarithm
is tested by this ordinary local minimum theorem. -/
theorem leviC_posSemidef_at_local_min {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hm : IsLocalMin f z) : (leviC f z).PosSemidef := by
  apply (L22Aux.leviC_posSemidef_iff hf).mpr
  intro v
  unfold L22Aux.complexLeviQuadratic
  exact div_nonneg (add_nonneg (secondFDeriv_nonneg_at_local_min hf hm v)
    (secondFDeriv_nonneg_at_local_min hf hm (Complex.I • v))) (by norm_num)

end Yau.NodeProofs.P08Aux
