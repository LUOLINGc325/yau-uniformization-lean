import Yau.Geometry.Basic

noncomputable section

namespace Yau.Proofs.C07ChartChordAux

open Yau

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem hermitian_re_from_norm (h : HermitianInnerProduct V) (u v : V) :
    (h.toFun u v).re =
      (hermitianNormSq h (u + v) - hermitianNormSq h u - hermitianNormSq h v) / 2 := by
  have hc : (h.toFun v u).re = (h.toFun u v).re := by
    simpa using congrArg Complex.re (h.conjugate_symmetric v u)
  simp only [hermitianNormSq, h.map_add_left, h.map_add_right, Complex.add_re]
  linarith

theorem hermitian_im_from_norm (h : HermitianInnerProduct V) (u v : V) :
    (h.toFun u v).im =
      (hermitianNormSq h u + hermitianNormSq h v - hermitianNormSq h (u + Complex.I • v)) / 2 := by
  have hc : (h.toFun v u).im = -(h.toFun u v).im := by
    simpa using congrArg Complex.im (h.conjugate_symmetric v u)
  simp [hermitianNormSq, h.map_add_left, h.map_add_right, h.map_smul_left,
    h.map_smul_right, Complex.mul_re, Complex.mul_im, hc] <;> ring

theorem hermitianNormSq_real_smul (h : HermitianInnerProduct V) (t : ℝ) (v : V) :
    hermitianNormSq h ((t : ℂ) • v) = t ^ 2 * hermitianNormSq h v := by
  simp only [hermitianNormSq, h.map_smul_left, h.map_smul_right, Complex.star_def,
    Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero]
  ring

end Yau.Proofs.C07ChartChordAux
